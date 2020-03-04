---
title: "Abstract definitional interpreters in Haskell: a Final Tagless exercise"
---

This post is based on the _Abstract Definitional Interpreters_ paper [[1]](#references). The paper
shows how an interpreter for some target language embedded in a meta-language can be turned into an
_abstract_ interpreter, which is able to give certain over- and underapproximations of target
program behaviors. This interpreter is shown to be total and terminating. We will refer to
[[1]](#references) as "the ADI paper" from now on.

The ADI paper represents the target language's AST as a data type in the meta language
(specifically, Racket). The interpreter is defined as a fold over this AST. This approach to
language embedding is called _initial_ by some authors.

Authors then claim that Racket's module system allows separating the core interpreter and concrete
details of its various flavors --- for example, the same core is used to implement an evaluator and
an approximating interpreter.

In this post, we will try to reimplement the ADI paper in Haskell.

When one thinks about embedding a language in Haskell with a possibility of having several
interpretations for the same expressions, one of the first things that comes to mind is the _final
tagless_ approach popularized by Oleg Kiselyov [[2]](#references). We will try to apply it to the
abstract interpretation and evaluate the properties of this approach.

Overview of the paper and this post
-----------------------------------

The trick of the abstract interpretation, employed in the ADI paper and introduced in
[[3]](#references), amounts to these steps:

1. Define an interpreter for the target language as a recursive function over AST
2. Make the set of all possible runtime values finite by introducing _abstract values_
3. Use indirection via a _store_ for all variable accesses
4. Make the address space finite by allowing the same address to refer to multiple possible values.

This transformation (steps 2-4) makes an interpreter total and finite, but, of course, limits its
power to just approximating the target program's behavior.

The ADI paper defines a simple interpreter for an AST and then applies these steps.  We will follow
only some of them, demonstrating that they are possible to be implemented in a typed language like
Haskell as successfully as in untyped Racket.

Namely, we will:

1. Define an interpreter that depends on a set of monadic effects (section 3 of the ADI paper)
2. Run it on some examples from section 3 to show that it works
3. Show that it can be turned into a nondeterministic interpreter with abstract values (section 3.2)
4. Run the new interpreter on the same examples and observe that it behaves as the one in the paper
5. And finally, demonstrate that Final Tagless approach leads to easy extension of our language,
   something that is not possible in the original implementation

A technical note
----------------

[This](https://github.com/maksbotan/maksbotan.github.io/tree/develop/posts/2019-09-04-abstract-definitional-interpreters.lhs)
is a literal Haskell file. Here's how to load in GHCi (adapt for other build tools if not using
stack):

```console
$ stack ghci 2019-09-04-abstract-definitional-interpreters.lhs \
    --package markdown-unlit \
    --package containers \
    --package mtl \
    --package transformers \
    --ghci-options='-pgmL markdown-unlit'
```

We will use Haskell 98, that is Haskell + 98 extensions, as Csongor Kiss joked in his ICFP 2019
talk. Let us enable these extensions now.

<details class="code-details">
<summary>Necessary extensions</summary>

```haskell
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module ADI where

import Control.Applicative
import Control.Monad.Fail (MonadFail)
import Control.Monad.Identity
import Control.Monad.List
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Data.Kind (Type)
import qualified Data.Map.Strict as M
```
</details>

The target language and its embedding
-------------------------------------

The language of [[1]](#references) is a simple one --- simply typed lambda calculus with one base
type (integers) and recursion via explicit `let rec` binder. We will not copy-paste its definition
here and proceed straight to embedding.

Let us represent arithmetic operations available in the target language using a datatype:

```haskell
data Op = Plus | Minus | Times | Divide deriving (Eq, Show)
```

First of all, we are going to use Typed Final Tagless encoding, to offload typechecking of the target
language to GHC and also to ensure the totality of all interpreters. To do that, we will define a
type class `Lang` over some representation type `repr :: Type -> Type`, which will be our embedding:

```haskell
class Lang repr where
  num :: Int -> repr Int
  if0 :: repr Int -> repr a -> repr a -> repr a
  op :: Op -> repr Int -> repr Int -> repr Int

  var :: String -> repr a
  lam :: String -> repr b -> repr (a -> b)
  app :: repr (a -> b) -> repr a -> repr b
```

<details class="code-details">
<summary>A note on type safety</summary>
There is, of course, a way to subvert the type-system by using the `var` combinator with an
arbitrary type. This may be amended by pushing variable bindings to the type level, but this is not
essential for this presentation.
</details>

Note that we are using explicit variable names in lambda-abstractions. If we were to follow
Kiselyov's work to the letter, we would need to represent the target language's lambdas as Haskell
functions:

```{.haskell .ignore}
lam :: (repr a -> repr b) -> repr (a -> b)
```

While this may be made to work in our case with some effort, it does not match the ADI paper and
does not really fit our task. Reasons for this will be given in the next section.

Now that we have an embedding of our language, we can write some terms in it. We will use some
examples from the paper and a couple more.

This term is supposed to evaluate to 63:

```haskell
t63 :: Lang repr => repr Int
t63 = op Times (op Plus (num 3) (num 4)) (num 9)
```

This term is supposed to fail due to division by zero:

```haskell
tDivZero :: Lang repr => repr Int
tDivZero = op Divide (num 5) (op Minus (num 3) (num 3))
```

And these terms show that functions also work:

```haskell
tPlusTwo :: Lang repr => repr (Int -> Int)
tPlusTwo = lam "x" (op Plus (var "x") (num 2))

t42 :: Lang repr => repr Int
t42 = op Times (num 21) (num 2)
```

Higher-order functions are representable and type-checked by GHC as well:

```haskell
tId :: Lang repr => repr (a -> a)
tId = lam "x" (var "x")

tTwice :: Lang repr => repr ((a -> a) -> a -> a)
tTwice = lam "f" (lam "v" (app (var "f") (app (var "f") (var "v"))))

tHO :: Lang repr => repr Int
tHO = app (app tTwice tPlusTwo) (num 42)
```

We omit recursive functions from our language for the sake of simplicity.

Since we are using typed embedding, it is trivial to extend it with booleans and, for
example, give a more precise type for `if0`.

Runtime representation
----------------------

Remember that making an _abstract interpreter_ requires a store for values and closures. We choose
to represent the mapping of variable names to their (integer) addresses in the store as
`Data.Map.Strict.Map`:

```haskell
type VarEnv = M.Map String Int
```

The store will also be represented as a map from addresses to values. And at this point, we must
decide on runtime representation of our values.

When defining instances of his final tagless type classes, Kiselyov uses a newtype like this

```{.haskell .ignore}
newtype R a = R { unR :: a } deriving (Show, Eq)
```

emphasizing that it is not a tag. 

This newtype is used to store both values and closures of the target language, which are simple
Haskell functions in his case. This plays well with `repr (a -> b)` encoding of lambdas, since this
is instantiated with `R (a -> b)`, which is just an ordinary Haskell function.

However, we can't do it this way in our case, since in order to achieve the goal of the ADI paper,
the implementation of the interpreter has to be monadic.  This means that runtime representation of
`repr (Int -> Int)` can't be a Haskell function of type `Int -> Int`, but rather something like `Int
-> m Int`.

To overcome this, we will introduce a type `Repr` with different constructors for different types of
runtime values. This essentially drops the word "tagless" from our Final Tagless encoding. Doesn't
this defeat the whole point of doing everything in FT style?

It follows from [[2]](#references) that the sole purpose of doing everything in tagless style is to
avoid runtime errors in the interpreter due to pattern matching on tags. The same effect may be
achieved with GADTs, which have been available for a long time by now.

With `GADTs`, we could define our representation type `Repr` as follows:
```{.haskell .ignore}
data Repr a where
  RNum :: Int -> Repr Int -- for integers
  RAbs :: ... -> Repr (a -> b) -- for closures
```

Alas, this is not possible in our case. Our store, represented as a `Map`, is _monomorphic_ in its
value type, meaning that we would have to put `Repr a` in some kind of existential wrapper like
[`Data.Dynamic`](http://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Dynamic.html#t:Dynamic),
canceling the whole profit of having a `GADT`. Moreover, when applying abstract interpretation
trick, we have to make the store finite, meaning that some cells will be occupied by more than one
value which may have different types, again calling for existentials.

So instead we make our `Repr` an ordinary ADT:

```haskell
data Repr (m :: Type -> Type) where
  RNum :: Int -> Repr m
  RAbs :: VarEnv -> String -> m (Repr m) -> Repr m
```

<details class="code-details">
<summary>Show instance</summary>

```haskell
instance Show (Repr m) where
  showsPrec p (RNum n)
     = showParen
         (p >= 11)
         (showString "RNum " . showsPrec 11 n)
  showsPrec p (RAbs _e x _v)
     = showParen
         (p >= 11)
         (showString "RAbs " . showsPrec 11 x)
```
</details>

This datatype is parameterized over arbitrary monad `m` in which the interpreter runs.

Here, `RNum` constructor encodes integers of the target language and `RAbs` encodes its closures.
`RAbs` has to store the variables captured by the closure, name of the lambda-bound variable it
expects and a monadic action that evaluates it.

Having defined this `Repr` type, we are able to define the type of the store, parameterized over the
representation:

```haskell
type ValStore (m :: Type -> Type) (r :: (Type -> Type) -> Type) = M.Map Int (r m)
```

Representing the interpreter
----------------------------

The next step is to write an interpreter. Now, we will argue that our task is not in embedding a
single language in Haskell, but rather embedding _two_ languages.  The first one is the
lambda-calculus we have already dealt with, and the second one is the language of abstract
interpreters. It has the following operations:

* `findAddr` to get "memory address" of variable from the current environment
* `readAddr` to get a value or closure from memory by its address
* `alloc` to create a new cell in the store and return its address
* `store` to write a new value to an address in memory
* `withEnv` to run some action with a variable bound to some address

Both languages are completely independent of each other and may be expressed in different styles. We
chose Final Tag(less) for the first one, let's do the same with the second.

Since our language involves mutable state through `store` combinator, we will have to use some Monad
in Haskell. We will define this monad in the so-called "mtl style", using a type class to abstract
over all possible implementations.

We will use `MonadReader` to represent binding of variables to their addresses and `MonadState` to
represent the store. We also need `MonadFail` to represent the possibility of failure in the target
language, to be able to detect divisions by zero.

**The Interpreter Monad**

As we are going to define interpretation monad in "mtl" style, we need a type class:

```haskell
class MonadInterpreter (m :: Type -> Type) (r :: (Type -> Type) -> Type) | m -> r where
  getEnv :: m VarEnv
  findAddr :: String -> m Int
  readAddr :: Int -> m (r m)
  alloc :: String -> m Int
  store :: Int -> r m -> m ()
  withEnv :: VarEnv -> m a -> m a
```

Instances of this class will use `VarEnv` and `ValStore` class to interact with the store. We can
use `MonadReader` and `MonadState` classes for that and give a general instance for our type class:

```haskell
instance (Monad m, MonadReader VarEnv m, MonadState (ValStore m r) m) => MonadInterpreter m r where
  getEnv = ask
  findAddr x = (M.! x) <$> ask
  readAddr a = (M.! a) <$> get
  alloc _ = M.size <$> get
  store x v = modify $ M.insert x v
  withEnv e = local (const $ e)
```

**The actual interpreter** 

Finally, we are ready to make an instance of the `Lang` type class. For that, we need some type
`repr` that will be able to unify with `Lang`'s member types. We can't use some `Monad m => m a` for
that because we want to use our `Repr` runtime tags. Let's introduce a special wrapper:

```haskell
newtype WithRepr m r a = WithRepr { getInterp :: m (r m) }
```

Here `a` type variable is a phantom one, meaning that it will unify with type-checked `repr` from
the typeclass, but there will be no type information in the runtime values.

Instance for `Lang` is pretty straightforward:

```haskell
instance (MonadInterpreter m Repr, MonadFail m) => Lang (WithRepr m Repr) where
  var x = WithRepr $ findAddr x >>= readAddr
    
  num x = WithRepr $ return $ RNum x

  if0 (WithRepr x) (WithRepr a) (WithRepr b) = WithRepr $ do
    RNum x' <- x
    -- Here a pattern match failure is possible, which is hidden by `MonadFail` instance.
    -- If we were using GADTs, `x` would have type `m (Repr Int)` and the only way to match was to use
    -- RNum constructor and GHC would be happy, but we are not, and so pattern match failure does
    -- not occur solely by our Gentlemen Agreement.
    -- This is equally relevant for every other method in this instance.
    if x' == 0 then a else b

  op op' (WithRepr a) (WithRepr b) = WithRepr $ do
    RNum a' <- a
    RNum b' <- b
    case op' of
      Plus -> return $ RNum $ a' + b'
      Minus -> return $ RNum $ a' - b'
      Times -> return $ RNum $ a' * b'
      Divide -> if b' == 0 then fail "Divide by zero" else return $ RNum $ a' `div` b'

  lam x (WithRepr a) = WithRepr $ do
    e <- getEnv
    -- A closure must remember environment at its point of definition.
    return $ RAbs e x a 

  app (WithRepr f) (WithRepr a) = WithRepr $ do
    RAbs e x f' <- f
    a' <- a

    addr <- alloc x
    store addr a'

    -- Extend closure's environment with a value for its argument and evaluate it
    withEnv (M.insert x addr e) f'
```

As you can see, this instance ties _any_ fitting monad with our language. By supplying different
monads, we will be able to control the behavior of the interpreter without changing anything in its
code.

Making interpreters
-------------------

With all that in place, we only need to give an instance of `MonadReader` and `MonadState`, and
we'll have an interpreter. The easiest way to obtain these instances is to use monad transformers
from the `mtl` package, but there are other possibilities like the
[capability](http://hackage.haskell.org/package/capability) library or any of the algebraic effects
libraries.

**A simple interpreter**

Let's write a simple interpreter that evaluates programs to their final values. Just stack
transformers in the right order:

```haskell
newtype RInterpreter a
  = RInterpreter
    { getR :: ReaderT VarEnv (MaybeT (StateT (ValStore RInterpreter Repr) Identity)) a
    }
  deriving (Functor, Applicative, Monad, MonadReader VarEnv, MonadState (ValStore RInterpreter Repr), MonadFail)

runR :: RInterpreter a -> (Maybe a, ValStore RInterpreter Repr)
runR = runIdentity . flip runStateT mempty . runMaybeT . flip runReaderT mempty . getR
```

With that, we can run our terms:

```
> print $ runR $ getInterp @_ @Repr $ t63
(Just (RNum 63),fromList [])
```

And an example of failure:

```
> print $ runR $ getInterp @_ @Repr $ tDivZero
(Nothing,fromList [])
```

Higher-order functions work as well:

```
> print $ runR $ getInterp @_ @Repr $ tHO
(Just (RNum 46),fromList [(0,RAbs "x"),(1,RNum 42),(2,RNum 42),(3,RNum 44)])
```

In the last example we can see all values that end up in the store after the interpretation.

As in the original paper, if we simply swap `MaybeT` with `StateT`, there will be no store output in
the case of failure:

```haskell
newtype RInterpreter' a = RInterpreter' { getR' :: ReaderT VarEnv (StateT (ValStore RInterpreter' Repr) (MaybeT Identity)) a }
  deriving (Functor, Applicative, Monad, MonadReader VarEnv, MonadState (ValStore RInterpreter' Repr), MonadFail)

runR' :: RInterpreter' a -> Maybe (a, ValStore RInterpreter' Repr)
runR' = runIdentity . runMaybeT . flip runStateT mempty . flip runReaderT mempty . getR'
```

```
> print $ runR' $ getInterp @_ @Repr $ tDivZero
Nothing
```

**Approximating interpreter**

Now we are ready to make something more interesting &mdash; an interpreter that computes an
_approximation_ of the target program's behavior. This is the second example from the paper and it
amounts to replacing all results of arithmetic operations with an _abstract number_ (`NN`).

For that, we need a new representation type:

```haskell
data NRepr (m :: Type -> Type) where
  NNum :: Int -> NRepr m
  NN :: NRepr m
  NAbs :: VarEnv -> String -> m (NRepr m) -> NRepr m
```

<details class="code-details">
<summary>Show instance</summary>

```haskell
instance Show (NRepr m) where
  showsPrec p (NNum n)
     = showParen
         (p >= 11)
         (showString "NNum " . showsPrec 11 n)
  showsPrec _p_ (NN)
     = showString "NN"
  showsPrec p (NAbs _e x _v)
     = showParen
         (p >= 11)
         (showString "NAbs " . showsPrec 11 x)
```
</details>

and a new instance of `Lang`. This interpreter will be non-deterministic, returning a list of
possible outcomes. We will represent this with an `Alternative` constraint and a `ListT`
transformer.

So, define another `newtype`...

```{.haskell .ignore}
newtype NInterpreter a = NInterpreter { getN :: ReaderT VarEnv (StateT (ValStore NInterpreter) (MaybeT Identity)) a }
  deriving (Functor, Applicative, Monad, MonadReader VarEnv, MonadState (ValStore NInterpreter), MonadFail, Alternative)

runN :: RInterpreter' a -> [(Maybe a, ValStore NInterpreter)]
runN = runIdentity . runListT . flip runStateT mempty . runMaybeT . flip runReaderT mempty . getN
```

Unfortunately, this newtype won't work. GHC derives `Alternative` instance for `NInterpreter` from
`MaybeT`, which short-circuits all `fail`ures. To overcome this, we define our own `MaybeT`-like
transformer with the help of `DerivingVia`:

```haskell
newtype MT m a = MT { getMT :: m (Maybe a) }
   deriving (Functor, Applicative, Monad, MonadFail, MonadState s) via (MaybeT m)

deriving instance (Show a, Show (m (Maybe a))) => Show (MT m a)

instance (Monad m, Alternative m) => Alternative (MT m) where
 empty = MT $ empty
 (MT x) <|> (MT y) = MT $ x <|> y
```

`Alternative` instance for `MT` forwards `<|>` to underlying monad instead of using `Maybe`
features.

Now we can use `MT` to define the actual `NInterpreter`:

```haskell
newtype NInterpreter a = NInterpreter { getN :: ReaderT VarEnv (MT (StateT (ValStore NInterpreter NRepr) (ListT Identity))) a }
  deriving (Functor, Applicative, Monad, MonadReader VarEnv, MonadState (ValStore NInterpreter NRepr), MonadFail, Alternative)

runN :: NInterpreter a -> [(Maybe a, ValStore NInterpreter NRepr)]
runN = runIdentity . runListT . flip runStateT mempty . getMT . flip runReaderT mempty . getN
```

And, of course, we need a `Lang` instance for `NRepr`:

```haskell
instance (MonadInterpreter m NRepr, MonadFail m, Alternative m) => Lang (WithRepr m NRepr) where
  var x = WithRepr $ findAddr x >>= readAddr

  num x = WithRepr $ return $ NNum x

  if0 (WithRepr x) (WithRepr a) (WithRepr b) = WithRepr $ do
    x' <- x
    case x' of
      NNum 0 -> a
      NNum _ -> b
      NN -> a <|> b
      _ -> error "Gentlemen Agreement broken"

  op op' (WithRepr _a_) (WithRepr b) = WithRepr $ do
    case op' of
      Plus -> return $ NN
      Minus -> return $ NN
      Times -> return $ NN
      Divide -> do
        b' <- b
        case b' of
          NNum 0 -> fail "Divide by zero"
          NNum _ -> return $ NN
          NN -> fail "Divide by zero" <|> return NN
          _ -> error "Gentlemen Agreement broken"

  lam x (WithRepr a) = WithRepr $ do
    e <- getEnv
    return $ NAbs e x a 

  app (WithRepr f) (WithRepr a) = WithRepr $ do
    NAbs e x f' <- f
    a' <- a

    addr <- alloc x
    store addr a'

    withEnv (M.insert x addr e) f'
```

And finally we can run it:

```
> print $ runN $ getInterp @_ @NRepr $ tDivZero
[(Nothing,fromList []),(Just NN,fromList [])]
```

As expected, we see both possibilities &mdash; failure and success.

Duplicating code from previous `Lang` instance may be seen as a disadvantage, but it seems natural
and in fact inevitable &mdash; if two interpreters use different runtime representations, they
hardly can share a meaningful amount of code. Of course, we can regard `Repr` as a third "language"
in our problem and write Final encoding for it as well, which would allow for extensibility, but
that seems an overkill.

Extensions
----------

One of the major advantages of solving the Expression Problem (see [[2]](#references) for discussion
of) in the Final style is a possibility to extend the language "for free". 

We chose to omit the recursion from our language to simplify things. Now let's add it back to our
language to see if that advantage holds in our case.

To do that, we only need to define a subclass to our `Lang` type class and write an instance for it:

```haskell
class Lang repr => RecLang repr where
  letrec :: String -> repr (a -> b) -> repr (a -> b)

instance (Monad m, MonadInterpreter m Repr, Lang (WithRepr m Repr)) => RecLang (WithRepr m Repr) where
  letrec x (WithRepr a) = WithRepr $ do
    -- This code is a direct translation of Racket code in the paper
    e <- getEnv
    addr <- alloc x
    let e' = M.insert x addr e
    v <- withEnv e' a
    store addr v
    return v
```

In this extended language we can define classic factorial function:

```haskell
fact :: RecLang repr => repr (Int -> Int)
fact = letrec "f" $ lam "n" (if0 n (num 1) (op Times n (app f (op Minus n (num 1)))))
  where
    n = var "n"
    f = var "f"
```

And check that it indeed works:

```
> print $ runR $ getInterp @_ @Repr $ app fact (num 5)
(Just (RNum 120),fromList [(0,RAbs "n"),(1,RNum 5),(2,RNum 4),(3,RNum 3),(4,RNum 2),(5,RNum 1),(6,RNum 0)])
```

Naturally, one cell in store is occupied by `fact`'s closure itself and others by arguments to all
recursive calls.

**A truly abstract interpreter**

The next step would be to make the store actually finite (sections 3.3 and 4 of the ADI paper). In
our case, this would require changes only in the `MonadInterpreter` instance, which then can use
`<|>` and `asum` of the underlying `Alternative` to account for nondeterminism in the store. We will
not do this here, but we assume that this change will be a rather straightforward one.

Final thoughts
--------------

We've seen that Final Tagless (well, not tagless in our case) style is as expressive for the task of
abstract interpretation and solves the same problem that Initial approaches like free monads and
algebraic effects do.

We've also shown that the major advantage of FT in an Expression Problem still holds in the abstract
interpretation case. This resembles the results from Kiselyov's paper [[4]](#references), where he
builds compilers completely in Final style.

Final Tagless was also used to control monadic effects the interpreter can do. In this post, we were
able to get away with plain old `mtl` for that, but if we were to add more features from the paper,
we would need things like two `StateT`s in a stack, which is a pain in `mtl`. This should not be
regarded as a disadvantage of this approach, though, as there are other libraries without this
limitation. One of them is `capability`, which claims to be "mtl done right". Curiously though,
`capability` does not implement the Nondeterminism effect at the moment, which is crucial for
abstract interpretation.

One more observation of this post is that combining `GADTs` with final encodings gives more freedom
in interpreter implementation, while still letting the compiler prove that our interpreter will be
total.

By using monomorphic store in this concrete case, we lost this totality proof. Instead, possible
pattern match failures occur in multiple interpreter methods. Totality may be recovered by shifting
all failures to a single point, namely into `var` combinator. If the values in store were wrapped in
`Dynamic`, we would be able to use `fromDynamic` to recover the needed type or fail, giving every
other method access to correct types.

As a final note, we would like to point out that from a category-theoretic point of view, the Final
style is not in fact Final, which is acknowledged by Kiselyov and pointed out in [[5]](#references).
Actually, Final and Initial encodings are isomorphic.

However, this does not mean that the whole Final / Initial distinction is completely senseless. It
well may be that one style gives better performance than the other, for example, due to more
optimization possibilities for the compiler. This is known to algebraic effects library authors, who
usually compare their libraries to `mtl` and report comparable performance.

References
----------

1. D. Darais, N. Labich, P. Nguyen and D. Van Horn, "Abstracting definitional interpreters (functional pearl)", Proceedings of the ACM on Programming Languages, vol. 1, no. 12, pp. 1-25, 2017. Available: https://plum-umd.github.io/abstracting-definitional-interpreters/. [Accessed 1 September 2019].
2. O. Kiselyov, "Typed Tagless Final Interpreters", Lecture Notes in Computer Science, pp. 130-174, 2012. Available: http://okmij.org/ftp/tagless-final/course/lecture.pdf. [Accessed 1 September 2019].
3. D. Van Horn and M. Might, "Abstracting abstract machines", Communications of the ACM, vol. 54, no. 9, p. 101, 2011. Available: http://matt.might.net/papers/vanhorn2010abstract.pdf. [Accessed 1 September 2019].
4. J. Careette, O. Kiselyov and C. Shan, "Finally tagless, partially evaluated: Tagless staged interpreters for simpler typed languages", Journal of Functional Programming, vol. 19, no. 5, pp. 509-543, 2009. Available: http://okmij.org/ftp/tagless-final/JFP.pdf. [Accessed 1 September 2019].
5. J. Gibbons and N. Wu, "Folding domain-specific languages", Proceedings of the 19th ACM SIGPLAN international conference on Functional programming - ICFP '14, 2014. Available: http://www.cs.ox.ac.uk/jeremy.gibbons/publications/embedding.pdf. [Accessed 1 September 2019].
