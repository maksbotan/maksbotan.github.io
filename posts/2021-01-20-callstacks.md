---
title: Capturing call stack with Haskell exceptions
---

Recently I discovered a nice way to capture call stack in Haskell exceptions almost transparently,
and I'm goint to share it in this post

If this is a known technique, let me know, otherwise &mdash; enjoy using it.

## What is a call stack

Suppose somewhere in the program you use `error` to signal an impossible situation:

```haskell
foo :: [a] -> a
foo [] = error "impossible!"
foo a:_ = a

bar :: [Int] -> [Int] -> Int
bar a b = foo a + foo b
```

And then accidentally use it with an empty list:

```haskell
λ> bar [] []
*** Exception: impossible!
CallStack (from HasCallStack):
  error, called at stacks.hs:4:10 in main:Main
```

Obviously, there is an error, but `GHCI` also prints a peculiar thing: a call stack! It contains
only one entry and isn't helpful though... So you go to
[GHC manual](https://downloads.haskell.org/ghc/latest/docs/html/users_guide/) to see what
`HasCallStack` the message is talking about and there it is:
[`HasCallStack` section](https://downloads.haskell.org/ghc/latest/docs/html/users_guide/glasgow_exts.html#hascallstack).

As the manual says, you add `HasCallStack` constraint to your `foo` and `bar` functions:

```haskell
foo :: HasCallStack => [a] -> a
foo [] = error "impossible!"
foo a:_ = a

bar :: HasCallStack => [Int] -> [Int] -> Int
bar a b = foo a + foo b
```

Now the output becomes much more informative:

```haskell
λ> bar [] []
*** Exception: impossible!
CallStack (from HasCallStack):
  error, called at stacks.hs:6:10 in main:Main
  foo, called at stacks.hs:10:11 in main:Main
  bar, called at <interactive>:5:1 in interactive:Ghci1
```

You get function names, module names and even source locations for all calls starting from the
`ghci` prompt down to the point where `error` is called.

Remember, however, that stack is captured only as far from the `error` call as there are
`HasCallStack` constraint. E.g., dropping the constraint from `foo` will also exclude `bar` from the
log:

```haskell
λ> bar [] []
*** Exception: impossible!
CallStack (from HasCallStack):
  error, called at stacks.hs:6:10 in main:Main
```

Still, you get to know the precise location of the `error` call, which is nice.

**Caveat**: `head`, `tail`, `read` and so on use
[`errorWithoutStackTrace`](http://hackage.haskell.org/package/base-4.14.1.0/docs/GHC-Err.html#v:errorWithoutStackTrace)
(for performance reasons), so you won't ever see stack traces from them. One more reason to avoid
`head`!

## Using exceptions

However, using `error` to report errors is not very convenient: you can pass only a `String` as an
argument and so catching specific errors while propagating others becomes very hard and messy.

Fortunately, there is another mechanism in GHC for that: exceptions. So you define your custom
exception type and throw it from the `foo` function like this:

```haskell
data FooException = FooException
  deriving (Show, Exception)

foo :: HasCallStack => [a] -> a
foo [] = throw FooException
foo a:_ = a

bar :: HasCallStack => [Int] -> [Int] -> Int
bar a b = foo a + foo b
```

You run it and except to see the nice exception with a stack trace. But...

```haskell
λ> bar [] []
*** Exception: FooException
```

You get none! What is going on and how `error` is different from
[`throw`](http://hackage.haskell.org/package/base-4.14.1.0/docs/Control-Exception.html#v:throw)?

The reason is that exceptions don't capture the stack trace automatically, even when thrown from a
place with `HasCallStack` context. There is an [open
issue](https://gitlab.haskell.org/ghc/ghc/-/issues/12096) to do so, reported back in 2016, but no
progress was made yet.

## Capturing stacks

But what if we want to capture stack with exceptions? One possible way would be to save the stack
(represented as
[`CallStack`](http://hackage.haskell.org/package/base-4.14.1.0/docs/GHC-Stack.html#t:CallStack)
type) as part of the exception constructor, then make your custom `throwWithStack :: HasCallStack =>
Foo -> IO ()` function and use it everywhere, but that is too cumbersome and you may simply forget
to use the right throwing function.

Fortunately, there is a better way. Recall that magic `HasCallStack` constraint captures call stack
from the point where something annotated with it is used. We don't want to annotate `throw`, but
there is one more thing on the same line &mdash; exception constructor itself! Turns out, you can
use GADTs to capture stack with a exception data:

```haskell
data FooException where
  FooException :: HasCallStack => FooException
```

And then access it in `Show` instance:

```haskell
instance Show FooException where
  show FooException = "FooException\n" <> prettyCallStack callStack

deriving anyclass instance Exception FooException
```

Here `callStack` is provided by `GHC.Stack` and will use `HasCallStack` constraint introduced by
pattern match on `FooException` GADT constructor.

Let's see an example of how it works:

```haskell
λ> bar [] []
*** Exception: FooException
CallStack (from HasCallStack):
  FooException, called at stacks.hs:18:16 in main:Main
  foo, called at stacks.hs:22:11 in main:Main
  bar, called at <interactive>:7:1 in interactive:Ghci1
```

For another example, here is a real call stack I reproduced in our production code:

```haskell
Exception: Operation timeout
CallStack (from HasCallStack):
  TimeOut, called at src/Database/Bolt/Connection.hs:38:36 in hasbolt-0.1.4.3-inplace:Database.Bolt.Connection
  run, called at src/XXX/DB/Impl.hs:42:43 in xxx-0.3.5.0-inplace:XXX.DB.Impl
  runDB, called at src/XXX/DB/Impl.hs:124:14 in xxx-0.3.5.0-inplace:XXX.DB.Impl
  programs, called at src/XXX/API/Program.hs:33:17 in xxx-0.3.5.0-inplace:XXX.API.Program
```

## Final remarks

`HasCallStack` is a magic constraint, so the fact that this trick works may or may not be a
coincidence: some later change in GHC may stop GADT pattern match from affecting how `HasCallStack`
is solved. However, I think that this approach is useful enough and may be used in practice. Just
don't forget to add enough `HasCallStack` to places which can fail.

Don't forget though that `HasCallStack` is not free and sometimes can break some optimizations,
especially if used in recursive functions (that's the reason `head` & friends do not capture the
stack).

Of course, this posts does nothing to help debugging builtin exceptions, like `IOError`. For that,
the usual way is to build with `-prof` and run you code with `+RTS -xc`, as documented in [the
manual](https://downloads.haskell.org/ghc/latest/docs/html/users_guide/runtime_control.html#rts-flag--xc).

## Useful links

- [GHC manual on call
  stacks](https://downloads.haskell.org/ghc/latest/docs/html/users_guide/glasgow_exts.html#hascallstack)
- [GHC manual on stacks from profile build](https://downloads.haskell.org/ghc/latest/docs/html/users_guide/glasgow_exts.html#hascallstack)
- [Haddock for `GHC.Stack`](http://hackage.haskell.org/package/base-4.14.1.0/docs/GHC-Stack.html)
- [Issue to add call stacks to exceptions](https://gitlab.haskell.org/ghc/ghc/-/issues/12096)
- [GHC Proposal for
  that](https://github.com/bgamari/ghc-proposals/blob/stacktraces/proposals/0000-exception-backtraces.rst)
- [Using DWARF debug information in GHC](https://www.well-typed.com/blog/2020/04/dwarf-1/)
