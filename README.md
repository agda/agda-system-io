Overview
========

Minimal I/O binding
-------------------

This library is intended to provide a minimal binding to Haskell IO,
which respects Agda's semantics while still providing the performance
benefits of lazy IO.

The problem with directly binding to Haskell's IO monad is that lazy
IO does not respect Agda's semantics.  For example, given two
programs:

```haskell
hello1 : List Char -> IO String
hello1 [] = putStr "Hello"
hello1 (x :: xs) = putStr "Hello"
```

and:

```haskell
hello2 : List Char -> IO String
hello2 xs = putStr "Hello"
```

It is routine to prove that hello1 and hello2 are extensionally equal,
and so we would expect that:

```haskell
mainX = getContents >>= helloX
```

would have the same behaviour, no matter which helloX function is
plugged in.

Unfortunately, Haskell program equality does not include
eta-equivalence on lists, and so main1 will block waiting for input,
where main2 prints "Hello".

This library provides an implementation of a simple transactional model
of IO.  In this model, all IO has strict semantics, but the programmer
has control over the order of evaluation, via use of the commit command.
All IO is buffered until a commit operation takes place, so the program:

```haskell
putStr "Hello, World\n"
```

prints nothing, whereas the program:

```haskell
putStr "Hello, World\n" >> commit
```

prints the expected greeting.  If data is read lazily, then it is not
made strict until the commit operation.  For example, the program
System.IO.Examples.DevNull reads and discards its input:

```agda
getBytes {lazy} >>= λ bs →
  putStr "Done.\n" >>
  commit
```

runs in constant space, for example when fed a 500M file:

     559,216,832 bytes allocated in the heap
          91,624 bytes copied during GC
          20,392 bytes maximum residency (1 sample(s))
          33,296 bytes maximum slop
               2 MB total memory in use (0 MB lost due to fragmentation)

Its strict equivalent reads the whole file into memory.

Transducers
-----------

There is also a more experimental library which is intended to provide
the benefit of iteratees to Agda IO.  It is based on transducers
(that is automata that can read input and produce output), and is
typed using a variant on session types.  Since automata are explicit
about when they perform input, they are not subject to eta-equivalence,
so can be used without worrying about breaking Agda's semantics.

Currently the transducer library is provided without any bindings
to the I/O library -- this will be fixed soon.

Some simple examples are in System.IO.Examples.Transducers.

Requirements
============

Agda 2.2.6 or 2.2.8, and the Agda standard library 0.3 or 0.4.

Haskell libraries bytestring and utf8-string.

Compiling
=========

```
$ agda -i src -i <agda-stdlib-src> -c src/System/IO/Examples/HelloWorld.agda
```

Testing
=======

```
$ ./HelloWorld
```
