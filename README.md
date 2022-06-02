# idris2-rhone : Monadic Stream Functions in Idris2

This library provides a DSL for writing reactive programs
in Idris2. It was inspired by Haskell's [dunai](https://github.com/ivanperez-keera/dunai)
library, and the implementation adjusted to Idris2 in
such a way that it satisfies the totality checker.

This is still bound to change a lot, as I'm still experimenting
with different additional type level guarantees to make
switching a looping more versatile while keeping the
totality checker happy.

My main focus right now is to use this for writing
single page web application in a declarative manner.
This is therefore developed in parallel with
[idris2-rhone-js](https://github.com/stefan-hoeck/idris2-rhone-js),
which provides DOM bindings for the monadic stream functions
introduced in this library.

## Documentation

There is a growing list of pretty detailed tutorials
in the `src/Doc` folder. For an introduction to the basic
concepts and arrowized functional reactive programme,
[start here](src/Doc/Basics.md).

## Dependencies

For bundling and broadcasting input to several stream functions,
we use the sum and product types for them *idris2-sop* project.
There are additional prerequisites for building the documentation
and for running the tests.

The latest commit is daily tested to build against the current
HEAD of the Idris compiler. Since Idris2 releases are happening
rather infrequently at the moment, it is suggested to use
a package manager like [pack](https://github.com/stefan-hoeck/idris2-pack)
to install and maintain matching versions of the Idris compiler
and this library. Pack will also automatically install all
required dependencies.

### Core Library

* [idris2-sop](https://github.com/stefan-hoeck/idris2-sop)

### Docs

* [idris2-elab-util](https://github.com/stefan-hoeck/idris2-elab-util)
* [idris2-sop](https://github.com/stefan-hoeck/idris2-sop)

### Testing

* [idris2-elab-util](https://github.com/stefan-hoeck/idris2-elab-util)
* [idris2-sop](https://github.com/stefan-hoeck/idris2-sop)
* [idris2-pretty-show](https://github.com/stefan-hoeck/idris2-pretty-show)
* [idris2-hedgehog](https://github.com/stefan-hoeck/idris2-hedgehog)

## About the Name

In Haskell, there is a tradition to name
arrowized functional reactive programming (AFRP)
libraries and derivations thereof after rivers (e.g:
[yampa](https://github.com/ivanperez-keera/Yampa/),
[dunai](https://github.com/ivanperez-keera/dunai),
[bearriver](https://hackage.haskell.org/package/bearriver), and
[rhine](https://hackage.haskell.org/package/rhine)).
When I started experimenting with AFRP in Idris2, I was in the
Swiss canton of Wallis, where the river Rhône (Rhone in German)
has its source, so I thought this would be a fitting name
for this library.
