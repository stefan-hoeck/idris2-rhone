# An Introduction to Monadic Stream Functions

This tutorial gives an introduction to monadic
stream functions (MSFs), providing examples of
how to setup networks of such functions for defining
reactive behaviors.
Since I use MSFs mainly as an experimental tool to
write reactive web pages in
[idris2-rhone-js](https://github.com/stefan-hoeck/idris2-rhone-js),
the examples will - for the time being - come from
that field.

This is a literate Idris2 file, so we need some imports first:

```idris
module Doc.Basics

import Control.Monad.State
import Data.MSF
import Data.Nat
import Generics.Derive

%language ElabReflection
%default total
```

## What are MSFs?

To the best of my knowledge, MSFs have first been introduced
in Haskell's [dunai](https://hackage.haskell.org/package/dunai)
library. There is also a nice
[article](https://www.cs.nott.ac.uk/~psxip1/#FRPRefactored)
describing the concept of MSFs and the general idea behind
arrowized functional reactive programming (AFRP).
I am not going to give an introduction to functional
reactive programming and its semantic model here.
I'd rather like to show what
MSFs can be used for and how they work internally.
However, I sometimes will pick a simple example from FRP
to demonstrate a certain use case.

An MSF can be thought of having the following structure
(given in Haskell code, as this definition does not go well
with the totality checker of Idris2):

```haskell
data MSF m a b = MSF { step :: a -> m (b, MSF m a b) }
```

The above definition is the one used by the *dunai* library,
although `step` is called `unMSF` there. What this does
is the following: It takes a value of an input type `a`
runs an effectful computation in monadic context `m`,
and returns a result of type `b` together with a new
monadic stream function, which will then be used to
process the next piece of input.

So MSFs describe effectful computations *the structure of
which can change with each evaluation step*. They are typically
used to process streams of input like the ones coming from
a graphical user interface or other external source.
They come with a plethora of combinators to describe
networks of computations potentially taking their input
from many different sources.

### The Implementaion used in *rhone*

As mentioned above, the most general form of MSFs as defined
in *dunai*, does not go well with the totality checker. On the
other hand it is very useful to be able to write provably
total networks of stream functions. As is often the case
in Haskell, the examples in the article mentioned above
make strong use of (arbitrary) recursion and laziness to set
up interesting and powerful stream networks and
programmers have to be very careful
to not come up with an unsound MSF that will loop forever.
It is my hope that Idris and its totality checker
will be able to safe us from falling into this trap most
of the time.

The actual implementation in `Data.MSF` is therefore a
sum type consisting of several constructors, some
of which define primitive operations, some of which are
there because they let us handle typical use cases more
efficiently. However, there is still a function called `step`
with exactly the expected type, but it is used for
single step evaluation of a stream function not for
their actual internal representation.

There are some other deviations from *dunai* more specific to Idris
and dependent types, about which we will talk soon enough.

### About using this Tutorial

Before we start: You can try the examples in this module
at the REPL: There are two functions (`embed` and `embedI`),
which run an MSF on a list of input values producing a list
of output values of the same length. Just load this document
into the REPL

```repl
rlwrap idris2 --find-ipkg src/Doc/Basics.md
```

and invoke `embedI` with a list of input values and a
stream function:

```repl
Doc.Basics> embedI ["foo", "bar"] (arr Prelude.reverse)
["oof", "rab"]
```

## Baby Steps: Lifting and Sequencing pure and effectful Functions

MSFs are effectful computations. We therefore expect to
be able to lift values, pure functions, and effectful
computations into the MSF context and run them in sequence
as we'd do with common function composition.
This can be achieved with utilities `const`, `id`, `arr`, `arrM`,
and operators `(^>>)`, `(>>>)`, `(>>^)`. For instance, assume
we have an effectful way for fetching a number from an external
resource and would like to do so, square the number and write
the result to some other resource, here's how to do that (we
abstract over the effectful computations in order to be able
to try this at the REPL):

```idris
square : Num n => n -> n
square x = x * x

calc : m Nat -> (String -> m ()) -> MSF m () ()
calc fetch pr = constM fetch >>> square ^>> show ^>> arrM pr
```

We can run this at the REPL, but if we just use `Identity`
as our context, this won't produce any interesting result:

```repl
Doc.Basics> embedI [(),()] $ calc (pure 1) (const $ pure ())
[(), ()]
```

Let's come up with a better context: The state monad.

```idris
record AppSt where
  constructor MkAppSt
  num : Nat
  out : List String

ini : AppSt
ini = MkAppSt 0 Nil

Eff : Type -> Type
Eff = State AppSt

getNat : Eff Nat
getNat = modify (record {num $= S}) >> map num get

putStr : String -> Eff ()
putStr s = modify (record {out $= (s ::)})
```

Let's try this:

```repl
Doc.Basics> execState ini (embed [(),(),(),()] $ calc getNat putStr)
MkAppSt 4 ["16", "9", "4", "1"]
```

## Static Networks: Parallelisation and Broadcasting

A typical use case consists of collecting input from several sources,
passing them through distinct stream networks and collecting
the results afterwards. For instance, consider an application
collecting mouse clicks: Their x and y coordinates plus the
button clicked. We'd like to transform each piece of data differently:
The x-axis should be scaled by a factor of two, the y-axis
should be translated by 10 and the button should be converted
to a colour. In addition, each computation should log its input
to a suitable logging facility.

The classical way to do this in arrowized FRP is to use
the `(***)` operator from `Control.Arrow` in contrib. However,
this gets cumbersome pretty quickly resulting in cluttered
sequences of infix operators. Haskell introduced a language extension
with special syntax for this, but this is Idris, and we don't
have such an extension. What we do have, though, is great support for
list syntax and the ability to easily make use of type-level
computations. We therefore use a special heterogeneous
list type `Data.MSF.MSFList` for defining lists of
monadic stream functions and run them in parallel.
Instead of pairs, we use the n-ary products from the *sop*
library as the resulting input and output types.

```idris
data Button = Lft | Rgt | Mdl

%runElab derive "Button" [Generic,Meta,Show,Eq]

toColor : Button -> String
toColor Lft = "red"
toColor Rgt = "blue"
toColor Mdl = "green"

mouse : (log : String -> m ()) -> MSF m (NP I [Int16,Int16,Button]) String
mouse log =
  par [ withEffect (\x => log #"x: \#{show x}"#) >>^ (*2)
      , withEffect (\y => log #"y: \#{show y}"#) >>^ (+10)
      , withEffect (log . show) >>^ toColor
      ] >>^ (\[x,y,c] => #"x: \#{show x}, y: \#{show y}, c: \#{c}"#)

runMouse : List (NP I [Int16,Int16,Button]) -> (AppSt, List String)
runMouse ps = runState ini $ embed ps (mouse putStr)
```

Another typical use case is to broadcast some input common
to several stream functions to all of them and collect
the result in a product type. The classical way to do this
is by using the `(&&&)` operator. In Idris, we can again use a
(heterogeneous) list type for this: `Data.MSF.FanList`.

For instance, let us take an input in Kelvin, and
calculate the temperature in Celsius and Fahrenheit
from it, putting together all three values in a string.

```idris
toCelsius : Double -> Double
toCelsius x = x - 273.15

toFahrenheit : Double -> Double
toFahrenheit x = x * 9 / 5 - 459.67

temp : (log : String -> m ()) -> MSF m Double String
temp log =
  fan [ withEffect (log . show)
      , arr toCelsius
      , arr toFahrenheit ] >>^
  (\[k,c,f] => #"\#{show k} K, \#{show c} °C, \#{show f} °F"#)

runTemp : List Double -> (AppSt, List String)
runTemp vs = runState ini $ embed vs (temp putStr)
```

## Making a Choice: Using Sum Types to select MSFs

We sometimes need to choose between two or more
stream functions, depending on an input value.
The canonical example is to make a choice based
on `Left` or `Right`, leading to a result, which
is again `Left` or `Right`. This can again be generalized
by using an n-ary sum to select from an n-ary product
of signal functions. The result will be a sum type
of the same arity:

```idris
record MouseClick where
  constructor MkMC
  x   : Int32
  y   : Int32
  btn : Button

%runElab derive "MouseClick" [Generic,Meta,Show,Eq]

record Key where
  constructor MkKey
  c     : Char
  shift : Bool

%runElab derive "Key" [Generic,Meta,Show,Eq]

record Input where
  constructor MkInput
  value : String

%runElab derive "Input" [Generic,Meta,Show,Eq]

events :  (out : String -> m ())
       -> MSF m (NS I [MouseClick,Key,Input]) (NS I [Button,Char,String])
events out = choice
  [ withEffect (out . show) >>^ btn
  , withEffect (out . show) >>^ c
  , withEffect (out . show) >>^ value
  ]

eventsExample : (AppSt, List (NS I [Button,Char,String]))
eventsExample = runState ini $ embed vs (events putStr)
  where vs : List (NS I [MouseClick,Key,Input])
        vs = [ inject $ MkKey 'C' True
             , inject $ MkInput "hello world"
             , inject $ MkMC 12 100 Rgt
             ]
```

There are many additional predefined combinators for
dealing with the concept of making a choice based on
an input value, all of which are using one of the
two primitives `choice` or `collect` internally.

## Feedback: Stateful Computations

Whenever we need to accumulate values, we use one
of the feedback combinators. Let's do some real
functional reactive programming. First, we need a
notion of time and time deltas:

```idris
DTime : Type
DTime = Nat

Time : Type
Time = Nat
```

If we are going to use MSFs to emulate arrowized functional
reactive programming, we are going to need an input of
time deltas for many operations. There are several ways
to go about this: We could use MSFs pairing the
current time delta with each input value:
`MSF m (NP I [DTime,i]) o`. This gets cumbersome if
we start nesting networks of signal functions and need
to make sure the time deltas are passed on to all subsystems.
We could also use some kind of reader monad, where asking
for the current time delta is just a monadic action.
Here, I generalize the above by just passing an implicit
getter function as an argument to all combinators.

For instance, if we get an input of time deltas, we can calculate the
time since when the system was running:

```idris
time : (dt : m DTime) => MSF m i Time
time = constM dt >>> accumulateWith (+) 0
```

We can also use time deltas to calculate integrals
of time-varying entities:

```idris
integral_ : (dt : m DTime) => MSF m Double Double
integral_ =
  fan [id, constM dt] >>>
  feedback 0 (arr (\[acc,[v,d]] => let a2 = acc + v * cast d in [a2,a2]))
```

The above uses the `feedback` primitive directly. However, in this case it
is more convenient, to use `accumulateWith`:

```idris
integral : (dt : m DTime) => MSF m Double Double
integral =   fan [id, constM dt]
         >>> accumulateWith (\[v,d],acc => acc + v * cast d) 0
```

With this we can simulate the movement (velocity
and height) of a ball in vertical free fall:

```idris
Acceleration : Type
Acceleration = Double

Velocity : Type
Velocity = Double

Position : Type
Position = Double

g : Acceleration
g = -9.81

velocity : m DTime => (v0 : Velocity) -> MSF m Acceleration Velocity
velocity v0 = integral + const v0

position : m DTime => (p0 : Position) -> MSF m Velocity Position
position p0 = integral + const p0

record Ball where
  constructor MkBall
  pos : Position
  vel : Velocity

ball : m DTime => (ini : Ball) -> MSF m i Ball
ball ini =   const g >>> velocity ini.vel
         >>> fan [position ini.pos, id]
         >>^ (\[p,v] => MkBall p v)

ballGame : m DTime -> (ini : Ball) -> MSF m i String
ballGame dt ini = fan [time, ball ini] >>^ dispBall
  where dispBall : NP I [Time,Ball] -> String
        dispBall [t,MkBall p v] =
          #"t: \#{show t}; y: \#{show p}; v: \#{show v}"#

testBallGame : List String
testBallGame = embedI (replicate 10 ()) (ballGame (Id 1) $ MkBall 500 0)
```
