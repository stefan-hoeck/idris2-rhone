||| Provides a data type for Monadic Stream Functions (MSFs)
||| together with associated interface implementations and
||| some core functionality.
|||
||| An MSF is an effectful computation from an input of type `i`
||| to an output of type `o`, that can be described using a rich
||| library of combinators and evaluated using function
||| `Data.MSF.Running.step`,
||| which not only produces an output for every input value
||| but also a new MSF to be used in the next evaluation step.
module Data.MSF.Core

import Data.MSF.Event
import Data.SOP

%default total

mutual
  ||| A heterogeneous list of MSFs. This is used both
  ||| for running several unrelated MSFs in parallel, in
  ||| which case it takes an n-ary product as input
  ||| and produces an n-ary product as output (see
  ||| function `par`), as well as for selecting a single
  ||| MSF to run based on an n-ary sum as input, in which
  ||| case a value of an n-ary sum is produced as output
  ||| (see function `choice` for this use case).
  public export
  data MSFList :  (m : Type -> Type)
               -> (is : List Type)
               -> (os : List Type)
               -> Type where
    Nil  : MSFList m [] []
    (::) :  (sf : MSF m i o)
         -> (sfs : MSFList m is os)
         -> MSFList m (i :: is) (o :: os)

  namespace FanList
    ||| A heterogeneous list of MSFs all of which
    ||| accept the same input type. This is used for
    ||| broadcasting a input value across several MSFs,
    ||| collecting the result as an n-ary product.
    ||| See also function `fan`.
    public export
    data FanList :  (m : Type -> Type)
                 -> (i : Type)
                 -> (os : List Type)
                 -> Type where
      Nil  : FanList m i Nil
      (::) :  (sf : MSF m i o)
           -> (sfs : FanList m i os)
           -> FanList m i (o :: os)

  namespace CollectList
    ||| A heterogeneous list of MSFs all of which
    ||| produce the same type of outup. This is used for
    ||| choosing a single MSF for producing a result based
    ||| on an n-ary sum as input. See also function `collect`.
    public export
    data CollectList :  (m  : Type -> Type)
                     -> (is : List Type)
                     -> (o  : Type)
                 -> Type where
      Nil  : CollectList m Nil o
      (::) :  (sf : MSF m i o)
           -> (sfs : CollectList m is o)
           -> CollectList m (i :: is) o

  ||| A monadic stream function (`MSF`) is used to
  ||| convert streams of input values of type `i` to
  ||| output values of type `o` in a monadic context `m`.
  |||
  ||| The [dunai](https://hackage.haskell.org/package/dunai)
  ||| library implements them as
  ||| `data MSF m i o = MSF (i -> m (o, MSF m i o))`
  ||| but this most general form does not go well with
  ||| the Idris totality checker.
  |||
  ||| It is therefore implemented as a set of primitive
  ||| constructors, some of which are truly primitives,
  ||| some of which are there for reasons of efficiency.
  ||| In later versions of this library, `MSF` might
  ||| no longer be publicly exported, so client code should
  ||| use the provided combinators instead of accessing the
  ||| data constructors directly.
  |||
  ||| `MSF` objects can be stepwise evaluated by invoking
  ||| function `Data.MSF.Running.step`.
  public export
  data MSF : (m : Type -> Type) -> (i : Type) -> (o : Type) -> Type where

    ||| The identity MSF
    Id        :  MSF m i i

    ||| The constant MSF
    Const     :  o -> MSF m i o

    ||| Lifts a pure function to an MSF
    Arr       :  (i -> o) -> MSF m i o

    ||| Lifts an effectful computation to an MSF
    Lifted    :  (i -> m o) -> MSF m i o

    ||| Sequencing of MSFs
    Seq       :  MSF m i x -> MSF m x o -> MSF m i o

    ||| Parallelising MSFs
    Par       :  MSFList m is os -> MSF m (NP I is) (NP I os)

    ||| Broadcasting a value to a list of MSFs
    ||| all taking the same input
    Fan       :  FanList m i os -> MSF m i (NP I os)

    ||| Choosing an MSF based on an n-ary sum as input
    Choice    :  MSFList m is os -> MSF m (NS I is) (NS I os)

    ||| Choosing an MSF (all of which produce the same output)
    ||| based on an n-ary sum as input
    Collect   :  CollectList m is o -> MSF m (NS I is) o

    ||| Feedback loops (stateful computations)
    Loop      :  s -> MSF m (NP I [s, i]) (NP I [s, o]) -> MSF m i o

    ||| Single time switching: Upon the first event,
    ||| the second stream function is calculated,
    ||| evaluated immediately and used henceforth.
    Switch    :  MSF m i (Either e o) -> (e -> MSF m i o) -> MSF m i o

--------------------------------------------------------------------------------
--          Lifting Primitives
--------------------------------------------------------------------------------

||| The identity MSF
export %inline
id : MSF m i i
id = Id

||| A constant MSF
export %inline
const : o -> MSF m i o
const = Const

||| Lifting a pure function to an MSF
export %inline
arr : (i -> o) -> MSF m i o
arr = Arr

||| Lifting an effectful computation to an MSF
export %inline
arrM : (i -> m o) -> MSF m i o
arrM = Lifted

||| Lifting a value in a context to an MSF
export %inline
constM : m o -> MSF m i o
constM = Lifted . const

--------------------------------------------------------------------------------
--          Sequencing MSFs
--------------------------------------------------------------------------------

infixr 1 >>>

||| Sequencing of MSFs
export %inline
(>>>) : MSF m i x -> MSF m x o -> MSF m i o
(>>>) = Seq

--------------------------------------------------------------------------------
--          Paralellising MSFs
--------------------------------------------------------------------------------

||| Runs a bundle of MSFs in parallel. This is
||| a generalization of `(***)` from `Control.Arrow`.
export %inline
par : MSFList m is os -> MSF m (NP I is) (NP I os)
par = Par

||| Broadcasts an input value across a list of MSFs,
||| all of which must accept the same type of input.
||| This is a generalization of `(&&&)` from `Control.Arrow`.
export %inline
fan : FanList m i os -> MSF m i (NP I os)
fan = Fan

||| Apply a binary function to the result of running
||| two MSFs in parallel.
export %inline
elementwise2 : (o1 -> o2 -> o3) -> MSF m i o1 -> MSF m i o2 -> MSF m i o3
elementwise2 f x y = fan [x,y] >>> arr (\[a,b] => f a b)

--------------------------------------------------------------------------------
--          Selecting MSFs
--------------------------------------------------------------------------------

||| Choose an MSF to run depending the input value
||| This is a generalization of `(+++)` from `Control.Arrow`.
export %inline
choice : MSFList m is os -> MSF m (NS I is) (NS I os)
choice = Choice

||| Choose an MSF all of which produce the same output.
||| This is a generalization of `(\|/)` from `Control.Arrow`.
export %inline
collect : CollectList m is o -> MSF m (NS I is) o
collect = Collect

--------------------------------------------------------------------------------
--          Loops and Stateful computations
--------------------------------------------------------------------------------

||| Feedback loops: Given an initial state value,
||| we can feedback the result of each evaluation
||| step and us it as the new state for the next step.
export %inline
feedback : s -> MSF m (NP I [s,i]) (NP I [s,o]) -> MSF m i o
feedback = Loop

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export %inline
Functor (MSF m i) where
  map f = (>>> arr f)

export %inline
Applicative (MSF m i) where
  pure = Const
  (<*>) = elementwise2 apply

export %inline
Semigroup o => Semigroup (MSF m i o) where
  (<+>) = elementwise2 (<+>)

export %inline
Monoid o => Monoid (MSF m i o) where
  neutral = Const neutral

export %inline
Num o => Num (MSF m i o) where
  fromInteger = Const . fromInteger
  (+) = elementwise2 (+)
  (*) = elementwise2 (*)

export %inline
Neg o => Neg (MSF m i o) where
  (-)    = elementwise2 (-)
  negate = map negate

export %inline
Integral o => Integral (MSF m i o) where
  mod = elementwise2 mod
  div = elementwise2 div

export %inline
Fractional o => Fractional (MSF m i o) where
  (/)  = elementwise2 (/)

export %inline
FromString o => FromString (MSF m i o) where
  fromString = const . fromString
