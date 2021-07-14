module Rhone.Types

import Data.Nat
import Data.Vect

import Rhone.Event

%default total

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

addSucc : IsSucc a -> IsSucc b -> IsSucc (a + b)
addSucc ItIsSucc ItIsSucc = ItIsSucc

--------------------------------------------------------------------------------
--          Time
--------------------------------------------------------------------------------

||| To avert rounding errors, we use integers
||| instead of floating point numbers for time. A time span is therefore
||| a strictly positive integer.
|||
||| The semantics of an integral time span of course
||| depend on the use case and sampling rate.
public export
record TimeSpan where
  constructor MkTimeSpan
  value    : Nat
  0 isSucc : IsSucc value

public export
fromInteger : (v : Integer) -> {auto 0 prf : IsSucc (fromInteger v)} -> TimeSpan
fromInteger v = MkTimeSpan (fromInteger v) prf

public export
Semigroup TimeSpan where
  (MkTimeSpan v1 s1 <+> MkTimeSpan v2 s2) = MkTimeSpan (v1 + v2) (addSucc s1 s2)

--------------------------------------------------------------------------------
--          Signal Vectors
--------------------------------------------------------------------------------

||| Describes the value stored at a single position in a signal vector.
|||
||| A signal is either continuous (`C`) or discrete (an event `E`).
public export
data SigDesc : Type where
  E : Type -> SigDesc
  C : Type -> SigDesc

||| Calculates the type of a value stored at a
||| single position in a signal vector from
||| the given signal description.
public export
DescType : SigDesc -> Type
DescType (E x) = Event x
DescType (C x) = x

||| A description of a signal vector is a
||| vector holding signal descriptions.
public export
SVDesc : Nat -> Type
SVDesc n = Vect n SigDesc

||| A signal vector is a heterogeneous list indexed
||| over the a vector of descriptions, describing the
||| type of the value stored at each position.
|||
||| Example:
|||
||| ```idris example
||| svect : SVect [C Int, E Time, E String]
||| svect = [12, Ev 8, NoEvent]
||| ```
public export
data SVect : SVDesc n -> Type where
  Nil  : SVect []
  (::) : (v : DescType d) -> SVect ds -> SVect (d :: ds)

||| Calculates a function type required to consume a
||| signal vector of the given description.
public export
SVFun : (description : SVDesc n) -> Type -> Type
SVFun []        x = x
SVFun (d :: ds) x = DescType d -> SVFun ds x

||| Consumes a signal vector using the given n-ary function.
public export
collapse : SVFun i t -> SVect i -> t
collapse v []        = v
collapse f (x :: xs) = collapse (f x) xs

||| Concatenation of signal vectors.
public export
(++) : SVect as -> SVect bs -> SVect (as ++ bs)
(++) []        ys = ys
(++) (x :: xs) ys = x :: (xs ++ ys)

||| Splits a signal vector into two parts at the given
||| implicit position.
public export
split :  {pos : Nat}
      -> {0 xs : SVDesc pos}
      -> SVect (xs ++ ys)
      -> (SVect xs, SVect ys)
split {pos = 0} {xs = []}         x        = ([], x)
split {pos = (S k)} {xs = _ :: _} (h :: t) = 
  let (a,b) = split t in (h :: a, b)

--------------------------------------------------------------------------------
--          Causality
--------------------------------------------------------------------------------

||| Causality descriptor.
|||
||| This is used to describe whether a signal function
||| is decoupled (its outpt at time t only depends on
||| its inputs at times t' < t) or causal (its output at
||| time t might depend also on its input at time t).
|||
||| This distinction is important for looping. In order
||| to generate a feedback loop with provably total evaluation
||| semantics, the looping part has to be decoupled as its
||| output is needed to create part of the input of
||| the signal function before its input from the loop is
||| available.
public export
data Causality = Dec | Cau

||| Causality of parallel combinations of signal functions.
|||
||| Parallelized signal functions are only decoupled, if
||| the individual parts are decoupled.
public export
par : Causality -> Causality -> Causality
par Dec Dec = Dec
par _ _     = Cau

||| Causality of serial combinations of signal functions.
|||
||| Serial signal functions are decoupled, if
||| at least one of the individual parts is decoupled.
public export
ser : Causality -> Causality -> Causality
ser Cau Cau = Cau
ser _ _     = Dec

--------------------------------------------------------------------------------
--          Signal Function
--------------------------------------------------------------------------------

||| Function over signal vectors.
|||
||| This is the core data type describing a reactive network.
||| While its constructors are publicly available, values of
||| this type should in general be created through (a combination of)
||| the many combinators provided by this library.
|||
||| The data type is indexed over the types of values stored in the
||| input signal vector and the types of values stored in the
||| output signal vector as well as the signal function's causality.
|||
||| Note, that for reasons of efficiency, this data type
||| has more data constructors than strictly necessary.
public export
data SF :  (input  : SVDesc m)
        -> (output : SVDesc n)
        -> (cau    : Causality)
        -> Type where

  ||| The constant signal function.
  Const  : SVect o -> SF i o Dec

  ||| Causal, stateless signal function, independent of time.
  Arr    : (f : SVect i -> SVect o) -> SF i o Cau

  ||| Primitive stateful, causal signal function.
  ||| Requires its input signal vector in order
  ||| to create the output and new state.
  Prim   :  {0 st : Type}
         -> st
         -> (run : TimeSpan -> st -> SVect i -> (st, SVect o))
         -> SF i o Cau

  ||| Primitive stateful, decoupled signal function.
  ||| Can produce its output without requiring its input
  ||| signal vector, which is only needed to generate
  ||| the updated state.
  DPrim  :  {0 st : Type}
         -> st
         -> (run : TimeSpan -> st -> (SVect i -> st, SVect o))
         -> SF i o Dec

  ||| Serial combination of signal functions.
  ||| If one of the two signal function is decoupled, the
  ||| resulting signal function as a whole is decoupled.
  Ser    :  {d1,d2 : _}
         -> SF i x d1
         -> SF x o d2
         -> SF i o (d1 `ser` d2)

  ||| Parallel combination of signal functions.
  ||| The result is only decoupled, if both of the
  ||| given signal functions are decoupled.
  Par    :  {d1,d2 : _}
         -> {n : _}
         -> {0 i1 : SVDesc n}
         -> SF i1 o1 d1
         -> SF i2 o2 d2
         -> SF (i1 ++ i2) (o1 ++ o2) (d1 `par` d2)

  ||| Fanning out of signal functions.
  ||| The result is only decoupled, if both of the
  ||| given signal functions are decoupled.
  Fan    :  {d1,d2 : _}
         -> SF i o1 d1
         -> SF i o2 d2
         -> SF i (o1 ++ o2) (d1 `par` d2)

  ||| Feedback loop. In order to get a provably total
  ||| evaluation function, the feedback signal function
  ||| must be decoupled: It must be able to generate
  ||| its output without having access at its input at
  ||| the current time.
  Loop   :  {n : _}
         -> {0 bs : SVDesc n}
         -> SF (as ++ cs) (bs ++ ds) d1
         -> SF ds cs Dec
         -> SF as bs d1
