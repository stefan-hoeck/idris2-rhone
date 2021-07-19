module Rhone.Types

import public Data.Nat
import public Data.Vect

import Rhone.Event

%default total

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

-- Proof that the sum of two positive naturals is again
-- a positive natural
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
||| A signal is either continuous (`C`), a countable list of
||| discrete events (`E`), or a step signal (`S`), which is constant
||| except for a countable number of changes.
public export
data SVDesc : Type where
  E : Type -> SVDesc
  C : Type -> SVDesc
  S : Type -> SVDesc
  P : SVDesc -> SVDesc -> SVDesc

||| Calculates the type of a value representing a signal vector
public export
Sample : SVDesc -> Type
Sample (E x)   = Maybe x
Sample (C x)   = x
Sample (S x)   = x
Sample (P x y) = (Sample x, Sample y)

--------------------------------------------------------------------------------
--          Initialisation
--------------------------------------------------------------------------------

public export
data Initialization = Ini | Uni

--------------------------------------------------------------------------------
--          Signal Functions
--------------------------------------------------------------------------------

public export
record Node (st : Type) (input : SVDesc) (output : SVDesc) where
  constructor MkNode
  state : st
  run   : TimeSpan -> Sample input -> st -> (st, Sample output)

||| Function over signal vectors.
|||
||| This is the core data type describing a reactive network.
||| While its constructors are publicly available, values of
||| this type should in general be created through (a combination of)
||| the many combinators provided by this library.
|||
||| The data type is indexed over the types of values stored in the
||| input signal vector and the types of values stored in the
|||
||| Note, that for reasons of efficiency, this data type
||| has more data constructors than strictly necessary.
public export
data SF_ :  (ini    : Initialization)
         -> (input  : SVDesc)
         -> (output : SVDesc)
         -> Type where

   ||| The identity signal function
   Id     : SF_ ini i i

   ||| The identity signal function
   First  : SF_ ini (P as bs) as

   ||| The identity signal function
   Second : SF_ ini (P as bs) bs

   ||| The constant signal function.
   Const  : Sample o -> SF_ ini i o

   ||| Stateless signal function, independent of time.
   Arr    : (f : Sample i -> Sample o) -> SF_ ini i o

   ||| Sequential combination of signal functions
   Seq    : SF_ ini i x -> SF_ ini x o -> SF_ ini i o

   ||| Fanning out of signal functions
   Fan    : SF_ ini as bs  -> SF_ ini as cs -> SF_ ini as (P bs cs)

   ||| Primitive stateful uninitialized signal function.
   UPrim   :  {0 st : Type}
           -> (Sample i -> (Node st i o, Sample o))
           -> SF_ Uni i o

   ||| Primitive stateful initialized signal function.
   IPrim   :  {0 st : Type} -> Node st i o -> SF_ Ini i o

   RSwitch :  SF_ ini i (P o $ E e)
           -> (e -> SF_ Uni i (P o $ E e))
           -> SF_ ini i o


--------------------------------------------------------------------------------
--          Evaluation
--------------------------------------------------------------------------------

mutual
  step0 : SF_ Uni i o -> Sample i -> (SF_ Ini i o, Sample o)
  step0 Id i          = (Id, i)
  step0 First (x, _)  = (First, x)
  step0 Second (_, y) = (Second, y)
  step0 (Const x) _   = (Const x, x)
  step0 (Arr f) i     = (Arr f, f i)
  step0 (Seq ix xo) i = 
    let (ix2,x) = step0 ix i
        (xo2,o) = step0 xo x
     in (Seq ix2 xo2, o)

  step0 (Fan asbs ascs) as = 
    let (asbs2,bs) = step0 asbs as
        (ascs2,cs) = step0 ascs as
     in (Fan asbs2 ascs2, (bs,cs))

  step0 (UPrim f) i = let (node,o) = f i in (IPrim node, o)
  step0 (RSwitch sf f) i = case step0 sf i of
    (sf2, (o, Nothing)) => (RSwitch sf2 f, o)
    (_  , (o, Just e))  => let (sf2,(o,_)) = step0 (f e) i
                            in (RSwitch sf2 f, o)

  step : TimeSpan -> SF_ Ini i o -> Sample i -> (SF_ Ini i o, Sample o)
  step _ Id i          = (Id, i)
  step _ First (x, _)  = (First, x)
  step _ Second (_, y) = (Second, y)
  step _ (Const x) _   = (Const x, x)
  step _ (Arr f) i     = (Arr f, f i)
  step t (Seq ix xo) i = 
    let (ix2,x) = step t ix i
        (xo2,o) = step t xo x
     in (Seq ix2 xo2, o)

  step t (Fan asbs ascs) as = 
    let (asbs2,bs) = step t asbs as
        (ascs2,cs) = step t ascs as
     in (Fan asbs2 ascs2, (bs,cs))

  step t (IPrim $ MkNode st run) i =
    let (st2,o) = run t i st
     in (IPrim $ MkNode st2 run, o)

  step t (RSwitch sf f) i = case step t sf i of
    (sf2, (o, Nothing)) => (RSwitch sf2 f, o)
    (_  , (o, Just e))  => let (sf2,(o,_)) = step0 (f e) i
                            in (RSwitch sf2 f, o)
