module Rhone.Basic

import Rhone.Types

infixr 1 >>>

||| The identity signal function.
export
id : SF i i Cau
id = Id

||| The constant signal function, which
||| always returns the same value.
export
const : o -> SF i (S o) Dec
const = Const

export %inline
(>>>) : {c1,c2 : _} -> SF i x c1 -> SF x o c2 -> SF i o (c1 `or` c2)
(>>>) = Seq c1 c2

--------------------------------------------------------------------------------
--          Initialization
--------------------------------------------------------------------------------

infixr 0 ==>, >==, -=>, >=-

export
initially : Sample o -> SF o o Cau
initially v = mkSFTimeless (\m,s => (Nothing,fromMaybe s m)) (Just v)

export
modInitial : (Sample o -> Sample o) -> SF o o Cau
modInitial f = mkSFTimeless (\m,s => (Nothing,fromMaybe id m s)) (Just f)

export
(==>) : {c : _} -> Sample o -> SF i o c -> SF i o c
v ==> sf = rewrite OrCau c in sf >>> initially v

export
(-=>) : {c : _} -> (Sample o -> Sample o) -> SF i o c -> SF i o c
f -=> sf = rewrite OrCau c in sf >>> modInitial f

export
(>==) : {c : _} -> Sample i -> SF i o c -> SF i o c
v >== sf = initially v >>> sf

export
(>=-) : {c : _} -> (Sample i -> Sample i) -> SF i o c -> SF i o c
f >=- sf = modInitial f >>> sf

--------------------------------------------------------------------------------
--          Lifting Functions
--------------------------------------------------------------------------------

||| Signal kind: Event, Continuous, and Step
public export
data Kind = KE | KC | KS

||| Proof that there is an n-ary function
||| to convert an sample from a signal function
||| to a single value.
|||
||| We keep track of the signal `Kind` to calculate
||| the kind of the output sample.
|||
||| There rules are as follows:
|||   (a) If at least one of the input values has kind `KE` (an event)
|||       the output value has also kind `KE`.
|||
|||   (b) If at least one of the input values has kind `KC`
|||       (a continuous signal) and (b) does not apply,
|||       the otput value has also kind `KC`.
|||
|||   (c) Only if all input signals have kind `KS` does the output
|||       signal have kind `KS
public export
data Liftable : Kind -> SVDesc -> Type where
  LE  : (0 x : Type) -> Liftable KE (E x)
  LC  : (0 x : Type) -> Liftable KC (C x)
  LS  : (0 x : Type) -> Liftable KS (S x)
  PE  : (0 x : Type) -> Liftable k d -> Liftable KE (P (E x) d)
  PS  : (0 x : Type) -> Liftable k d -> Liftable k (P (S x) d)
  PCE : (0 x : Type) -> Liftable KE d -> Liftable KE (P (C x) d)
  PCC : (0 x : Type) -> Liftable KC d -> Liftable KC (P (C x) d)
  PCS : (0 x : Type) -> Liftable KS d -> Liftable KC (P (C x) d)

||| Calculate the type of an n-ary function with the given
||| return type from a `Liftable k d`.
public export
0 Fun : Liftable k d -> Type -> Type
Fun (LE x)    res = x -> res
Fun (LC x)    res = x -> res
Fun (LS x)    res = x -> res
Fun (PE x y)  res = x -> Fun y res
Fun (PS x y)  res = x -> Fun y res
Fun (PCE x y) res = x -> Fun y res
Fun (PCC x y) res = x -> Fun y res
Fun (PCS x y) res = x -> Fun y res

applyS : (l : Liftable KS d) -> Fun l t -> Sample d -> t
applyS (LS _)   f v     = f v
applyS (PS _ r) f (v,w) = applyS r (f v) w

applyC : (l : Liftable KC d) -> Fun l t -> Sample d -> t
applyC (LC  _)   f v      = f v
applyC (PS  _ r) f (v, w) = applyC r (f v) w
applyC (PCC _ r) f (v, w) = applyC r (f v) w
applyC (PCS _ r) f (v, w) = applyS r (f v) w

applyE : (l : Liftable k d) -> Fun l t -> Sample d -> Maybe t 
applyE (LE _)    f v            = f <$> v
applyE (LC _)    f v            = Just $ f v
applyE (LS _)    f v            = Just $ f v
applyE (PS _  r) f (v, w)       = applyE r (f v) w
applyE (PCE _ r) f (v, w)       = applyE r (f v) w
applyE (PCC _ r) f (v, w)       = applyE r (f v) w
applyE (PCS _ r) f (v, w)       = applyE r (f v) w
applyE (PE _  r) f (Nothing, w) = Nothing
applyE (PE _  r) f (Just v,  w) = applyE r (f v) w

||| Lift an n-ary function over a tuple of
||| step signals.
export
liftS : {auto l : Liftable KS d} -> Fun l t -> SF d (S t) Cau
liftS f = mkSFStateless (applyS l f)

||| Lift an n-ary function over a tuple of non-event signals,
||| of which at least one is continuous.
export
liftC : {auto l : Liftable KC d} -> Fun l t -> SF d (C t) Cau
liftC f = mkSFStateless (applyC l f)

||| Lift an n-ary function over a tuple of signals,
||| of which at least one is an event.
export
liftE : {auto l : Liftable KE d} -> Fun l t -> SF d (E t) Cau
liftE f = mkSFStateless (applyE l f)
