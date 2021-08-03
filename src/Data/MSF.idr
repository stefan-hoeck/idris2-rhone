module Data.MSF

import Control.Monad.Either
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

%default total

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
  D : SVDesc -> SVDesc -> SVDesc

||| Calculates the type of a value representing a signal vector
public export
Sample : SVDesc -> Type
Sample (E x)   = Maybe x
Sample (C x)   = x
Sample (S x)   = x
Sample (P x y) = (Sample x, Sample y)
Sample (D x y) = Either (Sample x) (Sample y)

public export
data MSF : (m : Type -> Type) -> (i : SVDesc) -> (o : SVDesc) -> Type where
  Id        :  MSF m i i
  Const     :  Sample o -> MSF m i o
  Arr       :  (Sample i -> Sample o) -> MSF m i o
  Lifted    :  (Sample i -> m (Sample o)) -> MSF m i o
  Seq       :  MSF m i x -> MSF m x o -> MSF m i o
  Par       :  MSF m i1 o1 -> MSF m i2 o2 -> MSF m (P i1 i2) (P o1 o2)
  Fan       :  MSF m i o1 -> MSF m i o2 -> MSF m i (P o1 o2)
  Choice    :  MSF m i1 o1 -> MSF m i2 o2 -> MSF m (D i1 i2) (D o1 o2)
  Loop      :  (Sample s) -> MSF m (P i s) (P o s) -> MSF m i o
  RunReader :  MSF (ReaderT e m) i o -> MSF m (P (C e) i) o
  RunState  :  MSF (StateT s m) i o -> MSF m (P (C s) i) (P (C s) o)
  RunEither :  MSF (EitherT e m) i o
            -> (e -> (Sample o, MSF (EitherT e m) i o))
            -> MSF m i o

--------------------------------------------------------------------------------
--          Lifting Functions
--------------------------------------------------------------------------------

||| Signal kind: Event, Continuous, and Step
public export
data Kind = KE | KC | KS

||| Proof that there is an n-ary function
||| to convert a sample from a signal function
||| to a single value.
|||
||| We keep track of the signal `Kind` to calculate
||| the kind of the output sample.
|||
||| The rules are as follows:
|||
|||   (a) If at least one of the input values has kind `KE` (an event)
|||       the output value has also kind `KE`.
|||
|||   (b) If at least one of the input values has kind `KC`
|||       (a continuous signal) and (a) does not apply,
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
liftS : {auto l : Liftable KS d} -> Fun l t -> MSF m d (S t)
liftS f = Arr (applyS l f)

||| Lift an n-ary function over a tuple of non-event signals,
||| of which at least one is continuous.
export
liftC : {auto l : Liftable KC d} -> Fun l t -> MSF m d (C t)
liftC f = Arr (applyC l f)

||| Lift an n-ary function over a tuple of signals,
||| of which at least one is an event.
export
liftE : {auto l : Liftable KE d} -> Fun l t -> MSF m d (E t)
liftE f = Arr (applyE l f)

--------------------------------------------------------------------------------
--          Primitives
--------------------------------------------------------------------------------

infixr 1 >>>
infixr 3 &&&, ***

namespace C
  export %inline
  id : MSF m (C i) (C i)
  id = Id

  export %inline
  arr : (i -> o) -> MSF m (C i) (C o)
  arr = Arr

  export %inline
  arrM : (i -> m o) -> MSF m (C i) (C o)
  arrM = Lifted

namespace S
  export %inline
  id : MSF m (S i) (S i)
  id = Id

  export %inline
  const : o -> MSF m i (S o)
  const = Const

  export %inline
  arr : (i -> o) -> MSF m (S i) (S o)
  arr = Arr

  export %inline
  arrM : (i -> m o) -> MSF m (S i) (S o)
  arrM = Lifted

namespace E
  export %inline
  id : MSF m (E i) (E i)
  id = Id

  export %inline
  arr : (i -> o) -> MSF m (E i) (E o)
  arr = Arr . map

  export %inline
  arrM : Applicative m => (i -> m o) -> MSF m (E i) (E o)
  arrM = Lifted . traverse

  export %inline
  always : o -> MSF m i (E o)
  always = Const . Just

  export %inline
  never : MSF m i (E o)
  never = Const Nothing

export %inline
(>>>) : MSF m i x -> MSF m x o -> MSF m i o
(>>>) = Seq

export %inline
(***) : MSF m i1 o1 -> MSF m i2 o2 -> MSF m (P i1 i2) (P o1 o2)
(***) = Par

export %inline
(&&&) : MSF m i o1 -> MSF m i o2 -> MSF m i (P o1 o2)
(&&&) = Fan

export %inline
feedback : Sample s -> MSF m (P i s) (P o s) -> MSF m i o
feedback = Loop

export %inline
runReader : MSF (ReaderT e m) i o -> MSF m (P (C e) i) o
runReader = RunReader

export %inline
runState : MSF (StateT s m) i o -> MSF m (P (C s) i) (P (C s) o)
runState = RunState

export %inline
runEither :  MSF (EitherT e m) i o
          -> (e -> (Sample o, MSF (EitherT e m) i o))
          -> MSF m i o
runEither = RunEither

-- export
-- morph : (f : forall c . m1 c -> m2 c) -> MSF m1 i o -> MSF m2 i o
-- morph _ Id              = Id
-- morph _ (Const x)       = Const x
-- morph _ (Arr g)         = Arr g
-- morph f (Lifted g)      = Lifted $ f . g
-- morph f (Seq x y)       = Seq (morph f x) (morph f y)
-- morph f (Choice x y)    = Choice (morph f x) (morph f y)
-- morph f (Par x y)       = Par (morph f x) (morph f y)
-- morph f (Fan x y)       = Fan (morph f x) (morph f y)
-- morph f (Loop x y)      = Loop x (morph f y)
-- morph f (RunReader x)   = RunReader $ morph (mapReaderT f) x
-- morph f (RunState x)    = RunState $ morph (mapStateT f) x
-- morph f (RunEither x g) =
--   RunEither (morph (mapEitherT f) x)
--     (\e => let (o,sf) = g e in (o, assert_total $ morph (mapEitherT f) sf))

--------------------------------------------------------------------------------
--          Single step evaluation
--------------------------------------------------------------------------------

export
step : Monad m => Sample i -> MSF m i o -> m (Sample o, MSF m i o)
step _ c@(Const x)  = pure (x, c)
step v Id           = pure (v, Id)
step v c@(Arr f)    = pure (f v, c)
step v c@(Lifted f) = (,c) <$> f v

step v (Seq sf1 sf2) = do
  (vx,sf1') <- step v  sf1
  (vo,sf2') <- step vx sf2
  pure (vo, Seq sf1' sf2')

step (v1,v2) (Par sf1 sf2)  = do
  (o1,sf1') <- step v1 sf1
  (o2,sf2') <- step v2 sf2
  pure ((o1,o2), Par sf1' sf2')

step v (Fan sf1 sf2)  = do
  (o1,sf1') <- step v sf1
  (o2,sf2') <- step v sf2
  pure ((o1,o2), Fan sf1' sf2')

step (Left i1) (Choice sf1 sf2)  = do
  (o1,sf1') <- step i1 sf1
  pure (Left o1, Choice sf1' sf2)

step (Right i2) (Choice sf1 sf2)  = do
  (o2,sf2') <- step i2 sf2
  pure (Right o2, Choice sf1 sf2')

step v (Loop s sf) = do
  ((o,s2), sf2) <- step (v,s) sf
  pure (o, Loop s2 sf2)

step (e,i) (RunReader sf) = do
  (o,sf2) <- runReaderT e (step i sf)
  pure (o, RunReader sf2)

step (s,i) (RunState sf) = do
  (s2,o,sf2) <- runStateT s (step i sf)
  pure ((s2,o), RunState sf2)

step i (RunEither sf f) = do
  Left e <- runEitherT (step i sf)
    | Right (o, sf2) => pure (o, RunEither sf2 f)
  let (o, sf2) = f e
  pure (o, RunEither sf2 f)
