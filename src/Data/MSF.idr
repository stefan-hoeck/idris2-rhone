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

||| Calculates the type of a value representing a signal vector
public export
Sample : SVDesc -> Type
Sample (E x)   = Maybe x
Sample (C x)   = x
Sample (S x)   = x
Sample (P x y) = (Sample x, Sample y)

public export
data MSF : (m : Type -> Type) -> (i : SVDesc) -> (o : SVDesc) -> Type where
  Id        :  MSF m i i
  Const     :  Sample o -> MSF m i o
  Arr       :  (Sample i -> Sample o) -> MSF m i o
  Lifted    :  (Sample i -> m (Sample o)) -> MSF m i o
  Seq       :  MSF m i x -> MSF m x o -> MSF m i o
  Par       :  MSF m i1 o1 -> MSF m i2 o2 -> MSF m (P i1 i2) (P o1 o2)
  Fan       :  MSF m i o1 -> MSF m i o2 -> MSF m i (P o1 o2)
  Loop      :  (Sample s) -> MSF m (P i s) (P o s) -> MSF m i o
  RunReader :  MSF (ReaderT e m) i o -> MSF m (P (C e) i) o
  RunState  :  MSF (StateT s m) i o -> MSF m (P (C s) i) (P (C s) o)
  RunEither :  MSF (EitherT e m) i o
            -> (e -> (Sample o, MSF (EitherT e m) i o))
            -> MSF m i o

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

export
morph : (f : forall c . m1 c -> m2 c) -> MSF m1 i o -> MSF m2 i o
morph f Id              = Id
morph f (Const x)       = Const x
morph f (Arr g)         = Arr g
morph f (Lifted g)      = Lifted $ f . g
morph f (Seq x y)       = Seq (morph f x) (morph f y)
morph f (Par x y)       = Par (morph f x) (morph f y)
morph f (Fan x y)       = Fan (morph f x) (morph f y)
morph f (Loop x y)      = Loop x (morph f y)
morph f (RunReader x)   = RunReader $ morph (mapReaderT f) x
morph f (RunState x)    = RunState $ morph (mapStateT f) x
morph f (RunEither x g) =
  RunEither (morph (mapEitherT f) x)
    (\e => let (o,sf) = g e in (o,?bar)) --(o, morph (mapEitherT f) sf))

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

