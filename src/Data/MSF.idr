module Data.MSF

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Rhone.Types

public export
data MSF : (m : Type -> Type) -> (is : SVDesc) -> (os : SVDesc) -> Type where
  Const     : Sample os -> MSF m is os
  Arr       : (Sample is -> Sample os) -> MSF m is os
  Lifted    : (Sample is -> m (Sample os)) -> MSF m is os
  Seq       : MSF m i x -> MSF m x o -> MSF m i o
  Par       : MSF m i1 o1 -> MSF m i2 o2 -> MSF m (P i1 i2) (P o1 o2)
  Fan       : MSF m i o1 -> MSF m i o2 -> MSF m i (P o1 o2)
  Loop      : (Sample s) -> MSF m (P i s) (P o s) -> MSF m i o
  RunReader : MSF (ReaderT e m) i o -> MSF m (P (C e) i) o
  RunState  : MSF (StateT s m) i o -> MSF m (P (C s) i) (P (C s) o)

export
step : Monad m => Sample i -> MSF m i o -> m (Sample o, MSF m i o)
step _ c@(Const x)  = pure (x, c)
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
