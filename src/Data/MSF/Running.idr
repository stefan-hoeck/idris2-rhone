module Data.MSF.Running

import Control.Monad.Identity
import Data.MSF.Core
import Data.SOP

--------------------------------------------------------------------------------
--          Single step evaluation
--------------------------------------------------------------------------------

mutual
  export
  stepPar :  Monad m
          => MSFList m is os
          -> NP I is
          -> m (NP I os, MSFList m is os)
  stepPar []          []          = pure ([],[])
  stepPar (sf :: sfs) (vi :: vis) = do
    (vo, sf2)   <- step    sf  vi
    (vos, sfs2) <- stepPar sfs vis
    pure (vo :: vos, sf2 :: sfs2)

  export
  stepFan :  Monad m
          => FanList m i os
          -> i
          -> m (NP I os, FanList m i os)
  stepFan []          _  = pure ([],[])
  stepFan (sf :: sfs) vi = do
    (vo, sf2)   <- step    sf  vi
    (vos, sfs2) <- stepFan sfs vi
    pure (vo :: vos, sf2 :: sfs2)

  export
  stepChoice :  Monad m
             => MSFList m is os
             -> NS I is
             -> m (NS I os, MSFList m is os)
  stepChoice (sf :: sfs) (Z vi) = do
    (vo, sf2) <- step sf vi
    pure (Z vo, sf2 :: sfs)

  stepChoice (sf :: sfs) (S y) = do
    (vo, sfs2) <- stepChoice sfs y
    pure (S vo, sf :: sfs2)

  export
  stepCollect :  Monad m
              => CollectList m is o
              -> NS I is
              -> m (o, CollectList m is o)
  stepCollect (sf :: sfs) (Z vi) = do
    (vo, sf2) <- step sf vi
    pure (vo, sf2 :: sfs)

  stepCollect (sf :: sfs) (S y) = do
    (vo, sfs2) <- stepCollect sfs y
    pure (vo, sf :: sfs2)

  export
  step : Monad m => MSF m i o -> i -> m (o, MSF m i o)
  step c@(Const x)  _ = pure (x, c)
  step Id           v = pure (v, Id)
  step c@(Arr f)    v = pure (f v, c)
  step c@(Lifted f) v = (,c) <$> f v

  step (Seq sf1 sf2) v = do
    (vx,sf1') <- step sf1 v
    (vo,sf2') <- step sf2 vx
    pure (vo, Seq sf1' sf2')

  step (Par sfs) v = mapSnd Par <$> stepPar sfs v

  step (Fan sfs) v = mapSnd Fan <$> stepFan sfs v

  step (Choice sfs) v = mapSnd Choice <$> stepChoice sfs v

  step (Collect sfs) v = mapSnd Collect <$> stepCollect sfs v

  step (Loop s sf) v = do
    ([s2,o], sf2) <- step sf [s,v]
    pure (o, Loop s2 sf2)
  
  step (Morph f msf) v = do
    (o, msf2) <- f (step msf) v
    pure (o, Morph f msf2)

  step (Switch sf f) i = do
    (Left e,_) <- step sf i
      | (Right o,sf2) => pure (o, Switch sf2 f)
    step (f e) i
  
  step (DSwitch sf f) i = do
    (Left(e, o),_) <- step sf i
      | (Right o,sf2) => pure (o, DSwitch sf2 f)
    pure (o, f e)
  
  step (Freeze sf) i = do
    (o,sf2) <- step sf i
    pure ([sf2,o], Freeze sf2)

--------------------------------------------------------------------------------
--          Running MSFs
--------------------------------------------------------------------------------

export
embed : Monad m => List i -> MSF m i o -> m (List o)
embed [] _          = pure []
embed (vi :: is) sf = do
  (vo,sf2) <- step sf vi
  os       <- embed is sf2
  pure $ vo :: os

export
embedI : List i -> MSF Identity i o -> List o
embedI is = runIdentity . embed is
