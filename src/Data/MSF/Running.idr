module Data.MSF.Running

import Control.Monad.Identity
import Data.MSF.Core

%default total

--------------------------------------------------------------------------------
--          Single step evaluation
--------------------------------------------------------------------------------

||| Single step evaluation of monadic stream functions.
||| This is used to drive a typical application using
||| MSFs for processing input.
export
step : Monad m => MSF m i o -> i -> m (o, MSF m i o)

par : Monad m => ParList m is os -> HList is -> m (HList os, ParList m is os)
par []          []          = pure ([],[])
par (sf :: sfs) (vi :: vis) = do
  (vo, sf2)   <- step    sf  vi
  (vos, sfs2) <- par sfs vis
  pure (vo :: vos, sf2 :: sfs2)

fan : Monad m => FanList m i os -> i -> m (HList os, FanList m i os)
fan []          _  = pure ([],[])
fan (sf :: sfs) vi = do
  (vo, sf2)   <- step    sf  vi
  (vos, sfs2) <- fan sfs vi
  pure (vo :: vos, sf2 :: sfs2)

choice : Monad m => ParList m is os -> HSum is -> m (HSum os, ParList m is os)
choice (sf :: sfs) (Here vi) = do
  (vo, sf2) <- step sf vi
  pure (Here vo, sf2 :: sfs)

choice (sf :: sfs) (There y) = do
  (vo, sfs2) <- choice sfs y
  pure (There vo, sf :: sfs2)

collect : Monad m => CollectList m is o -> HSum is -> m (o, CollectList m is o)
collect (sf :: sfs) (Here vi) = do
  (vo, sf2) <- step sf vi
  pure (vo, sf2 :: sfs)

collect (sf :: sfs) (There y) = do
  (vo, sfs2) <- collect sfs y
  pure (vo, sf :: sfs2)

step c@(Const x)  _ = pure (x, c)
step Id           v = pure (v, Id)
step c@(Arr f)    v = pure (f v, c)
step c@(Lifted f) v = (,c) <$> f v

step (Seq sf1 sf2) v = do
  (vx,sf1') <- step sf1 v
  (vo,sf2') <- step sf2 vx
  pure (vo, Seq sf1' sf2')

step (Par sfs) v = mapSnd Par <$> par sfs v

step (Fan sfs) v = mapSnd Fan <$> fan sfs v

step (Choice sfs) v = mapSnd Choice <$> choice sfs v

step (Collect sfs) v = mapSnd Collect <$> collect sfs v

step (Loop s sf) v = do
  ([s2,o], sf2) <- step sf [s,v]
  pure (o, Loop s2 sf2)

step (Switch sf f) i = do
  (Left e,_) <- step sf i
    | (Right o,sf2) => pure (o, Switch sf2 f)
  step (f e) i

--------------------------------------------------------------------------------
--          Running MSFs
--------------------------------------------------------------------------------

||| Uses the given MSF to process a list of input
||| values. This is useful for testing MSFs.
export
embed : Monad m => List i -> MSF m i o -> m (List o)
embed [] _          = pure []
embed (vi :: is) sf = do
  (vo,sf2) <- step sf vi
  os       <- embed is sf2
  pure $ vo :: os

||| `embed` using the `Identity` monad.
export
embedI : List i -> MSF Identity i o -> List o
embedI is = runIdentity . embed is

||| Calculates the size (number of constructors)
||| of a MSF. This is useful for testing and
||| possibly optimizing applications.
export
size : MSF m i o -> Nat

sizePar : ParList m is os -> Nat
sizePar [] = 0
sizePar (sf :: sfs) = size sf + sizePar sfs

sizeFan : FanList m i os -> Nat
sizeFan [] = 0
sizeFan (sf :: sfs) = size sf + sizeFan sfs

sizeCol : CollectList m is o -> Nat
sizeCol [] = 0
sizeCol (sf :: sfs) = size sf + sizeCol sfs

size Id            = 1
size (Const x)     = 1
size (Arr f)       = 1
size (Lifted f)    = 1
size (Seq x y)     = 1 + size x + size y
size (Par x)       = 1 + sizePar x
size (Fan x)       = 1 + sizeFan x
size (Choice x)    = 1 + sizePar x
size (Collect x)   = 1 + sizeCol x
size (Loop x y)    = 1 + size y
size (Switch x f)  = 1 + size x
