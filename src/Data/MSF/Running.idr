module Data.MSF.Running

import Control.Monad.Identity
import Data.IORef
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
--          Testing MSFs
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

--------------------------------------------------------------------------------
--          Handler
--------------------------------------------------------------------------------

||| An event handler typically used as an auto-implicit argument
public export
record Handler (m : Type -> Type) (e : Type) where
  [noHints]
  constructor H
  handle_ : e -> m ()

export %inline
handle : {auto h : Handler m e} -> e -> m ()
handle = h.handle_

--------------------------------------------------------------------------------
--          Running MSFs
--------------------------------------------------------------------------------

-- initialEvent: If `Just e`, evaluate the given `MSF` once with `e` to
-- properly initialize all components.
-- idPrefix: prefix for uniqe ids
reactimate_ :
     HasIO m
  => (initialEvent : Maybe e)
  -> (mkMSF        : Handler m e -> m (MSF m e (), m ()))
  -> m (m ())
reactimate_ ie mkMSF = do
  -- Here we will put the proper event handler once everyting
  -- is ready. This is not Haskell, so we can't define
  -- the handler lazily and satisfy the totality checker at
  -- the same time. We therefore initialize the mutable reference
  -- with a dummy.
  hRef    <- newIORef {a = e -> m ()} (const $ pure ())

  -- our event handler
  let h := H (\ve => readIORef hRef >>= \h => h ve)

  (sf,cl) <- mkMSF h

  -- the current application state consists of the current
  -- monadic stream function, which will be stored in a
  -- mutable ref
  sfRef   <- newIORef sf

  -- we can now implement the *real* event handler:
  -- when an event is being fired, we evaluate the current
  -- MSF and put the resulting continuation in the mutable ref
  -- to be used when the next event occurs.
  let realHandler : e -> m ()
      realHandler = \ev => do
        sf1      <- readIORef sfRef
        (_, sf2) <- step sf1 ev
        writeIORef sfRef sf2

  -- we need to register the correct event handler, otherwise
  -- nothing will run
  writeIORef hRef handle

  -- finally, fire the initial event (if any)
  traverse_ h.handle_ ie

  pure cl

||| Create a monadic stream function (the reactive behavior
||| of an UI, for instance)
||| by passing the given generation function `sf` an event handler
||| that can be registered at reactive components.
||| The MSF will then be invoked and
||| evaluated whenever an event is fired.
export %inline
reactimate : HasIO m => (Handler m e -> m (MSF m e (), m ())) -> m (m ())
reactimate = reactimate_ Nothing

||| Like `reactimate`, but evaluates the `MSF` once at the beginning by
||| passing it the given initial event.
export
reactimateIni : HasIO m => e -> (Handler m e -> m (MSF m e (), m ())) -> m (m ())
reactimateIni = reactimate_ . Just
