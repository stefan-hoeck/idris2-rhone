module Data.MSF.Trans

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.MSF.Core
import Data.SOP

%default total

--------------------------------------------------------------------------------
--          Monad Morphisms
--------------------------------------------------------------------------------

export %inline
morph : Monad m1 => (f : forall c . m1 c -> m2 c) -> MSF m1 i o -> MSF m2 i o
morph f = Morph (f .)

export %inline
morphGS :  Monad m1
        => (forall c . (a1 -> m1 (b1, c)) -> (a2 -> m2 (b2, c)))
        -> MSF m1 a1 b1
        -> MSF m2 a2 b2
morphGS = Morph

--------------------------------------------------------------------------------
--          Reader
--------------------------------------------------------------------------------

||| Yields the current environment
export %inline
ask : MonadReader e m => MSF m i e
ask = constM ask

||| Runs a function over the current environment
export %inline
asks : MonadReader e m => (e -> o) -> MSF m i o
asks = constM . asks

export
unReader : Monad m => MSF (ReaderT e m) i o -> MSF m (NP I [e,i]) o
unReader = morphGS (\f,[ve,vi] => runReaderT ve (f vi))

export
withReader : Monad m => MSF m (NP I [e,i]) o -> MSF (ReaderT e m) i o
withReader = morphGS (\f,vi => MkReaderT $ \ve => f [ve,vi])

--------------------------------------------------------------------------------
--          State
--------------------------------------------------------------------------------

||| Yiels the current state
export %inline
get : MonadState s m => MSF m i s
get = constM get

||| Applies the current state to a function
export %inline
gets : MonadState s m => (s -> o) -> MSF m i o
gets = constM . gets

||| Overwrites the state with the input
export %inline
put : MonadState s m => MSF m s ()
put = arrM put

||| Modifies the state with the input function
export %inline
modify : MonadState s m => MSF m (s -> s) ()
modify = arrM modify

||| Uses the given function to calculate the ouput
||| and a new state from the current state
export %inline
state : MonadState s m => (s -> (s,o)) -> MSF m i o
state = constM . state

export
unState : Monad m => MSF (StateT s m) i o -> MSF m (s,i) (s,o)
unState =
  morphGS (\f,(vs,vi) => (\(x,y,z) => ((x,y),z)) <$> runStateT vs (f vi))

export
withState : Monad m => MSF m (s,i) (s,o) -> MSF (StateT s m) i o
withState =
  morphGS (\f,vi => ST $ \vs => (\((x,y),z) => (x,y,z)) <$> f (vs,vi))

--------------------------------------------------------------------------------
--          Writer
--------------------------------------------------------------------------------

export
tell : MonadWriter w m => MSF m w ()
tell = arrM tell

export
writer : MonadWriter w m => MSF m (NP I [a,w]) a
writer = arrM $ \[va,vm] => writer (va,vm)

export
unWriter : Monoid w => Monad m => MSF (WriterT w m) i o -> MSF m i (o,w)
unWriter = morphGS (\f,vi => (\((x,y),z) => ((x,z),y)) <$> runWriterT (f vi))

export
withWriter : Semigroup w => Monad m => MSF m i (o,w) -> MSF (WriterT w m) i o
withWriter =
  morphGS (\f,vi => MkWriterT $ \vw => (\((a,b),c) => ((a,c),vw <+> b)) <$> f vi)
