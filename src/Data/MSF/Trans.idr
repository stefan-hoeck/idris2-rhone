module Data.MSF.Trans

import Control.Monad.Reader
import Control.Monad.State
import Data.MSF.Core
import Data.MSF.Util
import Data.MSF.Running
import Data.SOP

--------------------------------------------------------------------------------
--          General Morphisms
--------------------------------------------------------------------------------

export
morphGS :  Monad m1
        => (forall c . (i1 -> m1(o1,c)) -> i2 -> m2(o2,c))
        -> MSF m1 i1 o1
        -> MSF m2 i2 o2
morphGS f sf = feedback sf (arrM run >>^ \(o2,sf2) => [sf2,o2])
  where run : NP I [MSF m1 i1 o1,i2] -> m2 (o2, MSF m1 i1 o1)
        run [sf1,vi2] = f (step sf1) vi2

export
morph : Monad m1 => (forall c . m1 c -> m2 c) -> MSF m1 i1 o1 -> MSF m2 i1 o1
morph f = morphGS (f .)

--------------------------------------------------------------------------------
--          State
--------------------------------------------------------------------------------

export
get : MonadState s m => MSF m i s
get = constM get

export
put : MonadState s m => MSF m s ()
put = arrM put

export
modify : MonadState s m => MSF m (s -> s) ()
modify = arrM modify

--------------------------------------------------------------------------------
--          Reader
--------------------------------------------------------------------------------

export
ask : MonadReader e m => MSF m i e
ask = constM ask

export
unreader : Monad m => MSF (ReaderT e m) i o -> MSF m (NP I [e,i]) o
unreader = morphGS (\f,[ve,vi] => runReaderT ve (f vi))

export
unreader_ : Monad m => MSF (ReaderT e m) () o -> MSF m e o
unreader_ = morphGS (\f,ve => runReaderT ve (f ()))
