module Data.MSF.Trans

import Control.Monad.Reader
import Control.Monad.State
import Data.MSF.Core
import Data.MSF.Util

export
get : MonadState s m => MSF m i s
get = constM get

export
put : MonadState s m => MSF m s ()
put = arrM put

export
modify : MonadState s m => MSF m (s -> s) ()
modify = arrM modify

export
ask : MonadReader e m => MSF m i e
ask = constM ask
