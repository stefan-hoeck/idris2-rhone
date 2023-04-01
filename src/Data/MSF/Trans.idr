||| Monad morphisms and interaction with monad transformer stacks.
module Data.MSF.Trans

import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.MSF.Core
import Data.MSF.Util
import Data.MSF.Running

--------------------------------------------------------------------------------
--          General Morphisms
--------------------------------------------------------------------------------

||| The most general structure-preserving monad morphism.
||| This can be used to change the input and output type plus
||| the effect type of an MSF without affecting its internal
||| structure (wiring of stream functions).
|||
||| For examples of usage, have a look at the implementations of
||| functions like `unreader`, `reader`, `unstate`, and similar.
export
morphGS :  Monad m1
        => (forall c . (i1 -> m1(o1,c)) -> i2 -> m2(o2,c))
        -> MSF m1 i1 o1
        -> MSF m2 i2 o2
morphGS f sf = feedback sf (arrM run >>^ \(o2,sf2) => [sf2,o2])
  where run : HList [MSF m1 i1 o1,i2] -> m2 (o2, MSF m1 i1 o1)
        run [sf1,vi2] = f (step sf1) vi2

||| Applies a monad morphism to change the context of an MSF.
|||
||| ```idris example
||| fromPure : Monad m => MSF Identity i o -> MSF m i o
||| fromPure = morph (pure . runIdentity)
||| ```
export
morph : Monad m1 => (forall c . m1 c -> m2 c) -> MSF m1 i1 o1 -> MSF m2 i1 o1
morph f = morphGS (f .)

--------------------------------------------------------------------------------
--          Identity
--------------------------------------------------------------------------------

||| Puts a pure MSF (over the `Identity` monad) in another
||| monadic context.
export
fromPure : Monad m => MSF Identity i o -> MSF m i o
fromPure = morph (pure . runIdentity)

--------------------------------------------------------------------------------
--          State
--------------------------------------------------------------------------------

||| Alias for `constM get`
export
get : MonadState s m => MSF m i s
get = constM get

||| Alias for `constM put`
export
put : MonadState s m => MSF m s ()
put = arrM put

||| Alias for `constM modify`
export
modify : MonadState s m => MSF m (s -> s) ()
modify = arrM modify

||| Converts an outer `StateT` wrapper to an MSF converting
||| an additional argument of the state type.
export
fromState : Monad m => MSF (StateT s m) i o -> MSF m (HList [s,i]) (HList [s,o])
fromState =
  morphGS (\f,[vs,vi] => (\(vs2,vo,vc) => ([vs2,vo],vc)) <$> runStateT vs (f vi))

||| Runs the given stateful MSF as a feedback loop with `ini` as the
||| initial input.
|||
||| This is a shorthand for `feedback ini . fromState`.
export
loopState : Monad m => (ini : s) -> MSF (StateT s m) i o -> MSF m i o
loopState ini = feedback ini . fromState

||| Like `fromState` but drops the uninteresting unit in- and output.
export
fromState_ : Monad m => MSF (StateT s m) () () -> MSF m s s
fromState_ = morphGS (\f,vs => (\(vs2,_,vc) => (vs2,vc)) <$> runStateT vs (f ()))

||| Converts a state transforming MSF to one with its monadic context
||| wrapped in `StateT s`.
export
toState : Monad m => MSF m (HList [s,i]) (HList [s,o]) -> MSF (StateT s m) i o
toState =
  morphGS (\f,vi => ST $ \vs => (\([vs2,vo],vc) => (vs2,vo,vc)) <$> f [vs,vi])

||| Like `toState` but for MSFs without additional in- or output
export
toState_ : Monad m => MSF m s s -> MSF (StateT s m) () ()
toState_ = morphGS (\f,_ => ST $ \vs => (\(vs2,vc) => (vs2,(),vc)) <$> f vs)

--------------------------------------------------------------------------------
--          Reader
--------------------------------------------------------------------------------

||| Alias for `constM ask`
export
ask : MonadReader e m => MSF m i e
ask = constM ask

||| Converts an outer `ReaderT` wrapper to an MSF taking an
||| an additional input.
export
fromReader : Monad m => MSF (ReaderT e m) i o -> MSF m (HList [e,i]) o
fromReader = morphGS (\f,[ve,vi] => runReaderT ve (f vi))

||| Converts the given MSF to use `env` as its environment.
|||
||| This is an alias for `fan [ const env, id ] >>> fromReader sf`.
export
withEnv : Monad m => (env : e) -> (sf : MSF (ReaderT e m) i o) -> MSF m i o
withEnv env sf = fan [ const env, id ] >>> fromReader sf

||| Like `unReader` but drops the uninteresting unit input.
export
fromReader_ : Monad m => MSF (ReaderT e m) () o -> MSF m e o
fromReader_ = morphGS (\f,ve => runReaderT ve (f ()))

||| Converts an MSF taking an additional input
||| to one with its monadic context wrapped in `ReaderT e`.
export
toReader : Monad m => MSF m (HList [e,i]) o -> MSF (ReaderT e m) i o
toReader = morphGS (\f,vi => MkReaderT $ \ve => f [ve,vi])

||| Like `toReader` but for MSFs without additional input
export
toReader_ : Monad m => MSF m e o -> MSF (ReaderT e m) () o
toReader_ = morphGS (\f,_ => MkReaderT f)

--------------------------------------------------------------------------------
--          Writer
--------------------------------------------------------------------------------


||| Alias for `arrM tell`
export
tell : MonadWriter w m => MSF m w ()
tell = arrM tell

||| Converts an outer `WriterT` wrapper to an MSF producing
||| an additional output.
export
fromWriter : Monoid w => Monad m => MSF (WriterT w m) i o -> MSF m i (HList [w,o])
fromWriter =
  morphGS (\f,vi => (\((vo,vc),vw) => ([vw,vo],vc)) <$> runWriterT (f vi))

||| Like `fromWriter` but ignores the uninteresting output.
export
fromWriter_ : Monoid w => Monad m => MSF (WriterT w m) i () -> MSF m i w
fromWriter_ =
  morphGS (\f,vi => (\((_,vc),vw) => (vw,vc)) <$> runWriterT (f vi))

||| Converts an MSF producing an additional output
||| to one with its monadic context wrapped in `WriterT w`.
export
toWriter : Monoid w => Monad m => MSF m i (HList [w,o]) -> MSF (WriterT w m) i o
toWriter =
  morphGS (\f,vi =>
    MkWriterT $ \vw => (\([vw2,vo],vc) => ((vo,vc),vw <+> vw2)) <$> f vi)

||| Like `toWriter` but produces unit as output.
export
toWriter_ : Monoid w => Monad m => MSF m i w -> MSF (WriterT w m) i ()
toWriter_ =
  morphGS (\f,vi =>
    MkWriterT $ \vw => (\(vw2,vc) => (((),vc),vw <+> vw2)) <$> f vi)
