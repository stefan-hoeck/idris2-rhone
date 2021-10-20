||| This module can be used to run an SF for a long time
||| as quickly as possible to check for memory leaks.
module Test.Leak

import Control.ANSI.CSI
import Control.Monad.Identity
import Control.Monad.Reader
import Control.MonadRec
import Data.Fuel
import Data.Iterable
import Data.MSF
import Data.MSF.Running
import Data.MSF.Switch
import Data.MSF.Trans
import Data.String

%default total

DTime : Type
DTime = Double

SF : Type -> Type -> Type
SF = MSF (ReaderT DTime Identity)

Velocity : Type
Velocity = Double

Acceleration : Type
Acceleration = Double

integralFrom : (v0 : Double) -> SF Double Double
integralFrom v0 = fan [id, iPre v0, ask] >>> accumulateWith next 0
  where next : NP I [Double,Double,DTime] -> Double -> Double
        next [new,old,dt] acc = acc + (dt / 2 * (new + old))

acc : Acceleration
acc = -9.81

velocity : (v0 : Velocity) -> (a0 : Acceleration) -> SF Acceleration Velocity
velocity v0 a0 = integralFrom a0 >>^ (+ v0)

position : (p0 : Double) -> (v0 : Velocity) -> SF Velocity Double
position p0 v0 = integralFrom v0 >>^ (+ p0)

record Ball where
  constructor MkBall
  pos : Double
  vel : Velocity

dispBall : NP I [Ball,Nat] -> String
dispBall [b,n] = 
  let char = if b.vel <= 0 then '<' else '>'
   in    cursorUp1
      ++ eraseLine End
      ++ padLeft 9 ' ' (show n)
      ++ replicate (cast b.pos) char

ballFrom : Ball -> SF i Ball
ballFrom (MkBall p0 v0) =
      const acc
  >>> velocity v0 acc
  >>> fan [position p0 v0, id]
  >>^ \[p,v] => MkBall p v

bounce : Ball -> Event (SF i Ball)
bounce (MkBall y vy) =
  if y <= 0 then Ev . ballFrom $ MkBall y (-vy) else NoEv

ballGame : Ball -> SF i Ball
ballGame b0 = feedback NoEv $ rSwitch (ballFrom b0) >>> fan [arr bounce, id]

game : MSF Identity () Ball
game = const 0.0001 >>> unreader_ (ballGame $ MkBall 80 0)

controller : MSF IO () ()
controller = morph (pure . runIdentity) (fan [game,count]) >>! putStrLn . dispBall

run : Fuel -> IO ()
run f = iterM (\_,sf => snd <$> step sf ()) (const ()) controller f

partial
main : IO ()
main = run forever
