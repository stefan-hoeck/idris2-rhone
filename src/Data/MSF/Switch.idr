||| Switching Combinators
|||
||| Switches allow us to dynamically change the structure
||| (wiring) of a running network of stream functions.
||| Semantically, the react on discrete events, but
||| some of the switching primitives in this module use
||| the `Either` data type if it allows us to more exactly
||| describe the semantics of a switch.
module Data.MSF.Switch

import Data.MSF.Core
import Data.MSF.Event
import Data.MSF.Running
import Data.MSF.Util

%default total

--------------------------------------------------------------------------------
--          Immediate Switches
--------------------------------------------------------------------------------

||| Produces output of the first MSF until it produces
||| a `Left`, in which case the event will be used to
||| create a new MSF, which will be immediately evaluated
||| and used henceforth.
|||
||| This is a one-time switch, which is often used to
||| run an MSF a fixed number of times or until a certain
||| event occurs, after which the replacement will be used.
|||
||| Note: It is unsafe to use this in a recursive setting,
|||       as it would allow us to create an infinite loop
|||       of streaming functions, all of which return `Left`s
|||       forever. Luckily, the totality checker will prevent us
|||       from doing this.
export %inline
switchE : MSF m i (Either e o) -> (e -> MSF m i o) -> MSF m i o
switchE = Switch

||| Produces output of the given MSF until it fires an event,
||| in which case a new MSF is created,
||| which will be evaluated immediately and used henceforth.
|||
||| This uses `switchE` internally, so all restrictions mentioned
||| there apply.
export
switch :
     MSF m i (HList [o, Event e])
  -> (e -> MSF m i o)
  -> MSF m i o
switch sf = switchE $ sf >>^ (\[vo,ve] => event (Right vo) Left ve)

--------------------------------------------------------------------------------
--          Delayed Switches
--------------------------------------------------------------------------------

rswUtil : HList [o,Event x] -> Either (x,o) o
rswUtil [vo,Ev vx] = Left (vx,vo)
rswUtil [vo,NoEv]  = Right vo

||| Produces output of the given MSF until it fires an event,
||| in which case a new MSF is created,
||| which will be used in all further evaluation steps.
export
dSwitch : MSF m i (HList [o, Event e]) -> (e -> MSF m i o) -> MSF m i o
dSwitch sf = switch (sf >>> par [id, iPre NoEv])

--------------------------------------------------------------------------------
--          Recurring Switches
--------------------------------------------------------------------------------

export %inline
rSwitch : Monad m => MSF m i o -> MSF m (HList [Event $ MSF m i o,i]) o
rSwitch sf =
  feedback sf . arrM $
    \[sf,[ev,vi]] => do
      (vo,sf2) <- step (fromEvent sf ev) vi
      pure [sf2,vo]

export %inline
drSwitch : Monad m => MSF m i o -> MSF m (HList [Event $ MSF m i o,i]) o
drSwitch sf =
  feedback sf . arrM $
    \[sf,[ev,vi]] => do
      (vo,sf2) <- step sf vi
      pure [fromEvent sf2 ev,vo]

||| Produces output of the first MSF until the second
||| fires an event, in which case a new MSF is created,
||| which will be used in all futre evaluation cycles.
export
drswitchWhen :
     {auto _ : Monad m}
  -> MSF m i o
  -> MSF m i (Event e)
  -> (e -> MSF m i o)
  -> MSF m i o
drswitchWhen ini es f = fan [es >>^ map f,id] >>> drSwitch ini
