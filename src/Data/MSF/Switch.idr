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
import Data.MSF.Util
import Data.SOP

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
switch :  MSF m i (NP I [o, Event e])
       -> (e -> MSF m i o)
       -> MSF m i o
switch sf = switchE $ sf >>^ (\[vo,ve] => event (Right vo) Left ve)

--------------------------------------------------------------------------------
--          Delayed Switches
--------------------------------------------------------------------------------

rswUtil : NP I [o,Event x] -> Either (x,o) o
rswUtil [vo,Ev vx] = Left (vx,vo)
rswUtil [vo,NoEv]  = Right vo

||| Produces output of the given MSF until it fires an event,
||| in which case a new MSF is created,
||| which will be used in all further evaluation steps.
|||
||| This uses `dSwitchE` internally, so all restrictions mentioned
||| there apply.
export
dSwitch : MSF m i (NP I [o, Event e]) -> (e -> MSF m i o) -> MSF m i o
dSwitch sf = switch (sf >>> par [id, iPre NoEv])

--------------------------------------------------------------------------------
--          Recurring Switches
--------------------------------------------------------------------------------

export %inline
drSwitch : MSF m i o -> MSF m (NP I [i, Event $ MSF m i o]) o
drSwitch = DRSwitch

||| Produces output of the first MSF until the second
||| fires an event, in which case a new MSF is created,
||| which will be used in all futre evaluation cycles.
export
drswitchWhen :  MSF m i o
             -> MSF m i (Event e)
             -> (e -> MSF m i o)
             -> MSF m i o
drswitchWhen ini es f = fan [id, es >>^ map f] >>> drSwitch ini
