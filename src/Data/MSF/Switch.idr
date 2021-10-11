module Data.MSF.Switch

import Data.MSF.Core
import Data.MSF.Event
import Data.MSF.Util
import Data.SOP

%default total

||| Produces output of the first MSF until it produces
||| a `Left`, in which case the event will be used to
||| create a new MSF, which will be immediately evaluated
||| and used henceforth.
export %inline
switchE : MSF m i (Either e o) -> (e -> MSF m i o) -> MSF m i o
switchE = Switch

||| Produces output of the first MSF until the second
||| fires an event, in which case a new MSF is created,
||| which will evaluated immediately and used henceforth.
export
switchWhen :  MSF m i o
           -> MSF m i (Event e)
           -> (e -> MSF m i o)
           -> MSF m i o
switchWhen sf ev =
  switchE $ fan [sf, ev] >>^ (\[vo,ve] => event (Right vo) Left ve)
  
||| Produces output of the first MSF until it returns a
||| `Left`, in which case a new MSF will be created and
||| used for processing all future input values.
export %inline
dswitch : MSF m i (Either (e,o) o) -> Inf (e -> MSF m i o) -> MSF m i o
dswitch = DSwitch
