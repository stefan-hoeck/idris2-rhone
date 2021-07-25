module Rhone.EventS

import Rhone.Event
import Rhone.Types

-- ||| Event source that never occurs.
-- public export
-- never : SF i [E a] Dec
-- never = Const [NoEvent]
-- 
-- ||| Event source with a single occurrence at time 0.
-- ||| The value of the event is given by the function argument.
-- public export
-- now : a -> SF i [E a] Dec
-- 
-- public export
-- repeatedly : TimeSpan -> a -> SF i [E a] Dec
