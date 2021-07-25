module Rhone.Event

import Rhone.Basic
import Rhone.Types

||| Event source that never occurs.
export
never : SF i (E o) Dec
never = Const Nothing

||| Event source with a single occurrence at time 0.
||| The value of the event is given by the function argument.
export
now : o -> SF i (E o) Dec
now v = Just v ==> never

-- public export
-- repeatedly : TimeSpan -> a -> SF i [E a] Dec
