module Rhone.Event

import Data.Colist
import Data.List
import Data.List1

import Rhone.Basic
import Rhone.Types

%default total

--------------------------------------------------------------------------------
--          Event Sources
--------------------------------------------------------------------------------

||| Event source that never occurs.
export
never : SF i (E o) Dec
never = Const Nothing

||| Event source with a single occurrence at time 0.
||| The value of the event is given by the function argument.
export
now : o -> SF i (E o) Dec
now v = Just v ==> never

||| Event source with consecutive occurrences at the given intervals.
||| Should more than one event be scheduled to occur in any sampling interval,
||| the output list will contain all events produced during that interval.
||| 
||| Guaranteed not to miss any events.
export
afterEachCat : Colist (TimeSpan, b) -> SF a (E $ List1 b) Dec
afterEachCat ps = mkSFDec go (const ps, Nothing)
  where go :  TimeSpan
           -> Colist (TimeSpan,b)
           -> (Sample a -> Colist (TimeSpan,b), Maybe $ List1 b)
        go _  []           = (const [], Nothing)
        go dt ((s,v) :: t) = 
          case dt.value `minus` s.value of
            k@(S _) =>
              let (f,m) = go (MkTimeSpan k ItIsSucc) t
               in (f, map (cons v) m <|> Just (singleton v))

            Z       =>
              case s.value `minus` dt.value of
                Z       => (\_ => t, Just $ singleton v)
                k@(S _) => (\_ => (MkTimeSpan k ItIsSucc, v) :: t, Nothing)


||| Event source with consecutive occurrences at the given intervals.
||| Should more than one event be scheduled to occur in any sampling interval,
||| only the first will in fact occur to avoid an event backlog.
export
afterEach : Colist (TimeSpan, b) -> SF a (E b) Dec
afterEach ps = afterEachCat ps >>> liftE head

||| Event source with a single occurrence at or as soon after
||| the given (local) time span as possible.
export
after : TimeSpan -> b -> SF a (E b) Dec
after dt v = afterEach [(dt,v)]

||| Event source with repeated occurrences with interval `dt`.
||| Note: If the interval is too short w.r.t. the sampling intervals,
||| the result will be that events occur at every sample. However, no more
||| than one event results from any sampling interval, thus avoiding an
||| "event backlog" should sampling become more frequent at some later
||| point in time.
export
repeatedly : TimeSpan -> b -> SF a (E b) Dec
repeatedly dt v = afterEach $ repeat (dt,v)

--------------------------------------------------------------------------------
--          Delayed Events
--------------------------------------------------------------------------------

-- State used for delaying events.
record DelaySt a where
  constructor MkDelaySt
  -- delay
  delay  : TimeSpan
  -- accumulated local time
  local  : Time
  -- event backlog
  events : List (Time,a)

delayNext : TimeSpan -> DelaySt a -> (Maybe a -> DelaySt a, Maybe $ List1 a)
delayNext dt (MkDelaySt delay local events) =
  let newLocal  = local `after` dt
      (es,rest) = span ((<= newLocal) . fst) events
      newEvents = maybe rest (\v => rest ++ [(newLocal `after` delay, v)])
   in (\m => MkDelaySt delay newLocal (newEvents m), fromList (map snd es))

initSt : TimeSpan -> Maybe a -> DelaySt a
initSt dt Nothing  = MkDelaySt dt 0 []
initSt dt (Just x) = MkDelaySt dt 0 [(0 `after` dt, x)]

export
delayCat : TimeSpan -> SF (E a) (E $ List1 a) Dec
delayCat dt = mkSFDec delayNext (\m => initSt dt m, Nothing)

export
delay : TimeSpan -> SF (E a) (E a) Dec
delay dt = delayCat dt >>> liftE head
