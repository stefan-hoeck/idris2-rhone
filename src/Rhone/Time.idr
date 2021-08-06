module Rhone.Time

import Data.MSF

--------------------------------------------------------------------------------
--          Time Domains
--------------------------------------------------------------------------------

public export
record TimeDomain time diff where
  constructor MkTimeDomain
  diffTime : time -> time -> diff

public export %inline
numTime : Neg n => TimeDomain n n
numTime = MkTimeDomain (-)

public export %hint
doubleTime : TimeDomain Double Double
doubleTime = numTime

public export %hint
integerTime : TimeDomain Integer Integer
integerTime = numTime

public export %hint
unitTime : TimeDomain () ()
unitTime = MkTimeDomain $ \_,_ => ()

--------------------------------------------------------------------------------
--          Clocks
--------------------------------------------------------------------------------

public export
RunningClock : (m : Type -> Type) -> (time : Type) -> (tag : Type) -> Type
RunningClock m time tag = MSF m () (time,tag)

public export
RunningClockInit : (m : Type -> Type) -> (time : Type) -> (tag : Type) -> Type
RunningClockInit m time tag = m (RunningClock m time tag, time)

public export
record Clock where
  constructor MkClock
  0 m        : Type -> Type
  0 time     : Type
  0 diff     : Type
  0 tag      : Type
  0 settings : Type
  domain     : TimeDomain time diff
  init       : settings -> RunningClockInit m time tag

public export
record TimeInfo (clock : Clock) where
  constructor MkTimeInfo
  sinceLast : clock.diff
  sinceInit : clock.diff
  absolute  : clock.time
  tag       : clock.tag
