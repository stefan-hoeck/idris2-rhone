module Rhone.Switch

import Rhone.Basic
import Rhone.Types

export
switch :  {c1,c2 : _}
       -> SF a (P b $ E c) c1
       -> (c -> SF a b c2)
       -> SF a b (c1 `and` c2)
switch sf f =
  RSwitch c1 c2 sf (\c => rewrite AndDec c2 in f c &&& Const Nothing)
