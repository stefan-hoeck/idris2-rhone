# UI Example 1 : Accumulating Button Clicks

In this example, I'll show how to set up an MSF for describing a
user interface with three buttons and a counter: One button
for increasing the counter, one for decreasing the counter,
and one for resetting the counter to zero. The buttons for
increasing and decreasing should be disabled once the counter gets too
small or too large. Likewise, the button for
resetting should be disabled if the counter is
at zero.

We'll define our own effect interface for this
allowing us to test the functionality of our MSF
in a pure environment.

```idris
module Docs.UIEx1

import Control.Monad.State
import Data.MSF
import Data.MSF.Trans
import Derive.Prelude

%language ElabReflection
%default total

interface Monad m => MonadUI m where
  disableInc   : Bool -> m ()
  disableDec   : Bool -> m ()
  disableReset : Bool -> m ()
  dispCount    : Int8 -> m ()
```

We assume that upon generating the widgets of the UI,
our program will register event handlers reacting on
certain button clicks. The events they'll fire will be
functions of type `Int8 -> Int8` used to modify
the application state.
We can now write the logic of our user interface:

```idris
Ev : Type
Ev = Int8 -> Int8

msf : MonadUI m => MSF m Ev ()
msf = accumulateWith apply 0 >>>
      fan_ [ arrM dispCount
           , (>= 10)    ^>> arrM disableInc
           , (<= (-10)) ^>> arrM disableDec
           , (== 0)     ^>> arrM disableReset
           ]
```

As you can see, accumulating the state is only a small
part. Most of the logic goes into adjusting the UI
to the updated state. The `fan_` function is convenient
for this.

For testing, we will use the state monad with a custom
record type for representing our user interface. Our state
will monitor for each button whether it is enabled or
not, as well as keep track of the content of an output field
or HTML element displaying the current counter:

```idris
record UI where
  constructor MkUI
  inc   : Bool
  dec   : Bool
  reset : Bool
  out   : String

ini : UI
ini = MkUI True True True ""

%runElab derive "UI" [Eq,Show]

MonadUI (State UI) where
  disableInc   b = modify { inc := not b }
  disableDec   b = modify { dec := not b }
  disableReset b = modify { reset := not b }
  dispCount    n = modify { out := #"Count: \#{show n}"# }
```

Finally, we use a data type for simulating user
interactions: An enum describing the button a user clicked:

```idris
data Input = Inc | Dec | Reset

%runElab derive "Input" [Eq,Show]
```

However, when we simulate the UI, we don't want to
have to keep track of whether every button click makes
sense at the current state. We assume the user interface
will not pass on a click on a disabled button, and we
use a pre-processing MSF to simulate this behavior.
Input valid at the current UI state will be converted
to an event the controlling MSF understands while
invalid input will be kept unmodified for logging
purposes:

```idris
onInput : MSF (State UI) Input (HSum [Ev,Input])
onInput = fan [get, id] >>> bool valid >>> choice [arr toFun, snd]
  where valid : HList [UI,Input] -> Bool
        valid [ui,Inc]   = ui.inc
        valid [ui,Dec]   = ui.dec
        valid [ui,Reset] = ui.reset

        toFun : HList [UI,Input] -> Int8 -> Int8
        toFun [_,Inc  ] = (+  1)
        toFun [_,Dec  ] = (+ -1)
        toFun [_,Reset] = const 0
```

Finally, putting everything together, we run a simulation
of the application. We provide a list of user actions,
collecting a string of the UI state after each action
accepted by the UI has been passed through the controlling
MSF, and a dummy string if the action was invalid:

```idris
simulate : List Input -> List String
simulate evs = evalState ini . embed evs
             $ onInput >>> collect
                 [ msf >>> get >>^ show
                 , arr $ \i => "Ignored invalid input: \{show i}"
                 ]

testUI : List String
testUI = simulate $  replicate 11 Inc
                  ++ replicate 2 Reset
                  ++ replicate 11 Dec
```

And at the REPL:

```repl
Docs.UIEx1> testUI
["MkUI { inc = True, dec = True, reset = True, out = "Count: 1" }",
 "MkUI { inc = True, dec = True, reset = True, out = "Count: 2" }",
 "MkUI { inc = True, dec = True, reset = True, out = "Count: 3" }",
 "MkUI { inc = True, dec = True, reset = True, out = "Count: 4" }",
 "MkUI { inc = True, dec = True, reset = True, out = "Count: 5" }",
 "MkUI { inc = True, dec = True, reset = True, out = "Count: 6" }",
 "MkUI { inc = True, dec = True, reset = True, out = "Count: 7" }",
 "MkUI { inc = True, dec = True, reset = True, out = "Count: 8" }",
 "MkUI { inc = True, dec = True, reset = True, out = "Count: 9" }",
 "MkUI { inc = False, dec = True, reset = True, out = "Count: 10" }",
 "Ignored invalid input: Inc",
 "MkUI { inc = True, dec = True, reset = False, out = "Count: 0" }",
 "Ignored invalid input: Reset",
 "MkUI { inc = True, dec = True, reset = True, out = "Count: -1" }",
 "MkUI { inc = True, dec = True, reset = True, out = "Count: -2" }",
 "MkUI { inc = True, dec = True, reset = True, out = "Count: -3" }",
 "MkUI { inc = True, dec = True, reset = True, out = "Count: -4" }",
 "MkUI { inc = True, dec = True, reset = True, out = "Count: -5" }",
 "MkUI { inc = True, dec = True, reset = True, out = "Count: -6" }",
 "MkUI { inc = True, dec = True, reset = True, out = "Count: -7" }",
 "MkUI { inc = True, dec = True, reset = True, out = "Count: -8" }",
 "MkUI { inc = True, dec = True, reset = True, out = "Count: -9" }",
 "MkUI { inc = True, dec = False, reset = True, out = "Count: -10" }",
 "Ignored invalid input: Dec"]
```

<!-- vi: filetype=idris2:syntax=markdown
-->
