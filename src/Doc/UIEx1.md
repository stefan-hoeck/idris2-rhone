## UI Example 1 : Accumulating Button Clicks

In this blog post, I describe how to set up
an MSF for describing a user interface with
three buttons and a counter: One button
for increasing the counter, one for decreasing
the counter, and one for resetting the counter
to zero. The buttons for increasing and decreasing
should be disabled once the counter gets to
small or too large. Likewise, the button for
resetting should be disabled if the counter is
at zero.

Here's a data type to describe the state of
the UI:

```idris
module Doc.UIEx1

import Control.Monad.State
import Data.MSF
import Generics.Derive

%language ElabReflection
%default total

record UI where
  constructor MkUI
  inc     : Bool
  dec     : Bool
  reset   : Bool
  out     : String

ini : UI
ini = MkUI True True True ""

%runElab derive "UI" [Generic,Meta,Eq,Show]
```

We simulate interacting with our user interface through
the `State` monad:

```idris
MonadUI : Type -> Type
MonadUI = State UI

disableInc : Bool -> MonadUI ()
disableInc b = modify $ record { inc = not b}

disableDec : Bool -> MonadUI ()
disableDec b = modify $ record { dec = not b}

disableReset : Bool -> MonadUI ()
disableReset b = modify $ record { reset = not b}

dispCount : Int8 -> MonadUI ()
dispCount n = modify $ record { out = #"Count: \#{show n}"#}
```

Finally, we use a data type to simulate UI events:

```idris
data Ev = Inc | Dec | Reset
```

However, we assume the user interface will not allow some
of these if the corresponding button is disabled. We therefore
use an initial MSF to simulate the correct behavior of
the UI, which will only pass on valid events:

```idris
convertEvent : MSF MonadUI Ev (Maybe (Int8 -> Int8))
convertEvent = fan [arrM (const get), id] >>> ifTrue valid (arr $ toFun . snd)
  where valid : NP I [UI,Ev] -> Bool
        valid [ui,Inc]   = ui.inc
        valid [ui,Dec]   = ui.dec
        valid [ui,Reset] = ui.reset

        toFun : Ev -> Int8 -> Int8
        toFun Inc   = (+1)
        toFun Dec   = (+ (-1))
        toFun Reset = const 0
```

We can now write the logic of our user interface:

```idris
msf : MSF MonadUI (Int8 -> Int8) ()
msf = accumulateWith apply 0 >>>
      fan_ [ arrM dispCount
           , (>= 10)    ^>> arrM disableInc
           , (<= (-10)) ^>> arrM disableDec
           , (== 0)     ^>> arrM disableReset
           ]
```

Finally, putting everything together, we run a simulation
of the application. We provide a list of user actions,
collecting a string of the UI state after each action
accepted by the UI, and an empty string if the action
was invalid:

```idris
simulate : List Ev -> List String
simulate evs = evalState ini . embed evs
             $   convertEvent
             >>> ifJust (msf >>> arrM (const get) >>^ show)
             >>^ fromMaybe ""
```
