## UI Input Validation

In this tutorial, we are going to have a go at
input validation in a graphical user interface.
We will soon see that if we want to be thorough about
this (and we should!), this is by no means trivial,
so be prepared for a lengthier post.

```idris
module Doc.UIEx2

import Control.Applicative.Syntax
import Control.Monad.Identity
import Control.Monad.Writer
import Data.Either
import Data.List
import Data.MSF
import Data.Maybe
import Data.So

%default total
```

### Specification of the UI

Our user interface will consist of a web form with
three text fields
where users have to enter an alias to be used
for logging in, their real name, and their age.
Whenever we allow users to freely enter some
text in a UI, this text *must* be properly
validated as soon as possible. To make sure we
don't forget to do that, we define custom
refinement types carrying the validation
results as erased proofs. At runtime, Idris
will optimize away these record wrappers.

```idris
-- An alias may consist only of lowercase characters
validAlias : String -> Bool
validAlias s =
  let len = length s
   in len > 0 && len <= 10 && all isLower (unpack s)

record Alias where
  constructor MkAlias
  value : String
  0 prf : So (validAlias value)

isPrintable : Char -> Bool
isPrintable ' ' = True
isPrintable c   = not (isControl c) && not (isSpace c)

-- A name may consist only of printable characters
validName : String -> Bool
validName s =
  let len = length s
   in len > 0 && len <= 50 && all isPrintable (unpack s)

record Name where
  constructor MkName
  value : String
  0 prf : So (validName value)

record Age where
  constructor MkAge
  value : Bits8
  0 prf : So (18 <= value && value <= 130)
```

There are several ways to go about input validation
in a UI. For instance, we plan to have a *submit* button,
which will send a request to our server if all text
fields have been correctly filled out. We could therefore
validate all input each time the button is clicked. Many
web forms in the browser work like that.

Personally, I don't like this approach. It's inconvenient
to go over a form of many fields several times just because
every time I click *submit* the application finds another
error I made. Input validation should be as interactive
as possible: Whenever users change the content of a text field,
they should get immediate feedback about the validity
of their input unless this would render the UI unusable,
for instance because validation reqests need to be sent
to the server.

We'd also like to be as friendly as possible. When
the page is being loaded, all text fields should be
empty and therefore invalid (we could fill them with
valid default values to start with, but that would make
it too risky for users to forget to enter some crucial piece
of information and end up with the default instead).
It would not be very kind to start shouting at them
about their invalid input before they even entered a
single character. We will therefore distinguish between
empty input fields, in which case we will print a
friendly reminder that some input is required,
and a non-empty field with invalid content, in which
case we might choose to give the text field a red
border and some tooltip hint about why the input is
invalid. We use a custom error type to
encapsulate the two forms of invalidity:

```idris
data Invalid = InputRequired | Msg String

namespace Invalid
  export
  print : Either Invalid a -> String
  print (Right _)            = "valid"
  print (Left $ Msg s)       = s
  print (Left InputRequired) = "req. input"
```

In addition to the three text fields, the UI should
also have a *submit* button. This should be disabled
if at least one of the text fields contains invalid
data. Otherwise, it should be enabled, and clicking
it should result in a request with data for creating
a new account being sent to the server:

```idris
record Account where
  constructor MkAccount
  alias : Alias
  name  : Name
  age   : Age

namespace Account
  export
  print : Account -> String
  print (MkAccount a n g) = #"{\#{a.value}, \#{n.value}, \#{show g.value}}"#
```

We also need to specify the type of input events
our controlling MSF will accept:

```idris
data Field = FAlias | FName | FAge

namespace Field
  export
  print : Field -> String
  print FAge   = "age"
  print FName  = "name"
  print FAlias = "alias"

data Ev = Submit | Input Field String

isSubmit : Ev -> Bool
isSubmit Submit = True
isSubmit _      = False

inputFor : Field -> Ev -> Event String
inputFor FAge   (Input FAge s)   = Ev s
inputFor FName  (Input FName s)  = Ev s
inputFor FAlias (Input FAlias s) = Ev s
inputFor _      _                = NoEv

namespace Ev
  export
  print : Ev -> String
  print Submit      = "Submit"
  print (Input f s) = #"Input \#{print f} \#{show s}"#
```

### Setting up a Testing Environment

As in the [previous post](UIEx1.md), we define a custom monad for
interacting with the UI:

```idris
interface Monad m => MonadUI m where
  enableSubmit  : Bool    -> m ()
  submit        : Account -> m ()
  validity      : Field   -> Either Invalid t -> m ()
```

For testing, we use the `Writer` monad for logging all
communication from the controller to the UI.

```idris
printCommands : List String -> String
printCommands = concat . intersperse ", "

Monad m => MonadUI (WriterT (List String) m) where
  enableSubmit True  = tell [ "enable submit" ]
  enableSubmit False = tell [ "disable submit" ]
  validity f v       = tell [ #"\#{print f}: \#{print v}"# ]
  submit acc         = tell [ #"submit: \#{print acc}"# ]
```

In order to get one line of logging output for each input
event, we traverse over the list of loggings using
`putStrLn`.

```idris
simulate : MSF (Writer (List String)) Ev () -> List Ev -> IO ()
simulate sf es = traverse_ (putStrLn . printCommands)
               $ embedI es (unWriter_ sf)
```

Note also the call to `Data.MSF.Trans.unWriter_`. For certain
monad transformers like `Reader`, `Writer`, or `State`,
MSFs make it very easy to break out of the outer monadic
context without affecting the inner structure (wiring) of the MSF.
An `MSF (WriterT w m) i o`, for instance, is isomorphic to
an `MSF m i (o,w)`. `Data.MSF.Trans` provides the necessary
conversion utilities.

In the example above, `unWriter_ sf`
has type `MSF Identity Ev (List String)`, so we will on
each evaluation step get a list with the logged commands
as a result.

### First Try: Validating an MSF directly

Let's give our web application a first try. Since
all refinemend types are of the same structure, we can use
a pretty general function for validating string input.

```idris
validate :  {f : a -> Bool}
         -> Cast String a
         => (fld : Field)
         -> (mk : (v : a) -> (0 prf : So (f v)) -> b)
         -> String
         -> Either Invalid b
validate fld mk s =
  let va  = cast {to = a} s
      msg = #"Invalid \#{print fld}: \#{s}"#
   in case choose (f va) of
        Left oh => Right $ mk va oh
        Right _ => Left $ if s == "" then InputRequired else Msg msg
```

Likewise, the MSF for reading and validating a single text
field is pretty general. Note that the events fired will already
include the new text content of the field in question, so
we don't have to look this up in the UI first:

```idris
input1 :  {f : a -> Bool}
       -> MonadUI m
       => Cast String a
       => (fld : Field)
       -> (mk : (v : a) -> (0 prf : So (f v)) -> b)
       -> MSF m Ev (Maybe b)
input1 fld mk =   inputFor fld
              ^>> hold ""
              >>> validate fld mk
              ^>> withEffect (validity fld)
              >>^ getRight
```

Let's break this down a bit: `inputFor` produces a
string event stream (`MSF m Ev (Event String)`), `hold ""`
converts this to a MSF with initial value `""`,
the value of which changes whenever
an input event for the given field is fired,
`withEffect (validity fld)` will update the UI with the
current validity information for the given field
and `Data.Either.getRight` converts the `Either String a`
to a `Maybe a`.

We can combine the MSFs for the three text fields to an `Account`
value using `MSF`'s applicative functor. Since all of them
are wrapped in a `Maybe`, we have a nesting of applicatives and
can make use of the operators from `Control.Applicative.Syntax`.

```idris
account1 : MonadUI m => MSF m Ev (Maybe Account)
account1 =    MkAccount
         <$$> input1 FAlias MkAlias
         <**> input1 FName  MkName
         <**> input1 FAge   MkAge
         >>>  withEffect (enableSubmit . isJust)
```

Finally, we need an MSF which sends a *submit* request
to the server, whenever the corresponding button is
clicked and all text fields contain valid input.

```idris
onSubmit : MonadUI m => MSF m Ev (Maybe Account) -> MSF m Ev ()
onSubmit sf =   fan [sf, when_ isSubmit]
            >>> justOnEvent
            >>> ifEvent (arrM submit)
```

We are ready to try out the first version of our
application controller:

```idris
testMSF1 : IO ()
testMSF1 = simulate (onSubmit account1)
             [ Input FAge "10"
             , Submit
             , Input FName "Höck"
             , Input FAge "40"
             , Input FAlias "me"
             , Submit
             ]
```

And at the REPL:

```
Doc.UIEx2> :exec testMSF1
alias: req. input, name: req. input, age: Invalid age: 10, disable submit
alias: req. input, name: req. input, age: Invalid age: 10, disable submit
alias: req. input, name: valid, age: Invalid age: 10, disable submit
alias: req. input, name: valid, age: valid, disable submit
alias: valid, name: valid, age: valid, enable submit
alias: valid, name: valid, age: valid, enable submit, submit: {me, Höck, 40}
```

We can see two things from this: The general behavior is correct,
however, on every event all fields are being validated and the
*enabled* state of the button is being updated.
In many cases, this will not be a problem.
But in case of a UI with many interactive elements
this might lead to a lot of redraws in the DOM and decrease
the responsiveness of the application. We therefore would like to
only update the UI, when a *real* change of state occured.

### Second Try: Validating an Event Stream

The problem of our first implementation was, that every
path in an MSF gets re-evaluated on every input event
unless we make use of one the choice combinators, which choose
amongst several MSFs based on a predicate or sum type.
For instance `inputFor fld` returns an `Event String`, which
is isomorphic to a `Maybe String`. If we make sure to
only run our validation logic in case this actually holds
a new string input, we make sure that no unnecessary work is being
done:

```idris
input2 :  {f : a -> Bool}
       -> MonadUI m
       => Cast String a
       => (fld : Field)
       -> (mk : (v : a) -> (0 prf : So (f v)) -> b)
       -> MSF m Ev (Maybe b)
input2 fld mk =   inputFor fld
              ^>> map (validate fld mk)
              ^>> withEffect (traverse_ $ validity fld)
              >>> hold (Left InputRequired)
              >>^ getRight

account2 : MonadUI m => MSF m Ev (Maybe Account)
account2 =    MkAccount
         <$$> input2 FAlias MkAlias
         <**> input2 FName  MkName
         <**> input2 FAge   MkAge
         >>>  withEffect (enableSubmit . isJust)

testMSF2 : IO ()
testMSF2 = simulate (onSubmit account2)
             [ Input FAge "10"
             , Submit
             , Input FName "Höck"
             , Input FAge "40"
             , Input FAlias "me"
             , Submit
             ]
```

And at the REPL:

```
Doc.UIEx2> :exec testMSF2
age: Invalid age: 10, disable submit
disable submit
name: valid, disable submit
age: valid, disable submit
alias: valid, enable submit
enable submit, submit: {me, Höck, 40}
```

Well, this didn't quite work out. While the *submit* button
is still being updated on every event, the text fields
will not be set to *input required* initially, since
validation of a given text field only happens
when a user types some text into exactly this field.

### Third Try: Using a custom Combinator

We already made sure that input in a text field
is only programmatically
validated when an actual input event happens at this
text field. However, we *also* need to take care about
the initial state a text field is in *before* any user
interaction happend at all.

There are several ways of handling this. For instance, we could
pair the `inputFor fld` event with an event stream, which
fires an event with an empty string exactly once:

```idris
aliasIn : MSF m Ev (Event String)
aliasIn = arr (inputFor FAlias) <|> once ""
```

While this would behave correctly, we'd still need to invoke
`hold` with an initial value to get a proper stream function
to build a validated `Account` value from the collected
text field contents. This would again lead to a repetition
of application logic. An alternative comes in form of
the `onChange` combinator. This compares the current value of
a signal function against its previous value, firing an event,
whenever the two are different. While this will be efficient
enough in most cases, it still performs unnecessary
computations. From the input events, we know *exactly* when
a value changes. Why should we recompute this information?
If for instance we are dealing with large lists of data,
comparing them on each input even might eventually have an
impact on performance of our web application.
We therefore write our own combinator for this use case, taking
into account what the input events tell us:

```idris
fireAndHold : o -> MSF m (Event o) (NP I [o, Event o])
fireAndHold v = fan [hold v, id <|> once v]
```

This combinator takes an event stream and passes it an initial
value converting it to both, a stream function as well as a new
event stream, which is guaranteed to fire an event at the
first evaluation step.

We can now extract a `Maybe b` from the resulting stream
function, while using the event stream for sending
validation info to the UI whenever the content of
the text field in question changed:

```idris
input :  {f : a -> Bool}
      -> MonadUI m
      => Cast String a
      => (fld : Field)
      -> (mk : (v : a) -> (0 prf : So (f v)) -> b)
      -> MSF m Ev (Maybe b)
input fld mk =   inputFor fld
             ^>> map (validate fld mk)
             ^>> fireAndHold (Left InputRequired) 
             >>> par [ arr getRight
                     , withEffect (traverse_ $ validity fld)
                     ]
             >>> hd
```

For enabling the *submit* button, we use `onChange` on
the corresponding boolean value, since
in this case it is not otherwise obvious, when the set
of text fields will turn from *invalid* to *valid* as
a whole:

```idris
account : MonadUI m => MSF m Ev (Maybe Account)
account =    MkAccount
        <$$> input FAlias MkAlias
        <**> input FName  MkName
        <**> input FAge   MkAge
        >>>  observeWith (isJust ^>> onChange >>> ifEvent (arrM enableSubmit))

testMSF : IO ()
testMSF = simulate (onSubmit account)
            [ Submit
            , Input FAge "10"
            , Input FAge "10"
            , Input FName ""
            , Submit
            , Input FName "Höck"
            , Input FAge "40"
            , Input FAlias "me"
            , Submit
            ]
```

And at the REPL:

```
Doc.UIEx2> :exec testMSF
alias: req. input, name: req. input, age: req. input, disable submit
age: Invalid age: 10
age: Invalid age: 10
name: req. input

name: valid
age: valid
alias: valid, enable submit
submit: {me, Höck, 40}
```

This is much better. There are still some unnecessary commands being
sent to the UI. These could be silenced by using `onChange` on
the string inputs directly, for instance. However, since in a real
user interface text input events only occur after key strokes, it is highly
unlikely that two identical input events will be fired in immediate
succession.

### Final Thoughts

As promised, this was a rather lengthy post. If we want to make sure
that input validation behaves correctly and no unnecessary work is
being done, we need some fine grained control about what happens
when. MSFs let us specify the exact wirings of information flow
and therefore grant us this degree of control, while still supporting
a declarative - albeit sometimes a bit cumbersome - way to describe them.

Perhaps you noticed the initial `Submit` event we fired when testing
the final example. What we didn't talk about so far is the *initialization*
of the user interface. If we use MSFs as our controllers, the
computations they perform will only take effect when they are being evaluated
(using `Data.MSF.Running.step`) for the first time. It therefore makes
sense to define some kind of *initialization event*, which the runtime
will fire before the user of our application even had a chance to
press the first key or click the first button. Setting up the
initial state of the UI should happen during this first step of
evaluation.
