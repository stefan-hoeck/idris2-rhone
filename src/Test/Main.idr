module Test.Main

import Test.Basics
import Hedgehog

main : IO ()
main = test [ Basics.props
            ]
