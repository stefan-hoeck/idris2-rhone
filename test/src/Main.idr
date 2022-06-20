module Main

import Basics
import Hedgehog

main : IO ()
main = test [ Basics.props
            ]
