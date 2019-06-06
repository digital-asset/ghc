{-# LANGUAGE DamlSyntax #-}

data R = R with foo :: Integer; bar :: String

updateR :: R -> R
updateR r =
  r with
    foo = 1
    bar = "quux"

main :: IO ()
main = undefined
