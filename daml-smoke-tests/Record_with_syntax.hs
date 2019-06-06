{-# LANGUAGE DamlSyntax #-}

daml 1.2
module Record_with_syntax where

data R = R with { foo :: Integer; bar :: String }

data S =
  S with
    quux :: Integer
    corge :: String

updateR :: R -> R
updateR r =
  r with
    foo = 1
    bar = "quux"
