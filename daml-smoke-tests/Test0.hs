{-# LANGUAGE DamlSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- Covers:
--   Version syntax
--   New colon convention
--   Record "with" definition/update
--   Function return type annotations

daml 1.2
module Test0 where

data R = R with { foo : Integer; bar : String }

data S =
  S with
    quux : Integer
    corge : String

updateR : R -> R
updateR r =
  r with
    foo = 1
    bar = "quux"

fact (n : Integer) : Integer
 | n <= 1    = 1
 | otherwise = n * fact (n - 1)
