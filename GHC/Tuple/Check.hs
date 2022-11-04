{-# LANGUAGE DamlSyntax #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module GHC.Tuple.Check where

import GHC.Types

userWrittenTuple : a -> a
userWrittenTuple = magic @"userWrittenTuple"
