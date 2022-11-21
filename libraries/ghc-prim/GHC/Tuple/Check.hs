{-# LANGUAGE DamlSyntax #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TypeApplications #-}

module GHC.Tuple.Check where

import GHC.Types

userWrittenTuple : a -> a
userWrittenTuple = \a -> a
