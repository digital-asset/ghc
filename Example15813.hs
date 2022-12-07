{-# LANGUAGE DamlSyntax #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Example15813 where

import DA.Internal.Desugar
import GHC.Types

template T
  with
    p : Party
  where
    signatory p

    choice C : ()
      controller p
      do pure ()

template U
  with
    p2 : Party
  where
    signatory p2

abort : Text -> Update a
abort = undefined

exerciseE : Choice t c (Either Text r) => ContractId t -> c -> Update r
exerciseE cid c = do
  r <- exercise cid c
  case r of
    Left err -> abort err
    Right r -> pure r

test : ContractId T -> Update ()
test cid = exerciseE cid C

-- test2 : ContractId U -> Update ()
-- test2 cid = exercise cid C
