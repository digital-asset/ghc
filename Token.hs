{-# LANGUAGE DamlSyntax #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module Example where

import DA.Internal.Desugar
import GHC.Types

interface Token where
{-
  getAmount : Decimal
-}
  choice Split : (ContractId Token, ContractId Token)
    with
      splitAmount : Int

  choice Transfer : ContractId Token
    with
      newOwner : Party

template Asset
  with
    amount : Decimal
    issuer : Party
    owner : Party
  where
    signatory issuer, owner

    implements Token where

      choice Split : (ContractId Token, ContractId Token)
        with
          splitAmount : Int
        controller owner
        do error "not implemented"

      choice Transfer : ContractId Token
        with
          newOwner : Int
        controller newOwner, owner
        do error "not implemented"

{-
      let getAmount = amount
-}

    choice OtherChoice : ()
     controller owner
     do pure ()
