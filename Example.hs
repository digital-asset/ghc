{-# LANGUAGE DamlSyntax #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Example where

{-
This file contains an example of a DAML template which can be compiled, desugared, and type-check:
$ ./_build/stage1/bin/ghc ./Example.hs

A minimal environment (to support the code generated by desugaring) is provided in:
  ./DA/Internal/Desugar.hs
  ./GHC/Types.hs
-}

import DA.Internal.Desugar
import GHC.Types

interface TheInterface where
  myInternalValue : Int
  viewtype Int

template TheTemplate
  with
    s : Party
  where
    signatory s
    agreement "my agreement"

    choice MyObservedChoice : () with obs : [Party]
      observer obs
      controller s
      do return ()

    implements TheInterface where
      myInternalValue = 1000
      view = myInternalValue this * 1000
