{-# LANGUAGE DamlSyntax #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PackageImports #-}

-- This file provides a definition required by a desugared DAML template.

module GHC.Types (primitive) where

import "ghc-prim" GHC.Types

primitive : forall (f : Symbol) b. b
primitive = primitive
