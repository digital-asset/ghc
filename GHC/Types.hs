{-# LANGUAGE DamlSyntax #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PackageImports #-}

-- This file provides a definition required by a desugared DAML template.

module GHC.Types (DamlInterface, Decimal, Opaque, primitive, primitiveInterface) where

import "ghc-prim" GHC.Types

primitive : forall (f : Symbol) b. b
primitive = primitive

primitiveInterface : forall (f : Symbol) b. b
primitiveInterface = primitiveInterface

data Opaque = Opaque

data Decimal = Decimal
  deriving (Eq, Show)

class DamlInterface
instance DamlInterface
