{-# LANGUAGE DamlSyntax #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- This file contains a minimal setup to allow the compilation of a desugared DAML template.

module DA.Internal.Desugar
  ( module DA.Internal.Desugar
  , concat
  , Bool(..)
  , Eq(..)
  , Show(..)
  )
where

import GHC.TypeLits (Symbol)
import GHC.Types (primitive)
import Data.String (IsString(..))

data Any
data ContractId a
data Update a
data TypeRep
data Party
data Text

data Optional a = None | Some a

data Consuming t = Consuming {}

data Archive = Archive {}

instance IsString Text where fromString = undefined

class IsParties a where
  toParties : a -> [Party]

instance IsParties Party where
  toParties p = [p]

instance IsParties [Party] where
  toParties ps = ps

instance IsParties (Optional Party) where
  toParties None = []
  toParties (Some p) = [p]

instance Eq Party where (==) = undefined
instance Show Party where show = undefined

instance Functor Update where
    fmap f x = x >>= \v -> pure (f v)

instance Applicative Update where
    pure = undefined
    f <*> x = f >>= \f -> x >>= \x -> pure (f x)

instance Monad Update where
    (>>=) = undefined

class HasSignatory t where
  signatory : t -> [Party]

class HasObserver t where
  observer : t -> [Party]

class HasEnsure t where
  ensure : t -> Bool

class HasAgreement t where
  agreement : t -> Text

class HasCreate t where
  create : t -> Update (ContractId t)

class HasFetch t where
  fetch : ContractId t -> Update t

class HasArchive t where
  archive : ContractId t -> Update ()

class HasTemplateTypeRep t where
  _templateTypeRep : proxy t -> TypeRep

class HasToAnyTemplate t where
  _toAnyTemplate : t -> Any

class HasFromAnyTemplate t where
  _fromAnyTemplate : Any -> Optional t

class HasExercise t c r | t c -> r where
  exercise : ContractId t -> c -> Update r

class HasToAnyChoice t c r | t c -> r where
  _toAnyChoice : proxy t -> c -> Any

class HasFromAnyChoice t c r | t c -> r where
  _fromAnyChoice : proxy t -> Any -> Optional c

class HasInterfaceTypeRep i where
  interfaceTypeRep : i -> TypeRep

class HasInterfaceTypeRep i => Implements t i where
  toInterface : t -> i
  fromInterface : i -> Optional t

coerceContractId : ContractId t -> ContractId i
coerceContractId = primitive @"BECoerceContractId"

toInterfaceContractId : forall i t. Implements t i => ContractId t -> ContractId i
toInterfaceContractId = coerceContractId

fromInterfaceContractId : forall t i. (Implements t i, HasFetch i) => ContractId i -> Update (Optional (ContractId t))
fromInterfaceContractId cid = do
  iface <- fetch cid
  pure $ case fromInterface iface of
    None -> None
    Some (_ : t) -> Some (coerceContractId cid)

class HasMethod i (m : Symbol) r | i m -> r

newtype Method t i (m : Symbol) r = Method { unMethod : t -> r }

mkMethod : (Implements t i, HasMethod i m r) => (t -> r) -> Method t i m r
mkMethod = Method
