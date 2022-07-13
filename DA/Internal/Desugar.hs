{-# LANGUAGE DamlSyntax #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

-- This file contains a minimal setup to allow the compilation of a desugared
-- DAML template and interface.

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

optional : b -> (a -> b) -> Optional a -> b
optional n _ None  = n
optional _ f (Some x) = f x

data Consuming t = Consuming {}
data NonConsuming t = NonConsuming {}

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

class HasKey t k | t -> k where
  key : t -> k

class HasLookupByKey t k | t -> k where
  lookupByKey : k -> Update (Optional (ContractId t))

class HasFetchByKey t k | t -> k where
  fetchByKey : k -> Update (ContractId t, t)

class HasMaintainer t k | t -> k where
  _maintainer : proxy t -> k -> [Party]

class HasToAnyContractKey t k | t -> k where
  _toAnyContractKey : proxy t -> k -> Any

class HasFromAnyContractKey t k | t -> k where
  _fromAnyContractKey : proxy t -> Any -> Optional k

class HasExerciseByKey t k c r | t -> k, t c -> r where
  _exerciseByKey : proxy t -> k -> c -> Update r

class HasIsInterfaceType t where
  _isInterfaceType : proxy t -> Bool

_typeRepForInterfaceExercise : (HasTemplateTypeRep t, HasIsInterfaceType t) => proxy t -> Optional TypeRep
_typeRepForInterfaceExercise p =
  if _isInterfaceType p
    then None
    else Some (_templateTypeRep p)

class HasInterfaceTypeRep i where
  _interfaceTypeRep : i -> TypeRep

class HasToInterface t i where
  _toInterface : t -> i

toInterface : forall i t. HasToInterface t i => t -> i
toInterface = _toInterface

class HasFromInterface t i where
  fromInterface : i -> Optional t
  unsafeFromInterface : ContractId i -> i -> t

-- Read: Interface `i` has a view of type `r`
class HasInterfaceView i v | i -> v

-- | This is only a marker for the container, it doesn't contain the
-- actual implementation of the method.
newtype InterfaceView t i = InterfaceView ()

type Implements t i =
  ( HasInterfaceTypeRep i
  , HasToInterface t i
  , HasFromInterface t i
  , HasInterfaceView t i
  )

coerceContractId : ContractId t -> ContractId i
coerceContractId = primitive @"BECoerceContractId"

toInterfaceContractId : forall i t. HasToInterface t i => ContractId t -> ContractId i
toInterfaceContractId = coerceContractId

fromInterfaceContractId : forall t i. (HasFromInterface t i, HasFetch i) => ContractId i -> Update (Optional (ContractId t))
fromInterfaceContractId cid = do
  iface <- fetch cid
  pure $ case fromInterface iface of
    None -> None
    Some (_ : t) -> Some (coerceContractId cid)

data ImplementsT t i = ImplementsT
data RequiresT a b = RequiresT

class HasMethod i (m : Symbol) r | i m -> r

newtype Method t i (m : Symbol) = Method ()

mkMethod : (Implements t i, HasMethod i m r) => (t -> r) -> Method t i m
mkMethod _ = Method ()

class HasExerciseGuarded t c r | t c -> r where
  exerciseGuarded : (t -> Bool) -> ContractId t -> c -> Update r

_exerciseDefault : HasExerciseGuarded t c r => ContractId t -> c -> Update r
_exerciseDefault = exerciseGuarded (const True)

_exerciseInterfaceGuard : forall i t. HasFromInterface t i => (t -> Bool) -> (i -> Bool)
_exerciseInterfaceGuard pred iface =
  optional False pred (fromInterface iface)
