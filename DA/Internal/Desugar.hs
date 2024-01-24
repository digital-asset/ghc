{-# LANGUAGE DamlSyntax #-}
{-# LANGUAGE PolyKinds #-}
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
{-# LANGUAGE AllowAmbiguousTypes #-} -- setField doesn't mention x, because we pass it as a type application

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

import GHC.TypeLits (Symbol, Nat)
import GHC.Types (primitive, magic)
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

class HasChoiceController t c where
  _choiceController : t -> c -> [Party]

class HasChoiceObserver t c where
  _choiceObserver : t -> c -> [Party]

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

class HasInterfaceView i v | i -> v where
  _view : i -> v

view : forall i v. HasInterfaceView i v => i -> v
view = _view

class HasFromAnyView i v | i -> v where
  _fromAnyView : proxy i -> Any -> Optional v

type Implements t i =
  ( HasInterfaceTypeRep i
  , HasToInterface t i
  , HasFromInterface t i
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

data RequiresT a b = RequiresT

class HasExerciseGuarded t c r | t c -> r where
  exerciseGuarded : (t -> Bool) -> ContractId t -> c -> Update r

_exerciseDefault : HasExerciseGuarded t c r => ContractId t -> c -> Update r
_exerciseDefault = exerciseGuarded (const True)

_exerciseInterfaceGuard : forall i t.
  (HasFromInterface t i, HasInterfaceTypeRep i, HasTemplateTypeRep t) =>
  ContractId t -> (t -> Bool) -> i -> Bool
_exerciseInterfaceGuard cid tpred ivalue =
  tpred (unsafeFromInterface (coerceContractId cid) ivalue)

--------------------------------------------------------------------------------
-- # Interface instance desugaring

-- ## Interface instance markers

-- | The type arguments @p@, @i@ and @t@ refer, respectively, to the
-- parent, interface and template of this interface instance. The parent
-- is the type whose declaration contains the interface instance, and must match
-- either the interface or the template. This is checked in RdrHsSyn and again
-- during LF Conversion.
newtype InterfaceInstance p i t = InterfaceInstance ()

mkInterfaceInstance : forall p i t. InterfaceInstance p i t
mkInterfaceInstance = InterfaceInstance ()

-- ## Method bodies

class HasMethod i (m : Symbol) r | i m -> r

-- | The type arguments @p@, @i@ and @t@ are the same as in 'InterfaceInstance',
-- while @m@ is the name of the method represented as a 'Symbol'.
newtype Method p i t (m : Symbol) = Method ()

mkMethod : forall p i t m r. (Implements t i, HasMethod i m r) => (t -> r) -> Method p i t m
mkMethod _ = Method ()

-- ## View bodies

-- class HasInterfaceView is also used for the type of the `view` function,
-- so it's not here.

-- | The type arguments @p@, @i@ and @t@ are the same as in 'InterfaceInstance'.
newtype InterfaceView p i t = InterfaceView ()

mkInterfaceView : forall p i t v. (Implements t i, HasInterfaceView i v) => (t -> v) -> InterfaceView p i t
mkInterfaceView _ = InterfaceView ()

class HasField (x : Symbol) r a | x r -> a where
    getField : r -> a
    setField : a -> r -> r

bypassReduceLambda : forall a. a -> a
bypassReduceLambda = magic @"bypassReduceLambda"

class NumericScale (n : Nat) where
    -- | Get the scale of a `Numeric` as an integer. For example,
    -- `numericScale (3.14159 : Numeric 5)` equals `5`.
    numericScale : proxy n -> Int

    -- | HIDE
    numericScalePrivate : proxy n -> ()

instance NumericScale 0 where numericScale _ = 0; numericScalePrivate _ = ()
instance NumericScale 1 where numericScale _ = 1; numericScalePrivate _ = ()
instance NumericScale 2 where numericScale _ = 2; numericScalePrivate _ = ()
instance NumericScale 3 where numericScale _ = 3; numericScalePrivate _ = ()
instance NumericScale 4 where numericScale _ = 4; numericScalePrivate _ = ()
instance NumericScale 5 where numericScale _ = 5; numericScalePrivate _ = ()
instance NumericScale 6 where numericScale _ = 6; numericScalePrivate _ = ()
instance NumericScale 7 where numericScale _ = 7; numericScalePrivate _ = ()
instance NumericScale 8 where numericScale _ = 8; numericScalePrivate _ = ()
instance NumericScale 9 where numericScale _ = 9; numericScalePrivate _ = ()
instance NumericScale 10 where numericScale _ = 10; numericScalePrivate _ = ()
instance NumericScale 11 where numericScale _ = 11; numericScalePrivate _ = ()
instance NumericScale 12 where numericScale _ = 12; numericScalePrivate _ = ()
instance NumericScale 13 where numericScale _ = 13; numericScalePrivate _ = ()
instance NumericScale 14 where numericScale _ = 14; numericScalePrivate _ = ()
instance NumericScale 15 where numericScale _ = 15; numericScalePrivate _ = ()
instance NumericScale 16 where numericScale _ = 16; numericScalePrivate _ = ()
instance NumericScale 17 where numericScale _ = 17; numericScalePrivate _ = ()
instance NumericScale 18 where numericScale _ = 18; numericScalePrivate _ = ()
instance NumericScale 19 where numericScale _ = 19; numericScalePrivate _ = ()
instance NumericScale 20 where numericScale _ = 20; numericScalePrivate _ = ()
instance NumericScale 21 where numericScale _ = 21; numericScalePrivate _ = ()
instance NumericScale 22 where numericScale _ = 22; numericScalePrivate _ = ()
instance NumericScale 23 where numericScale _ = 23; numericScalePrivate _ = ()
instance NumericScale 24 where numericScale _ = 24; numericScalePrivate _ = ()
instance NumericScale 25 where numericScale _ = 25; numericScalePrivate _ = ()
instance NumericScale 26 where numericScale _ = 26; numericScalePrivate _ = ()
instance NumericScale 27 where numericScale _ = 27; numericScalePrivate _ = ()
instance NumericScale 28 where numericScale _ = 28; numericScalePrivate _ = ()
instance NumericScale 29 where numericScale _ = 29; numericScalePrivate _ = ()
instance NumericScale 30 where numericScale _ = 30; numericScalePrivate _ = ()
instance NumericScale 31 where numericScale _ = 31; numericScalePrivate _ = ()
instance NumericScale 32 where numericScale _ = 32; numericScalePrivate _ = ()
instance NumericScale 33 where numericScale _ = 33; numericScalePrivate _ = ()
instance NumericScale 34 where numericScale _ = 34; numericScalePrivate _ = ()
instance NumericScale 35 where numericScale _ = 35; numericScalePrivate _ = ()
instance NumericScale 36 where numericScale _ = 36; numericScalePrivate _ = ()
instance NumericScale 37 where numericScale _ = 37; numericScalePrivate _ = ()

data Numeric (n : Nat)
