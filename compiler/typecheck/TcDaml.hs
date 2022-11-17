{-# LANGUAGE NamedFieldPuns #-}
module TcDaml where

import GhcPrelude

import InstEnv
import Outputable
import TcRnTypes
import TyCoRep
import TyCon
import OccName
import Name
import Module
import PrelNames
import RdrHsSyn
import RdrName
import SrcLoc
import HsTypes
import HsDecls
import HsExtension
import Type
import FastString
import TcRnMonad
import IfaceSyn
import HscTypes
import Var
import UniqFM
import Util
import qualified Data.Map as M

import Data.Maybe
import Data.List
import qualified Prelude as P ((<>))
import Control.Monad
import Data.Foldable (fold)

check :: NamedThing a => [String] -> String -> a -> Bool
check modules name namedThing
  | Just mod <- moduleNameString . moduleName <$> nameModule_maybe (getName namedThing)
  , mod `elem` modules
  , name == occNameString (getOccName namedThing)
  = True
  | otherwise
  = False

customDamlErrors :: Ct -> TcM (Maybe SDoc)
customDamlErrors ct = do
  info <- getEnvDaml
  pure $ displayError info =<< customDamlError ct

data DamlError
  = TriedView { target :: Name, result :: Type }
  | TriedExercise { target :: Name, choice :: Name, result :: Type }
  | TriedImplementMethod { target :: Name, method :: FastString, result :: Type }
  | TriedImplementView { target :: Name, triedReturnType :: Type, expectedReturnType :: Type }
  | NonExistentFieldAccess { recordType :: Type, expectedReturnType :: Type, fieldName :: FastString }
  | FieldAccessWrongReturnType { fieldName :: FastString, recordType :: Type, triedReturnType :: Type, expectedReturnType :: Type }
  | NumericScaleOutOfBounds { attemptedScale :: Integer }

customDamlError :: Ct -> Maybe DamlError
customDamlError ct
  | TyConApp con [LitTy (NumTyLit attemptedScale)] <- ctev_pred (ctEvidence ct)
  , check ["DA.Internal.Desugar", "GHC.Classes"] "NumericScale" con
  , attemptedScale > 37 || attemptedScale < 0
  = Just $ NumericScaleOutOfBounds { attemptedScale }
  | TyConApp con [LitTy (StrTyLit fieldName), recordType, resultType] <- ctev_pred (ctEvidence ct)
  , check ["DA.Internal.Desugar", "DA.Internal.Record"] "HasField" con
  = Just $ NonExistentFieldAccess { fieldName, recordType, expectedReturnType = resultType }
  | FunDepOrigin2 targetPred _ instancePred _ <- ctOrigin ct
  , TyConApp targetCon [LitTy (StrTyLit fieldName1), recordType1, targetRetType] <- targetPred
  , TyConApp instanceCon [LitTy (StrTyLit fieldName2), recordType2, instanceRetType] <- instancePred
  , check ["DA.Internal.Desugar", "DA.Internal.Record"] "HasField" targetCon
  , check ["DA.Internal.Desugar", "DA.Internal.Record"] "HasField" instanceCon
  , fieldName1 == fieldName2
  , eqType recordType1 recordType2
  , not (eqType targetRetType instanceRetType)
  = Just $ FieldAccessWrongReturnType { fieldName = fieldName1, recordType = recordType1, triedReturnType = targetRetType, expectedReturnType = instanceRetType }
  | FunDepOrigin2 targetPred _ instancePred _ <- ctOrigin ct
  , TyConApp targetCon [TyConApp iface1 [], targetRetType] <- targetPred
  , TyConApp instanceCon [TyConApp iface2 [], instanceRetType] <- instancePred
  , check ["DA.Internal.Desugar", "DA.Internal.Interface"] "HasInterfaceView" targetCon
  , check ["DA.Internal.Desugar", "DA.Internal.Interface"] "HasInterfaceView" instanceCon
  , iface1 == iface2
  , not (eqType targetRetType instanceRetType)
  = Just $ TriedImplementView { target = tyConName iface1, triedReturnType = targetRetType, expectedReturnType = instanceRetType }
  | TyConApp con [TyConApp target [], viewType] <- ctev_pred (ctEvidence ct)
  , check ["DA.Internal.Desugar", "DA.Internal.Interface"] "HasInterfaceView" con
  = Just $ TriedView { target = tyConName target, result = viewType }
  | TyConApp con [TyConApp target [], TyConApp choice [], result] <- ctev_pred (ctEvidence ct)
  , check ["DA.Internal.Desugar", "DA.Internal.Template.Functions"] "HasExercise" con
  = Just $ TriedExercise { target = tyConName target, choice = tyConName choice, result }
  | TyConApp con [TyConApp target [], LitTy (StrTyLit methodName), result] <- ctev_pred (ctEvidence ct)
  , check ["DA.Internal.Desugar"] "HasMethod" con
  = Just $ TriedImplementMethod { target = tyConName target, method = methodName, result }
  | otherwise
  = Nothing

printListWithHeader :: SDoc -> SDoc -> [SDoc] -> SDoc
printListWithHeader emptyMsg _ [] = emptyMsg
printListWithHeader _ nonEmptyMsg outs = nonEmptyMsg <+> hcat (punctuate (text ", ") outs)

displayError :: DamlInfo -> DamlError -> Maybe SDoc
displayError info TriedView { target, result }
  | isTemplate info target
  = pure
  $ vcat [ text "Tried to get an interface view of type" <+> pprq result <+> text "from template" <+> pprq target
         , text "Cast template" <+> pprq target <+> text "to an interface before getting its view."
         , printListWithHeader
              (text "Template" <+> pprq target <+> text "does not have any known interface implementations.")
              (text "Template" <+> pprq target <+> text "has the following interfaces:")
              (map pprq (allImplementedInterfaces info target))
         ]
  | isInterface info target
  , Just view <- interfaceView info target
  = pure
  $ text "Tried to get an interface view of type" <+> pprq result <+> text "from interface" <+> pprq target <+> text "but that interface's view is of type" <+> pprq view
  | isInterface info target
  = pure
  $ text "Tried to get an interface view of type" <+> pprq result <+> text "from interface" <+> pprq target <+> text "but that interface's view is not of type" <+> pprq result
  | otherwise
  = pure
  $ text "Tried to get an interface view of type" <+> pprq result <+> text "from type" <+> pprq target <+> text "which is neither an interface nor a template"
displayError info TriedExercise { target, result, choice }
  | [implementor] <- choiceImplementor info choice
  , isInterface info implementor
  , implements info target implementor
  , target /= implementor -- since interfaces implement themselves, we ignore if the target is itself
  = pure
  $ vcat [ text "Tried to exercise a choice" <+> pprq choice <+> text "on" <+> variantName info target
         , text "The choice" <+> pprq choice <+> text "belongs to" <+> variantName info implementor <+> text "which" <+> pprq target <+> text "implements."
         , text "Cast" <+> variantName info target <+> text "to" <+> variantName info implementor <+> text "before exercising the choice."
         ]
  | otherwise
  = pure
  $ vcat [ text "Tried to exercise a choice" <+> pprq choice <+> text "on" <+> variantName info target <+> text "but no choice of that name exists on" <+> variantName info target
         , printListWithHeader
              empty
              (text "Choice" <+> pprq choice <+> text "belongs only to the following types:")
              (map (variantName info) (choiceImplementor info choice))
         ]
displayError info TriedImplementMethod { target, method, result } =
  let ifaces = definesMethod info method
  in
  case target `lookup` ifaces of
    Just expectedResult
      | not (eqType expectedResult result)
      -> pure $ text "Implementation of method" <+> pprq method <+> text "on interface" <+> pprq target <+> text "should return" <+> pprq expectedResult <+> text "but instead returns " <+> pprq result
      | otherwise
      -> Nothing
    Nothing ->
      pure $
      vcat [ text "Tried to implement method" <+> pprq method <> text ", but interface" <+> pprq target <+> text "does not have a method with that name."
           , printListWithHeader
               empty
               (text "Method" <+> pprq method <+> text "is only a method on the following interfaces:")
               (map (pprq . fst) ifaces)
           ]
displayError info TriedImplementView { target, triedReturnType, expectedReturnType } =
  pure $ text "Tried to implement a view of type" <+> pprq triedReturnType <+> text "on interface" <+> pprq target
      <> text ", but the definition of interface" <+> pprq target <+> text "requires a view of type" <+> pprq expectedReturnType
displayError info NonExistentFieldAccess { recordType, expectedReturnType, fieldName } =
  pure $ text "Tried to access nonexistent field" <+> pprq fieldName
     <+> text "with type" <+> pprq expectedReturnType
     <+> text "on value of type" <+> pprq recordType
displayError info FieldAccessWrongReturnType { recordType, triedReturnType, expectedReturnType, fieldName } =
  pure $ text "Tried to get field" <+> pprq fieldName
     <+> text "with type" <+> pprq triedReturnType
     <+> text "on value of type" <+> pprq recordType
      <> text ", but that field has type" <+> pprq expectedReturnType
displayError info NumericScaleOutOfBounds { attemptedScale }
  | attemptedScale > 37
  = pure $ text "Tried to create a Numeric with a scale of" <+> ppr attemptedScale <> text ", but only scales up to 37 are supported."
  | attemptedScale < 0
  = pure $ text "Tried to create a Numeric with a negative scale, but Numerics must have a positive scale."

dedupe :: DamlInfo -> DamlInfo
dedupe (DamlInfo x0 x1 x2 x3 x4 x5) =
  DamlInfo
    (nubSort x0)
    (nubSort x1)
    (nubSort x2)
    (nubSortBy (\(mName, (cName, type_)) -> (mName, cName)) x3)
    (nubSort x4)
    (nubSortBy fst x5)
  where
    nubSortBy :: Ord b => (a -> b) -> [a] -> [a]
    nubSortBy f xs = M.elems $ M.fromList $ map (\x -> (f x, x)) xs

pprq :: Outputable a => a -> SDoc
pprq = quotes . ppr

isTemplate, isInterface :: DamlInfo -> Name -> Bool
isTemplate info name = name `elem` templates info
isInterface info name = name `elem` interfaces info

variantName :: DamlInfo -> Name -> SDoc
variantName info name
  | isTemplate info name = text "template" <+> pprq name
  | isInterface info name = text "interface" <+> pprq name
  | otherwise = text "type" <+> pprq name

allImplementedInterfaces, allImplementingTemplates :: DamlInfo -> Name -> [Name]
allImplementedInterfaces info name = [iface | (tpl, iface) <- implementations info, name == tpl]
allImplementingTemplates info name = [tpl | (tpl, iface) <- implementations info, name == iface]

implements :: DamlInfo -> Name -> Name -> Bool
implements info tpl iface = (tpl, iface) `elem` implementations info

choiceImplementor :: DamlInfo -> Name -> [Name]
choiceImplementor info name = [tplOrIface | (tplOrIface, choice) <- choices info, name == choice]

interfaceView :: DamlInfo -> Name -> Maybe Type
interfaceView info name = lookup name (views info)

definesMethod :: DamlInfo -> FastString -> [(Name, Type)]
definesMethod info method = [nameAndType | (m, nameAndType) <- methods info, m == method]

instance Monoid DamlInfo where
  mempty = DamlInfo [] [] [] [] [] []

instance Semigroup DamlInfo where
  (<>) (DamlInfo a0 a1 a2 a3 a4 a5) (DamlInfo b0 b1 b2 b3 b4 b5) =
    DamlInfo (a0 P.<> b0) (a1 P.<> b1) (a2 P.<> b2) (a3 P.<> b3) (a4 P.<> b4) (a5 P.<> b5)

instance Outputable DamlInfo where
  ppr info =
    hang (text "DamlInfo {") 2 $
    vcat [ text "templates =" <+> ppr (templates info)
         , text "interfaces =" <+> ppr (interfaces info)
         , text "choices =" <+> ppr (choices info)
         , text "methods =" <+> ppr (methods info)
         , text "implementations =" <+> ppr (implementations info)
         , text "views =" <+> ppr (views info)
         , text "}"
         ]

getEnvDaml :: TcM DamlInfo
getEnvDaml = do
  env <- getEnv
  mb_daml <- readMutVar (env_daml env)
  case mb_daml of
    Nothing -> do
      eps <- readMutVar $ hsc_EPS $ env_top env

      let tcg_tythings = foldMap extractDamlInfoFromTyThing (typeEnvElts $ tcg_type_env $ env_gbl env)
      let tcg_insts = foldMap extractDamlInfoFromClsInst (instEnvElts $ tcg_inst_env $ env_gbl env)
      let eps_tythings = foldMap extractDamlInfoFromTyThing (typeEnvElts $ eps_PTE eps)
      let eps_insts = foldMap extractDamlInfoFromClsInst (instEnvElts $ eps_inst_env eps)
      traceTc "DamlInfo tcg_tythings extracted" $ ppr tcg_tythings
      traceTc "DamlInfo tcg_insts extracted" $ ppr tcg_insts
      traceTc "DamlInfo eps_tythings extracted" $ ppr eps_tythings
      traceTc "DamlInfo eps_insts extracted" $ ppr eps_insts

      let new_info = dedupe (fold [tcg_tythings, tcg_insts, eps_tythings, eps_insts])
      traceTc "DamlInfo new_info" $ ppr new_info

      writeMutVar (env_daml env) (Just new_info)
      pure new_info
    Just info -> pure info

extractDamlInfoFromTyThing :: TyThing -> DamlInfo
extractDamlInfoFromTyThing tything =
  case tything of
    ATyCon tycon ->
      mempty
        { templates = mapMaybe matchTemplate [tycon]
        , interfaces = mapMaybe matchInterface [tycon]
        }
    _ -> mempty
  where
    matchTemplate, matchInterface :: TyCon -> Maybe Name
    matchTemplate = tyconWithConstraint "DamlTemplate"
    matchInterface = tyconWithConstraint "DamlInterface"

    tyconWithConstraint :: String -> TyCon -> Maybe Name
    tyconWithConstraint targetName tycon
      | isAlgTyCon tycon
      , let isMatchingLoneConstraint type_
              | Just (loneConstraint, []) <- splitTyConApp_maybe type_
              = similarName targetName (tyConName loneConstraint)
              | otherwise
              = False
      , any isMatchingLoneConstraint (tyConStupidTheta tycon)
      = Just $ tyConName tycon
      | otherwise
      = Nothing

extractDamlInfoFromClsInst :: ClsInst -> DamlInfo
extractDamlInfoFromClsInst inst =
  mempty
    { choices = mapMaybe matchChoice [inst]
    , methods = mapMaybe matchMethod [inst]
    , implementations = mapMaybe matchImplements [inst]
    , views = mapMaybe matchView [inst]
    }
  where
    matchChoice :: ClsInst -> Maybe (Name, Name)
    matchChoice clsInst = do
      [contractType, choiceType, returnType] <-
          clsInstMatch "HasExercise" clsInst
      (contractTyCon, []) <- splitTyConApp_maybe contractType
      (choiceTyCon, []) <- splitTyConApp_maybe choiceType
      pure (tyConName contractTyCon, tyConName choiceTyCon)

    matchMethod :: ClsInst -> Maybe (FastString, (Name, Type))
    matchMethod clsInst = do
      [contractType, methodNameType, returnType] <-
          clsInstMatch "HasMethod" clsInst
      (StrTyLit methodName) <- isLitTy methodNameType
      (contractTyCon, []) <- splitTyConApp_maybe contractType
      pure (methodName, (tyConName contractTyCon, returnType))

    matchImplements :: ClsInst -> Maybe (Name, Name)
    matchImplements clsInst = do
      [templateType, interfaceType] <-
          clsInstMatch "HasToInterface" clsInst
      (templateTyCon, []) <- splitTyConApp_maybe templateType
      (interfaceTyCon, []) <- splitTyConApp_maybe interfaceType
      pure (tyConName templateTyCon, tyConName interfaceTyCon)

    matchView :: ClsInst -> Maybe (Name, Type)
    matchView clsInst = do
      [ifaceType, viewType] <-
          clsInstMatch "HasInterfaceView" clsInst
      (ifaceTyCon, []) <- splitTyConApp_maybe ifaceType
      pure (tyConName ifaceTyCon, viewType)

    clsInstMatch :: String -> ClsInst -> Maybe [Type]
    clsInstMatch targetName clsInst = do
      guard $ similarName targetName (is_cls_nm clsInst)
      pure $ is_tys clsInst

similarName :: String -> Name -> Bool
similarName target name = occNameString (nameOccName name) == target

