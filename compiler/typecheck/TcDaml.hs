{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
module TcDaml where

import GhcPrelude

import qualified Data.Set as S
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

import Data.Bifunctor
import Data.Maybe
import Data.Either (partitionEithers)
import Data.Function (on)
import Data.List
import qualified Prelude as P ((<>))
import Control.Monad
import Data.Foldable (fold)

check :: NamedThing a => [String] -> [String] -> a -> Bool
check modules names namedThing
  | Just mod <- moduleNameString . moduleName <$> nameModule_maybe (getName namedThing)
  , mod `elem` modules
  , occNameString (getOccName namedThing) `elem` names
  = True
  | otherwise
  = False

customDamlError :: DamlInfo -> Ct -> Maybe SDoc
customDamlError info ct = do
  e <- detectError info ct
  m <- displayError info e
  pure (vcat [text "Possible Daml-specific reason for the following type error:", m])

data DamlError
  = TriedView { target :: Name, result :: Type }
  | TriedExercise { target :: Name, choice :: Name, result :: Type }
  | TriedImplementMethod { target :: Name, method :: FastString, result :: Type }
  | TriedImplementView { target :: Name, triedReturnType :: Type, expectedReturnType :: Type }
  | NonExistentFieldAccess { recordType :: Type, expectedReturnType :: Type, fieldName :: FastString }
  | FieldAccessWrongReturnType { fieldName :: FastString, recordType :: Type, triedReturnType :: Type, expectedReturnType :: Type }
  | NumericScaleOutOfBounds { attemptedScale :: Integer }
  | TriedImplementNonInterface { triedIface :: Name }

detectError :: DamlInfo -> Ct -> Maybe DamlError
detectError info ct
  | TyConApp con [LitTy (NumTyLit attemptedScale)] <- ctev_pred (ctEvidence ct)
  , check ["DA.Internal.Desugar", "GHC.Classes"] ["NumericScale"] con
  , attemptedScale > 37 || attemptedScale < 0
  = Just $ NumericScaleOutOfBounds { attemptedScale }
  | TyConApp con [LitTy (StrTyLit fieldName), recordType, resultType] <- ctev_pred (ctEvidence ct)
  , check ["DA.Internal.Desugar", "DA.Internal.Record"] ["HasField"] con
  = Just $ NonExistentFieldAccess { fieldName, recordType, expectedReturnType = resultType }
  | FunDepOrigin2 targetPred _ instancePred _ <- ctOrigin ct
  , TyConApp targetPredCon [LitTy (StrTyLit fieldName1), recordType1, targetRetType] <- targetPred
  , TyConApp instancePredCon [LitTy (StrTyLit fieldName2), recordType2, instanceRetType] <- instancePred
  , check ["DA.Internal.Desugar", "DA.Internal.Record"] ["HasField"] targetPredCon
  , check ["DA.Internal.Desugar", "DA.Internal.Record"] ["HasField"] instancePredCon
  , fieldName1 == fieldName2
  , eqType recordType1 recordType2
  , not (eqType targetRetType instanceRetType)
  = Just $ FieldAccessWrongReturnType { fieldName = fieldName1, recordType = recordType1, triedReturnType = targetRetType, expectedReturnType = instanceRetType }
  | TyConApp con [TyConApp target []] <- ctev_pred (ctEvidence ct)
  , check ["DA.Internal.Desugar", "DA.Internal.Interface"] ["HasInterfaceTypeRep"] con
  = Just $ TriedImplementNonInterface { triedIface = tyConName target }
  | FunDepOrigin2 targetPred _ instancePred _ <- ctOrigin ct
  , TyConApp targetPredCon [TyConApp iface1 [], targetRetType] <- targetPred
  , TyConApp instancePredCon [TyConApp iface2 [], instanceRetType] <- instancePred
  , check ["DA.Internal.Desugar", "DA.Internal.Interface"] ["HasInterfaceView"] targetPredCon
  , check ["DA.Internal.Desugar", "DA.Internal.Interface"] ["HasInterfaceView"] instancePredCon
  , let iface1Name = tyConName iface1
  , let iface2Name = tyConName iface2
  , synEq info iface1Name iface2Name
  , not (eqType targetRetType instanceRetType)
  = Just $ TriedImplementView { target = iface1Name, triedReturnType = targetRetType, expectedReturnType = instanceRetType }
  | TyConApp con [TyConApp target [], viewType] <- ctev_pred (ctEvidence ct)
  , check ["DA.Internal.Desugar", "DA.Internal.Interface"] ["HasInterfaceView"] con
  = Just $ TriedView { target = tyConName target, result = viewType }
  | FunDepOrigin2 targetPred _ instancePred _ <- ctOrigin ct
  , TyConApp targetPredCon (_ `Snoc` TyConApp targetCon [] `Snoc` LitTy (StrTyLit targetMethodName) `Snoc` targetResult) <- targetPred
  , TyConApp instancePredCon (_ `Snoc` TyConApp instanceCon [] `Snoc` LitTy (StrTyLit instanceMethodName) `Snoc` instanceResult) <- instancePred
  , check ["DA.Internal.Desugar"] ["HasMethod"] targetPredCon
  , check ["DA.Internal.Desugar"] ["HasMethod"] instancePredCon
  , let targetConName = tyConName targetCon
  , let instanceConName = tyConName instanceCon
  , synEq info targetConName instanceConName
  , targetMethodName == instanceMethodName
  , not (eqType targetResult instanceResult)
  = Just $ TriedImplementMethod { target = targetConName, method = targetMethodName, result = targetResult }
  | FunDepOrigin2 targetPred _ instancePred _ <- ctOrigin ct
  , TyConApp targetPredCon [TyConApp targetCon [], TyConApp targetChoice [], targetResult] <- targetPred
  , TyConApp instancePredCon [TyConApp instanceCon [], TyConApp instanceChoice [], instanceResult] <- instancePred
  , check ["DA.Internal.Desugar", "DA.Internal.Template.Functions"] ["HasExercise"] targetPredCon
  , check ["DA.Internal.Desugar", "DA.Internal.Template.Functions"] ["HasExercise"] instancePredCon
  , let targetConName = tyConName targetCon
  , let instanceConName = tyConName instanceCon
  , let targetChoiceName = tyConName targetChoice
  , let instanceChoiceName = tyConName instanceChoice
  , synEq info targetConName instanceConName
  , synEq info targetChoiceName instanceChoiceName
  , not (eqType targetResult instanceResult)
  = Just $ TriedExercise { target = instanceConName, choice = instanceChoiceName, result = targetResult }
  | TyConApp con [TyConApp target [], TyConApp choice [], result] <- ctev_pred (ctEvidence ct)
  , check ["DA.Internal.Desugar", "DA.Internal.Template.Functions"] ["HasExercise"] con
  = Just $ TriedExercise { target = tyConName target, choice = tyConName choice, result }
  | TyConApp con (_ `Snoc` TyConApp target [] `Snoc` LitTy (StrTyLit methodName) `Snoc` result) <- ctev_pred (ctEvidence ct)
  , check ["DA.Internal.Desugar"] ["HasMethod"] con
  = Just $ TriedImplementMethod { target = tyConName target, method = methodName, result }
  | otherwise
  = Nothing

snoc :: [a] -> Maybe ([a], a)
snoc [] = Nothing
snoc xs = Just (init xs, last xs)
pattern Snoc xs x <- (snoc -> Just (xs, x)) where
  Snoc xs x = xs ++ [x]

printListWithHeader :: SDoc -> SDoc -> [SDoc] -> SDoc
printListWithHeader emptyMsg _ [] = emptyMsg
printListWithHeader _ nonEmptyMsg outs = nonEmptyMsg <+> hcat (punctuate (text ", ") outs)

displayError :: DamlInfo -> DamlError -> Maybe SDoc
displayError info TriedView { target, result }
  | isTemplate info target
  = pure
  $ vcat [ text "Tried to get an interface view of type" <+> pprSynType info result <+> text "from template" <+> pprSynName info target
         , text "Cast template" <+> pprq target <+> text "to an interface before getting its view."
         , printListWithHeader
              (text "Template" <+> pprq target <+> text "does not have any known interface implementations.")
              (text "Template" <+> pprq target <+> text "has the following interfaces:")
              (map pprq (allImplementedInterfaces info target))
         ]
  | isInterface info target
  , Just view <- interfaceView info target
  = pure
  $ text "Tried to get an interface view of type" <+> pprSynType info result <+> text "from interface" <+> pprSynName info target <+> text "but that interface's view is of type" <+> pprSynName info view
  | isInterface info target
  = pure
  $ text "Tried to get an interface view of type" <+> pprSynType info result <+> text "from interface" <+> pprSynName info target <+> text "but that interface's view is not of type" <+> pprSynType info result
  | otherwise
  = pure
  $ text "Tried to get an interface view of type" <+> pprSynType info result <+> text "from type" <+> pprSynName info target <+> text "which is neither an interface nor a template"
displayError info TriedExercise { target, result, choice }
  | Just implementor <- choiceImplementor info choice
  , isInterface info implementor
  , implements info target implementor
  , target /= implementor -- since interfaces implement themselves, we ignore if the target is itself
  = pure
  $ vcat [ text "Tried to exercise a choice" <+> pprSynName info choice <+> text "on" <+> variantNameSyn info target
         , text "The choice" <+> pprq choice <+> text "belongs to" <+> variantNameSyn info implementor <+> text "which" <+> pprq target <+> text "implements."
         , text "Cast" <+> variantName info target <+> text "to" <+> variantName info implementor <+> text "before exercising the choice."
         ]
  | Just implementor <- choiceImplementor info choice
  , Just expectedReturnType <- choiceType info choice
  , not (result `eqType` expectedReturnType)
  = pure
  $ text "Tried to get a result of type" <+> pprSynType info result <+> text "by exercising choice" <+> pprSynName info choice <+> text "on" <+> variantNameSyn info target
   <+> text "but exercising choice" <+> pprq choice <+> text "should return type" <+> pprq expectedReturnType <+> text "instead."
  | otherwise
  = pure
  $ vcat [ text "Tried to exercise a choice" <+> pprSynName info choice <+> text "on" <+> variantNameSyn info target <+> text "but no choice of that name exists on" <+> variantName info target
         , printListWithHeader
              empty
              (text "Choice" <+> pprq choice <+> text "belongs only to the following types:")
              (map (variantNameSyn info) (maybeToList (choiceImplementor info choice)))
         ]
displayError info TriedImplementMethod { target, method, result }
  | [(_, expectedResult)] <- methodOn info method target
  , not (eqType expectedResult result)
  = pure $ text "Implementation of method" <+> pprq method <+> text "on interface" <+> pprSynName info target <+> text "should return" <+> pprq expectedResult <+> text "but instead returns " <+> pprq result
  | [] <- methodOn info method target
  = pure
  $ vcat [ text "Tried to implement method" <+> pprq method <> text ", but interface" <+> pprSynName info target <+> text "does not have a method with that name."
         , printListWithHeader
             empty
             (text "Method" <+> pprq method <+> text "is only a method on the following interfaces:")
             (map (pprq . fst) (methodsNamed info method))
         ]
  | otherwise
  = Nothing
displayError info TriedImplementView { target, triedReturnType, expectedReturnType } =
  pure $ text "Tried to implement a view of type" <+> pprSynType info triedReturnType <+> text "on interface" <+> pprSynName info target
      <> text ", but the definition of interface" <+> pprq target <+> text "requires a view of type" <+> pprSynType info expectedReturnType
displayError info NonExistentFieldAccess { recordType, expectedReturnType, fieldName } =
  pure $ text "Tried to access nonexistent field" <+> pprq fieldName
     <+> text "with type" <+> pprSynType info expectedReturnType
     <+> text "on value of type" <+> pprSynType info recordType
displayError info FieldAccessWrongReturnType { recordType, triedReturnType, expectedReturnType, fieldName } =
  pure $ text "Tried to get field" <+> pprq fieldName
     <+> text "with type" <+> pprSynType info triedReturnType
     <+> text "on value of type" <+> pprSynType info recordType
      <> text ", but that field has type" <+> pprSynType info expectedReturnType
displayError info NumericScaleOutOfBounds { attemptedScale } =
  pure $ text "Tried to define a Numeric with a scale of" <+> ppr attemptedScale <> text ", but only scales between 0 and 37 are supported."
displayError info TriedImplementNonInterface { triedIface }
  | isTemplate info triedIface
  = pure $ text "Tried to make an interface implementation of" <+> pprSynName info triedIface <>
           text ", but" <+> pprq triedIface <+> text "is a template, not an interface."
  | isInterface info triedIface
  = pure $ text "Tried to make an interface implementation of" <+> pprSynName info triedIface <>
           text ", but" <+> pprq triedIface <+> text "does not have an instance of HasInterfaceTypeRep. This should not happen, please contact support."
  | otherwise
  = pure $ text "Tried to make an interface implementation of" <+> pprSynName info triedIface <>
           text ", but" <+> pprq triedIface <+> text "is not an interface."

dedupe :: DamlInfo -> DamlInfo
dedupe (DamlInfo x0 x1 x2 x3 x4 x5 x6) =
  DamlInfo
    x0
    x1
    x2
    (nubSortBy (\(mName, (cName, type_)) -> (mName, cName)) x3)
    (nubSort x4)
    x5
    x6
  where
    nubSortBy :: Ord b => (a -> b) -> [a] -> [a]
    nubSortBy f xs = M.elems $ M.fromList $ map (\x -> (f x, x)) xs

pprq :: Outputable a => a -> SDoc
pprq = quotes . ppr

synEq :: DamlInfo -> Name -> Name -> Bool
synEq info n1 n2 = resolveSynonym info n1 == resolveSynonym info n2

isTemplate, isInterface, isSynonym :: DamlInfo -> Name -> Bool
isTemplate info name = resolveSynonym info name `S.member` templates info
isInterface info name = resolveSynonym info name `S.member` interfaces info
isSynonym info name = resolveSynonym info name `M.member` synonyms info

variantNameSyn :: DamlInfo -> Name -> SDoc
variantNameSyn info name
  | isTemplate info name = text "template" <+> pprSynName info name
  | isInterface info name = text "interface" <+> pprSynName info name
  | otherwise = text "type" <+> pprSynName info name

variantName :: DamlInfo -> Name -> SDoc
variantName info name
  | isTemplate info name = text "template" <+> pprq name
  | isInterface info name = text "interface" <+> pprq name
  | otherwise = text "type" <+> pprq name

allImplementedInterfaces, allImplementingTemplates :: DamlInfo -> Name -> [Name]
allImplementedInterfaces info name = [iface | (tpl, iface) <- implementations info, synEq info name tpl]
allImplementingTemplates info name = [tpl | (tpl, iface) <- implementations info, synEq info name iface]

implements :: DamlInfo -> Name -> Name -> Bool
implements info tpl iface = any (\(t, i) -> synEq info tpl t && synEq info iface i) (implementations info)

choiceImplementor :: DamlInfo -> Name -> Maybe Name
choiceImplementor info name = fst <$> M.lookup (resolveSynonym info name) (choices info)

choiceType :: DamlInfo -> Name -> Maybe Type
choiceType info name = snd <$> M.lookup (resolveSynonym info name) (choices info)

interfaceView :: DamlInfo -> Name -> Maybe Name
interfaceView info name = M.lookup (resolveSynonym info name) (views info)

methodsNamed :: DamlInfo -> FastString -> [(Name, Type)]
methodsNamed info method = [(name, type_) | (m, (name, type_)) <- methods info, m == method]

methodOn :: DamlInfo -> FastString -> Name -> [(Name, Type)]
methodOn info method target =
  [(name, type_) | (m, (name, type_)) <- methods info, m == method, synEq info target name]

resolveSynonym :: DamlInfo -> Name -> Name
resolveSynonym info name =
  case name `M.lookup` synonyms info of
    Just (resolvedName, _) -> resolvedName
    Nothing -> name

-- For unparameterised type aliases, we extract the name and print the alias
pprSynType :: DamlInfo -> Type -> SDoc
pprSynType info (TyConApp (getName -> name) []) = pprSynName info name
pprSynType _ ty = pprq ty

pprSynName :: DamlInfo -> Name -> SDoc
pprSynName info name =
  let synName = resolveSynonym info name
   in if name == synName
        then pprq name
        else pprq name <+> parens (text "Type synonym of" <+> pprq synName)

instance Monoid DamlInfo where
  mempty = DamlInfo S.empty S.empty M.empty [] [] M.empty M.empty

instance Semigroup DamlInfo where
  (<>) (DamlInfo a0 a1 a2 a3 a4 a5 a6) (DamlInfo b0 b1 b2 b3 b4 b5 b6) =
    DamlInfo (a0 P.<> b0) (a1 P.<> b1) (a2 P.<> b2) (a3 P.<> b3) (a4 P.<> b4) (a5 P.<> b5) (a6 P.<> b6)

instance Outputable DamlInfo where
  ppr info =
    hang (text "DamlInfo {") 2 $
    vcat [ text "templates =" <+> ppr (templates info)
         , text "interfaces =" <+> ppr (interfaces info)
         , text "choices =" <+> ppr (choices info)
         , text "methods =" <+> ppr (methods info)
         , text "implementations =" <+> ppr (implementations info)
         , text "views =" <+> ppr (views info)
         , text "synonyms =" <+> ppr (synonyms info)
         , text "}"
         ]

resolveAllSynonyms :: DamlInfo -> DamlInfo
resolveAllSynonyms info@DamlInfo {..} =
  DamlInfo
    { templates = S.map (resolveSynonym info) templates
    , interfaces = S.map (resolveSynonym info) interfaces
    , choices = (fmap . first) (resolveSynonym info) $ M.mapKeys (resolveSynonym info) choices
    , methods = (fmap . second . first) (resolveSynonym info) methods
    , implementations = (fmap . (\f -> bimap f f)) (resolveSynonym info) implementations
    , views = M.foldMapWithKey (M.singleton `on` resolveSynonym info) views
    , synonyms = synonyms
    }

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
      let all_tythings = typeEnvElts (tcg_type_env (env_gbl env)) ++ typeEnvElts (eps_PTE eps)
      let new_info_with_synonyms = extractSynonymsFromTyThings new_info all_tythings
      traceTc "DamlInfo new_info_with_synonyms" $ ppr new_info_with_synonyms

      let finalDamlInfo = resolveAllSynonyms new_info_with_synonyms

      writeMutVar (env_daml env) (Just finalDamlInfo)
      pure finalDamlInfo
    Just info -> pure info

extractDamlInfoFromTyThing :: TyThing -> DamlInfo
extractDamlInfoFromTyThing tything =
  case tything of
    ATyCon tycon ->
      mempty
        { templates = S.fromList $ mapMaybe matchTemplate [tycon]
        , interfaces = S.fromList $ mapMaybe matchInterface [tycon]
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

extractSynonymsFromTyThings :: DamlInfo -> [TyThing] -> DamlInfo
extractSynonymsFromTyThings existing tythings = go existing (mapMaybe getSynonym tythings)
  where
    synonymsToInfo :: [(Name, (Name, DamlSynonym))] -> DamlInfo
    synonymsToInfo syn = mempty { synonyms = M.fromList syn }

    getSynonym :: TyThing -> Maybe (Name, Name)
    getSynonym tything = do
      ATyCon msynonym <- pure tything
      TyConApp out [] <- synTyConRhs_maybe msynonym
      let outName = tyConName out
      pure (tyConName msynonym, outName)

    targetsToSynonyms :: [(Name, Name)]
    targetsToSynonyms = mapMaybe getSynonym tythings

    go :: DamlInfo -> [(Name, Name)] -> DamlInfo
    go info unusedSynonyms =
      let (matching, nonmatching) = partitionEithers $ map categorise unusedSynonyms
          categorise link@(synonym, value)
            | value `S.member` templates info = Left (synonym, (value, TemplateSyn))
            | value `S.member` interfaces info = Left (synonym, (value, InterfaceSyn))
            | value `M.member` choices info = Left (synonym, (value, ChoiceSyn))
            | (==value) `any` views info = Left (synonym, (value, ViewSyn))
            | Just result <- value `M.lookup` synonyms info = Left (synonym, result)
            | otherwise = Right (synonym, value)
      in
      if null matching
         then info
         else go (info P.<> synonymsToInfo matching) nonmatching

extractDamlInfoFromClsInst :: ClsInst -> DamlInfo
extractDamlInfoFromClsInst inst =
  mempty
    { choices = M.fromList $ mapMaybe matchChoice [inst]
    , methods = mapMaybe matchMethod [inst]
    , implementations = mapMaybe matchImplements [inst]
    , views = M.fromList $ mapMaybe matchView [inst]
    }
  where
    matchChoice :: ClsInst -> Maybe (Name, (Name, Type))
    matchChoice clsInst = do
      [contractType, choiceType, returnType] <-
          clsInstMatch "HasExercise" clsInst
      (contractTyCon, []) <- splitTyConApp_maybe contractType
      (choiceTyCon, []) <- splitTyConApp_maybe choiceType
      pure (tyConName choiceTyCon, (tyConName contractTyCon, returnType))

    matchMethod :: ClsInst -> Maybe (FastString, (Name, Type))
    matchMethod clsInst = do
      (_ `Snoc` contractType `Snoc` methodNameType `Snoc` returnType) <-
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

    matchView :: ClsInst -> Maybe (Name, Name)
    matchView clsInst = do
      [ifaceType, viewType] <-
          clsInstMatch "HasInterfaceView" clsInst
      (ifaceTyCon, []) <- splitTyConApp_maybe ifaceType
      (viewTyCon, []) <- splitTyConApp_maybe viewType
      pure (tyConName ifaceTyCon, tyConName viewTyCon)

    clsInstMatch :: String -> ClsInst -> Maybe [Type]
    clsInstMatch targetName clsInst = do
      guard $ similarName targetName (is_cls_nm clsInst)
      pure $ is_tys clsInst

similarName :: String -> Name -> Bool
similarName target name = occNameString (nameOccName name) == target

