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

import Data.Maybe
import Data.List
import qualified Prelude as P ((<>))

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
  env <- getEnv
  eps <- readMutVar $ hsc_EPS $ env_top env
  let gblEnvDamlInfo = extractDamlInfoFromGblEnv $ env_gbl env
  let epsDamlInfo = extractDamlInfoFromEPS eps
  let info = gblEnvDamlInfo `mappend` epsDamlInfo
  traceTc "TcGblEnv info" (ppr gblEnvDamlInfo)
  traceTc "TcGblEnv info" (ppr epsDamlInfo)
  pure $ fmap (displayError info) (customDamlError ct)

data DamlError
  = TriedView { target :: Name, result :: Type }
  | TriedExercise { target :: Name, choice :: Name, result :: Type }
  | TriedCall { target :: Name, method :: FastString, result :: Type }

customDamlError :: Ct -> Maybe DamlError
customDamlError ct
  | TyConApp con [TyConApp target [], viewType] <- ctev_pred (ctEvidence ct)
  , check ["DA.Internal.Desugar", "DA.Internal.Interface"] "HasInterfaceView" con
  = Just $ TriedView { target = tyConName target, result = viewType }
  | TyConApp con [TyConApp target [], TyConApp choice [], result] <- ctev_pred (ctEvidence ct)
  , check ["DA.Internal.Desugar", "DA.Internal.Template.Functions"] "HasExercise" con
  = Just $ TriedExercise { target = tyConName target, choice = tyConName choice, result = result }
  | TyConApp con [TyConApp target [], LitTy (StrTyLit methodName), result] <- ctev_pred (ctEvidence ct)
  , check ["DA.Internal.Desugar"] "HasMethod" con
  = Just $ TriedCall { target = tyConName target, method = methodName, result = result }
  | otherwise
  = Nothing

displayError :: DamlInfo -> DamlError -> SDoc
displayError info TriedView { target = target, result = result }
  | isTemplate info target
  = vcat [ text "Tried to get an interface view of type" <+> ppr result <+> text "from template" <+> ppr target
         , text "Cast template" <+> ppr target <+> text "to an interface before getting its view."
         , text "Known interfaces for template" <+> ppr target <+> text "include:"
         , hcat (punctuate (text ", ") (map ppr (allImplementedInterfaces info target)))
         ]
  | isInterface info target
  = text "Tried to get an interface view of type" <+> ppr result <+> text "from interface" <+> ppr target <+> text "but that interface's view is not of that type"
  | otherwise
  = text "Tried to get an interface view of type" <+> ppr result <+> text "from type" <+> ppr target <+> text "which is neither an interface nor a template"
displayError info TriedExercise { target = target, result = result, choice = choice }
  | [implementor] <- choiceImplementor info choice
  , isInterface info implementor
  , implements info target implementor
  = vcat [ text "Tried to exercise a choice" <+> ppr choice <+> text "on" <+> ppr target
         , text "This choice" <+> ppr choice <+> text "belongs to interface" <+> ppr implementor <+> text "which" <+> ppr target <+> text "implements."
         , text "Cast template" <+> ppr target <+> text "to interface" <+> ppr implementor <+> text "before exercising the choice."
         ]
  | [implementor] <- choiceImplementor info choice
  = vcat [ text "Tried to exercise a choice" <+> ppr choice <+> text "on" <+> ppr target <+> text "but no choice of that name exists on" <+> ppr target
         , text "This choice" <+> ppr choice <+> text "belongs to" <+> variantName info implementor <+> ppr implementor <+> text "instead."
         ]
  | otherwise
  = text "Tried to exercise a choice" <+> ppr choice <+> text "on" <+> ppr target <+> text "but no choice of that name exists on" <+> ppr target
displayError info TriedCall { target = target, method = method, result = result }
  = text "Tried to implement method" <+> ppr method <> text ", but interface" <+> ppr target <+> text "does not have a method with that name."

data DamlVariant = Template Name | Interface Name | Choice Name

data DamlInfo = DamlInfo
  { templates :: [Name]
  , interfaces :: [Name]
  , choices :: [(Name, Name)]
  , methods :: [(FastString, Type)]
  , implementations :: [(Name, Name)]
  }

isTemplate info name = name `elem` templates info
isInterface info name = name `elem` interfaces info
variantName info name
  | isTemplate info name = text "template"
  | isInterface info name = text "interface"
  | otherwise = text "type"
allImplementedInterfaces info name = [iface | (tpl, iface) <- implementations info, name == tpl]
allImplementingTemplates info name = [tpl | (tpl, iface) <- implementations info, name == iface]
implements info tpl iface = (tpl, iface) `elem` implementations info
choiceImplementor info name = [tplOrIface | (tplOrIface, choice) <- choices info, name == choice]

instance Monoid DamlInfo where
  mempty = DamlInfo [] [] [] [] []

instance Semigroup DamlInfo where
  (<>) (DamlInfo a0 a1 a2 a3 a4) (DamlInfo b0 b1 b2 b3 b4) =
    DamlInfo (a0 P.<> b0) (a1 P.<> b1) (a2 P.<> b2) (a3 P.<> b3) (a4 P.<> b4)

instance Outputable DamlInfo where
  ppr info =
    hang (text "DamlInfo {") 2 $
    vcat [ text "templates:" <+> ppr (templates info)
         , text "interfaces:" <+> ppr (interfaces info)
         , text "choices:" <+> ppr (choices info)
         , text "methods:" <+> ppr (methods info)
         , text "implementations:" <+> ppr (implementations info)
         ]

extractDamlInfoFromGblEnv :: TcGblEnv -> DamlInfo
extractDamlInfoFromGblEnv env =
  foldMap extractDamlInfoFromTyThing (typeEnvElts $ tcg_type_env env) `mappend`
    foldMap extractDamlInfoFromClsInst (instEnvElts $ tcg_inst_env env)

extractDamlInfoFromEPS :: ExternalPackageState -> DamlInfo
extractDamlInfoFromEPS eps =
  foldMap extractDamlInfoFromTyThing (typeEnvElts $ eps_PTE eps) `mappend`
    foldMap extractDamlInfoFromClsInst (instEnvElts $ eps_inst_env eps)

extractDamlInfoFromTyThing :: TyThing -> DamlInfo
extractDamlInfoFromTyThing tything =
  case tything of
    AnId id ->
      mempty
        { methods = mapMaybe matchMethod [id]
        , implementations = mapMaybe matchImplements [id]
        , choices = mapMaybe matchChoice [id]
        }
    ATyCon tycon ->
      mempty
        { templates = mapMaybe matchTemplate [tycon]
        , interfaces = mapMaybe matchInterface [tycon]
        }
    _ -> mempty
  where
    matchTemplate, matchInterface :: TyCon -> Maybe Name
    matchTemplate = tyconWithConstraint ghcTypesDamlTemplate
    matchInterface = tyconWithConstraint ghcTypesDamlInterface

    tyconWithConstraint :: RdrName -> TyCon -> Maybe Name
    tyconWithConstraint targetName tycon
      | isAlgTyCon tycon
      , let isMatchingLoneConstraint type_
              | Just (loneConstraint, []) <- splitTyConApp_maybe type_
              , similarName targetName (tyConName loneConstraint)
              = True
              | otherwise
              = False
      , any isMatchingLoneConstraint (tyConStupidTheta tycon)
      = Just $ tyConName tycon
      | otherwise
      = Nothing

    matchChoice :: Id -> Maybe (Name, Name)
    matchChoice identifier
      | TyConApp headTyCon [contractType, choiceType, returnType] <- varType identifier
      , similarName (qualifyDesugar (mkClsOcc "HasExercise")) (tyConName headTyCon)
      , Just (contractTyCon, []) <- splitTyConApp_maybe contractType
      , Just (choiceTyCon, []) <- splitTyConApp_maybe choiceType
      = Just (tyConName contractTyCon, tyConName choiceTyCon)
      | otherwise
      = Nothing

    matchMethod :: Id -> Maybe (FastString, Type)
    matchMethod identifier
      | TyConApp headTyCon [contractType, methodNameType, returnType] <- varType identifier
      , similarName (qualifyDesugar (mkClsOcc "HasMethod")) (tyConName headTyCon)
      , LitTy (StrTyLit methodName) <- methodNameType
      = Just (methodName, contractType)
      | otherwise
      = Nothing

    matchImplements :: Id -> Maybe (Name, Name)
    matchImplements identifier
      | TyConApp headTyCon [templateType, interfaceType] <- varType identifier
      , similarName (qualifyDesugar (mkClsOcc "ToInterface")) (tyConName headTyCon)
      , Just (templateTyCon, []) <- splitTyConApp_maybe templateType
      , Just (interfaceTyCon, []) <- splitTyConApp_maybe interfaceType
      = Just (tyConName templateTyCon, tyConName interfaceTyCon)
      | otherwise
      = Nothing

    isMatchingLoneConstraint :: RdrName -> IfaceType -> Bool
    isMatchingLoneConstraint targetName type_
      | IfaceTyConApp (IfaceTyCon tyConName _info) IA_Nil <- type_
      , similarName targetName tyConName
      = True
      | otherwise
      = False

extractDamlInfoFromClsInst :: ClsInst -> DamlInfo
extractDamlInfoFromClsInst inst =
  mempty
    { choices = mapMaybe matchChoice [inst]
    , methods = mapMaybe matchMethod [inst]
    , implementations = mapMaybe matchImplements [inst]
    }
  where
    matchChoice :: ClsInst -> Maybe (Name, Name)
    matchChoice clsInst
      | Just [contractType, choiceType, returnType] <-
          clsInstMatch (qualifyDesugar (mkClsOcc "HasExercise")) clsInst
      , Just (contractTyCon, []) <- splitTyConApp_maybe contractType
      , Just (choiceTyCon, []) <- splitTyConApp_maybe choiceType
      = Just (tyConName contractTyCon, tyConName choiceTyCon)
      | otherwise
      = Nothing

    matchMethod :: ClsInst -> Maybe (FastString, Type)
    matchMethod clsInst
      | Just [contractType, methodNameType, returnType] <-
          clsInstMatch (qualifyDesugar (mkClsOcc "HasMethod")) clsInst
      , Just (StrTyLit methodName) <- isLitTy methodNameType
      = Just (methodName, contractType)
      | otherwise
      = Nothing

    matchImplements :: ClsInst -> Maybe (Name, Name)
    matchImplements clsInst
      | Just [templateType, interfaceType] <-
          clsInstMatch (qualifyDesugar (mkClsOcc "ToInterface")) clsInst
      , Just (templateTyCon, []) <- splitTyConApp_maybe templateType
      , Just (interfaceTyCon, []) <- splitTyConApp_maybe interfaceType
      = Just (tyConName templateTyCon, tyConName interfaceTyCon)
      | otherwise
      = Nothing

    clsInstMatch :: RdrName -> ClsInst -> Maybe [Type]
    clsInstMatch rdrName clsInst
      | similarName rdrName (is_cls_nm clsInst)
      = Just $ is_tys clsInst
      | otherwise
      = Nothing

similarName :: RdrName -> Name -> Bool
similarName (Qual targetModuleName targetOccName) name
  | Just actualModule <- nameModule_maybe name
  , moduleName actualModule == targetModuleName
  , nameOccName name == targetOccName
  = True
similarName _ _ = False

