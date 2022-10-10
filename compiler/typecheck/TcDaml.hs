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
  traceTc "TcGblEnv info" (ppr $ extractDamlInfoFromGblEnv $ env_gbl env)
  eps <- readMutVar $ hsc_EPS $ env_top env
  traceTc "TcGblEnv info" (ppr $ extractDamlInfoFromEPS eps)
  customDamlErrorsPure <$> getGblEnv <*> pure ct

customDamlErrorsPure :: TcGblEnv -> Ct -> Maybe SDoc
customDamlErrorsPure env ct
  -- TODO: Use PrelNames machinery to match unique names instead of resorting to string matching
  | TyConApp con [TyConApp target [], viewType] <- ctev_pred (ctEvidence ct)
  , check ["DA.Internal.Desugar", "DA.Internal.Interface"] "HasInterfaceView" con
  = Just
  $ vcat [ text "Tried to get an interface view of type" <+> ppr viewType <+> text "from a non-interface" <+> ppr (tyConName target)
         , text "If" <+> ppr (tyConName target) <+> text "is a template, try casting it using toInterface or toInterfaceContractId"
         ]
  | TyConApp con [TyConApp target [], TyConApp choiceName [], result] <- ctev_pred (ctEvidence ct)
  , check ["DA.Internal.Desugar", "DA.Internal.Template.Functions"] "HasExercise" con
  = Just
  $ vcat [ text "Tried to exercise a choice" <+> ppr choiceName <+> text "which doesn't exist on" <+> ppr (tyConName target)
         , text "If the choice" <+> ppr choiceName <+> text "belongs to an interface, try casting" <+> ppr (tyConName target) <+> text "using toInterface or toInterfaceContractId"
         ]
  | TyConApp con [TyConApp target [], LitTy (StrTyLit methodName), result] <- ctev_pred (ctEvidence ct)
  , check ["DA.Internal.Desugar"] "HasMethod" con
  = Just
  $ text "Tried to implement method" <+> ppr methodName <> text ", but interface" <+> ppr (tyConName target) <+> text "does not have a method with that name."
  | otherwise
  = Nothing

data DamlVariant = Template Name | Interface Name | Choice Name

data DamlInfo = DamlInfo
  { templates :: [Name]
  , interfaces :: [Name]
  , choices :: [(Name, Name)]
  , methods :: [(FastString, Type)]
  , implements :: [(Type, Type)]
  }

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
         , text "implements:" <+> ppr (implements info)
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
        , implements = mapMaybe matchImplements [id]
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

    matchImplements :: Id -> Maybe (Type, Type)
    matchImplements identifier
      | TyConApp headTyCon [templateType, interfaceType] <- varType identifier
      , similarName (qualifyDesugar (mkClsOcc "ToInterface")) (tyConName headTyCon)
      = Just (templateType, interfaceType)
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
    , implements = mapMaybe matchImplements [inst]
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

    matchImplements :: ClsInst -> Maybe (Type, Type)
    matchImplements clsInst
      | Just [template, interface] <-
          clsInstMatch (qualifyDesugar (mkClsOcc "ToInterface")) clsInst
      = Just (template, interface)
      | otherwise
      = Nothing

    clsInstMatch :: RdrName -> ClsInst -> Maybe [Type]
    clsInstMatch rdrName clsInst
      | similarName rdrName (is_cls_nm clsInst)
      = Just $ is_tys clsInst
      | otherwise
      = Nothing

addDamlTypesToGblEnv :: [LTyClDecl GhcRn] -> TcGblEnv -> TcGblEnv
addDamlTypesToGblEnv tyClDecls env@(TcGblEnv { tcg_daml_templates = templates
                                             , tcg_daml_interfaces = interfaces
                                             , tcg_daml_choices = choices }) =
  let (newTemplates, newInterfaces, newChoices) = extractDamlTypes tyClDecls
  in
  env { tcg_daml_templates  = templates ++ newTemplates
      , tcg_daml_interfaces = interfaces ++ newInterfaces
      , tcg_daml_choices    = choices ++ newChoices
      }

extractDamlTypes :: [LTyClDecl GhcRn] -> ([Name], [Name], [Name])
extractDamlTypes = splitVariants . mapMaybe extractDamlType
  where
    splitVariants :: [DamlVariant] -> ([Name], [Name], [Name])
    splitVariants = foldMap $ \x -> case x of
                                     Template a -> ([a], mempty, mempty)
                                     Interface a -> (mempty, [a], mempty)
                                     Choice a -> (mempty, mempty, [a])

extractDamlType :: LTyClDecl GhcRn -> Maybe DamlVariant
extractDamlType (L _ DataDecl { tcdLName = L _ name, tcdDataDefn = HsDataDefn { dd_ctxt = L _ contextTypes } })
  | any (isConstraint ghcTypesDamlInterface) contextTypes
  = Just (Interface name)
  | any (isConstraint ghcTypesDamlTemplate) contextTypes
  = Just (Template name)
  where
    isConstraint :: RdrName -> LHsType GhcRn -> Bool
    isConstraint rdrName (L _ (HsTyVar _ _ (L _ loneConstraint))) =
      similarName rdrName loneConstraint
    isConstraint _ _ = False
extractDamlType _ = Nothing

similarName :: RdrName -> Name -> Bool
similarName (Qual targetModuleName targetOccName) name
  | Just actualModule <- nameModule_maybe name
  , moduleName actualModule == targetModuleName
  , nameOccName name == targetOccName
  = True
similarName _ _ = False

