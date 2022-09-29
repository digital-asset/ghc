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

import Data.Maybe
import Data.List

check :: NamedThing a => [String] -> String -> a -> Bool
check modules name namedThing
  | Just mod <- moduleNameString . moduleName <$> nameModule_maybe (getName namedThing)
  , mod `elem` modules
  , name == occNameString (getOccName namedThing)
  = True
  | otherwise
  = False

customDamlErrors :: Ct -> TcM (Maybe SDoc)
customDamlErrors ct
  -- TODO: Use PrelNames machinery to match unique names instead of resorting to string matching
  | TyConApp con [TyConApp target [], viewType] <- ctev_pred (ctEvidence ct)
  , check ["DA.Internal.Desugar", "DA.Internal.Interface"] "HasInterfaceView" con
  = pure $ Just
  $ vcat [ text "Tried to get an interface view of type" <+> ppr viewType <+> text "from a non-interface" <+> ppr (tyConName target)
         , text "If" <+> ppr (tyConName target) <+> text "is a template, try casting it using toInterface or toInterfaceContractId"
         ]
  | TyConApp con [TyConApp target [], TyConApp choiceName [], result] <- ctev_pred (ctEvidence ct)
  , check ["DA.Internal.Desugar", "DA.Internal.Template.Functions"] "HasExercise" con
  = pure $ Just
  $ vcat [ text "Tried to exercise a choice" <+> ppr choiceName <+> text "which doesn't exist on" <+> ppr (tyConName target)
         , text "If the choice" <+> ppr choiceName <+> text "belongs to an interface, try casting" <+> ppr (tyConName target) <+> text "using toInterface or toInterfaceContractId"
         ]
  | TyConApp con [TyConApp target [], LitTy (StrTyLit methodName), result] <- ctev_pred (ctEvidence ct)
  , check ["DA.Internal.Desugar"] "HasMethod" con
  = pure $ Just
  $ text "Tried to implement method" <+> ppr methodName <> text ", but interface" <+> ppr (tyConName target) <+> text "does not have a method with that name."
  | otherwise
  = pure Nothing

data DamlVariant = Template Name | Interface Name | Choice Name

data DamlInfo = DamlInfo
  { templates :: [Name]
  , interfaces :: [Name]
  , choices :: [(Name, String)]
  , methods :: [(String, Name)]
  }

data TyConDamlVariant = TyConTemplate Name AlgTyConRhs | TyConInterface Name AlgTyConRhs | TyConChoice Name String

instance Outputable TyConDamlVariant where
  ppr (TyConTemplate name _) = text "TyConTemplate" <+> ppr name
  ppr (TyConInterface name _) = text "TyConInterface" <+> ppr name
  ppr (TyConChoice target name) = text "TyConChoice" <+> ppr target <> text name

extractDamlInfo :: TcGblEnv -> DamlInfo
extractDamlInfo env =
  DamlInfo
    { templates = mapMaybe matchTemplate $ tcg_tcs env
    , interfaces = mapMaybe matchInterface $ tcg_tcs env
    , choices = []
    , methods = []
    }
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

