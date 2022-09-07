{-# LANGUAGE CPP #-}

module TcDaml(
        customDamlErrors
  ) where

import GhcPrelude

import InstEnv
import Outputable
import TcRnTypes
import TyCoRep
import TyCon
import OccName
import PrelNames

customDamlErrors :: Ct -> [ClsInst] -> SDoc -> Maybe SDoc
customDamlErrors ct candidate_insts binds_msg
  | TyConApp con [TyConApp target [], viewType] <- ctev_pred (ctEvidence ct)
  , tyConName con == hasInterfaceViewClassName
  = Just
  $ vcat [ text "Tried to get an interface view of type" <+> ppr viewType <+> text "from a non-interface" <+> ppr (tyConName target)
         , text "If" <+> ppr (tyConName target) <+> text "is a template, try casting it using toInterface or toInterfaceContractId"
         ]
  | TyConApp con [TyConApp target [], TyConApp choiceName [], result] <- ctev_pred (ctEvidence ct)
  , tyConName con == hasExerciseClassName
  = Just
  $ vcat [ text "Tried to exercise a choice" <+> ppr choiceName <+> text "which doesn't exist on" <+> ppr (tyConName target)
         , text "If the choice" <+> ppr choiceName <+> text "belongs to an interface, try casting" <+> ppr (tyConName target) <+> text "using toInterface or toInterfaceContractId"
         ]
  | TyConApp con [TyConApp target [], LitTy (StrTyLit methodName), result] <- ctev_pred (ctEvidence ct)
  , tyConName con == hasMethodClassName
  = Just
  $ vcat [ text "Tried to call method" <+> ppr methodName <+> text "which doesn't exist on" <+> ppr (tyConName target)
         , text "If the method" <+> ppr methodName <+> text "belongs to an interface, try casting" <+> ppr (tyConName target) <+> text "using toInterface or toInterfaceContractId"
         ]
  | otherwise = Nothing

