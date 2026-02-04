-- This generates binds when using "deriving (Serializable)" in DAML.
-- It is mostly similar to gen_Show_binds in TcGenDeriv.hs.
-- I split it into a separate module to make future merges (hopefully) easier.
{-# LANGUAGE GADTs #-}
module TcGenDamlSerializable
    ( gen_Serializable_binds
    ) where

import GhcPrelude

import Bag
import BasicTypes
import DataCon
import FastString
import HsSyn
import PrelNames
import RdrName
import SrcLoc
import TcGenDeriv
import TyCon

gen_Serializable_binds :: SrcSpan -> TyCon
                       -> (LHsBinds GhcPs, BagDerivStuff)

gen_Serializable_binds loc tycon
  = (unitBag witness_bind, emptyBag)
  where
    witness_rdr = damlSerializableWitness_RDR
    data_cons = tyConDataCons tycon
    -- witness_bind = mkFunBindEC 1 loc damlSerializableWitness_RDR id (map pats_etc data_cons)

    witness_bind = mkRdrFunBindEC 1 id (L loc witness_rdr)
        [ mkMatch (mkPrefixFunRhs (L loc witness_rdr))
                                (map (parenthesizePat appPrec) p) e
                                (noLoc emptyLocalBinds)
        | (p,e) <- map pats_etc data_cons
        ]

    {-
    pats_etc data_con =
     ([con_pat], nlHsApp
         (nlHsVar (getRdrName mconcatName))
         (nlList $ map (nlHsApp witness . nlHsVar) as_needed))
         -}

    pats_etc data_con =
         ([con_pat, nlVarPat z_rdr], foldr
             (\v expr -> (nlHsApp (nlHsApp witness (nlHsVar v)) expr))
             (nlHsVar z_rdr)
             as_needed)
      where
         data_con_RDR  = getRdrName data_con
         con_arity     = dataConSourceArity data_con
         as_needed     = take con_arity as_RDRs
         con_pat       = nlConVarPat data_con_RDR as_needed
         witness       = nlHsVar witness_rdr

    z_rdr = mkVarUnqual (mkFastString "z")

    as_RDRs :: [RdrName]
    as_RDRs = [ mkVarUnqual (mkFastString ("a"++show i)) | i <- [(1::Int) .. ] ]
