-- NOTE(jaspervdj): This generates binds when using "deriving (Serializable)" in
-- DAML.  When porting or upgrading this, I would recommend looking at the
-- structure of gen_Show_binds in TcGenDeriv.hs.  I split it into a separate
-- module to make future merges (hopefully) easier.
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

gen_Serializable_binds loc tycon = (unitBag seri_bind, emptyBag)
  where
    seri_arity = 2

    seri_bind = mkRdrFunBindEC
        seri_arity
        id
        (L loc damlSerializableMethod_RDR)
        (map seri_match (tyConDataCons tycon))

    -- For every data constructor in the data type, this generates a case in the
    -- shape of:
    --
    --     seri (DataCon field1 field2 field3) z =
    --         seri field1 (seri field2 (seri field3 z))
    seri_match data_con = mkMatch
        (mkPrefixFunRhs (L loc damlSerializableMethod_RDR))
        [con_pat, nlVarPat z_rdr]
        (foldr
            (nlHsApp . nlHsApp seri . nlHsVar)
            (nlHsVar z_rdr)
            as_needed)
        (noLoc emptyLocalBinds)
      where
         data_con_RDR = getRdrName data_con
         con_arity    = dataConSourceArity data_con
         as_needed    = take con_arity as_rdrs
         con_pat      = parenthesizePat appPrec $ nlConVarPat data_con_RDR as_needed
         seri         = nlHsVar damlSerializableMethod_RDR

    as_rdrs :: [RdrName]
    as_rdrs = [ mkVarUnqual (mkFastString ("a"++show i)) | i <- [(1::Int) .. ] ]
    z_rdr = mkVarUnqual (mkFastString "z")
