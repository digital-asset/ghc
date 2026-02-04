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

gen_Serializable_binds loc tycon = (unitBag witness_bind, emptyBag)
  where
    witness_arity = 2

    witness_bind = mkRdrFunBindEC
        witness_arity
        id
        (L loc damlSerializableWitness_RDR)
        (map witness_match (tyConDataCons tycon))

    -- For every data constructor in the data type, this generates a case in the
    -- shape of:
    --
    --     witness (DataCon field1 field2 field3) z =
    --         witness field1 (witness field2 (witness field3 z))
    witness_match data_con = mkMatch
        (mkPrefixFunRhs (L loc damlSerializableWitness_RDR))
        [con_pat, nlVarPat z_rdr]
        (foldr
            (nlHsApp . nlHsApp witness . nlHsVar)
            (nlHsVar z_rdr)
            as_needed)
        (noLoc emptyLocalBinds)
      where
         data_con_RDR = getRdrName data_con
         con_arity    = dataConSourceArity data_con
         as_needed    = take con_arity as_rdrs
         con_pat      = parenthesizePat appPrec $ nlConVarPat data_con_RDR as_needed
         witness      = nlHsVar damlSerializableWitness_RDR

    as_rdrs :: [RdrName]
    as_rdrs = [ mkVarUnqual (mkFastString ("a"++show i)) | i <- [(1::Int) .. ] ]
    z_rdr = mkVarUnqual (mkFastString "z")
