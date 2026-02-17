{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE NoImplicitPrelude #-}

module DA.Internal.Serializable
    ( Serializable (..),
    ) where

class Serializable a where
    -- We want to avoid using any concrete datatypes (e.g. unit "()") since that
    -- compilicates the dependencies in between the prim modules.  We also want
    -- to avoid declaring our own datatype, since then we would just need to
    -- strip that out again.
    serializable :: a -> b -> b
