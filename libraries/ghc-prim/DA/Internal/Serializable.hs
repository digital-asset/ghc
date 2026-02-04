{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE NoImplicitPrelude #-}

module DA.Internal.Serializable(
    Serializable (..),
  ) where

data Witness

class Serializable a where
    witness :: a -> Witness -> Witness
