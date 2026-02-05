{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE NoImplicitPrelude #-}

module DA.Internal.Serializable(
    Serializable (..),
  ) where

class Serializable a where
    serializable :: a -> b -> b
