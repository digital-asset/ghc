{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE NoImplicitPrelude #-}

module DA.Internal.Serializable(
    SerializableWitness (..),
    Serializable (..),
  ) where

data SerializableWitness = SerializableWitness

class Serializable a where
    witness :: a -> SerializableWitness -> SerializableWitness
