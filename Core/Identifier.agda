open import Data.String using (String) renaming (_≟_ to _s≟_)

module Core.Identifier where

Id : Set
Id = String

_≟_ = _s≟_
