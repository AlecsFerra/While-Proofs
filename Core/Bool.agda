module Core.Bool where

open import Data.Bool using (Bool; true; false; not) renaming (_∧_ to _b∧_)
open import Data.Integer using (_≟_; _≤?_)
open import Relation.Nullary using (Dec; yes; no)

open import Core.State using (State)
open import Core.Arith using (Aexp; 𝓐〚_〛_)

infix 10 𝔹_
infix  4 _≤_ _≐_
infix  8 ¬_
infixr 8 _∧_

data Bexp : Set where
    𝔹_ : Bool → Bexp

    _≐_ : Aexp → Aexp → Bexp
    _≤_ : Aexp → Aexp → Bexp

    ¬_  : Bexp → Bexp
    _∧_ : Bexp → Bexp → Bexp

𝓑〚_〛_ : Bexp → State → Bool
𝓑〚 𝔹 b 〛     s = b
𝓑〚 n₁ ≐ n₂ 〛 s with 𝓐〚 n₁ 〛 s ≟ 𝓐〚 n₂ 〛 s
... | yes _ = true
... | no  _ = false
𝓑〚 n₁ ≤ n₂ 〛 s with 𝓐〚 n₁ 〛 s ≤? 𝓐〚 n₂ 〛 s
... | yes _ = true
... | no  _ = false
𝓑〚 ¬ b 〛     s = not (𝓑〚 b 〛 s)
𝓑〚 b₁ ∧ b₂ 〛 s = 𝓑〚 b₁ 〛 s b∧ 𝓑〚 b₂ 〛 s
