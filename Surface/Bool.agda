open import Data.Bool using (Bool)

open import Surface.Arith using (Aexp) renaming (compile to acompile)
open import Core.Bool renaming (
    Bexp to CBexp; _≐_ to _c≐_; _≤_ to _c≤_; ¬_ to c¬_; _∧_ to _c∧_;
    𝔹_ to c𝔹_)

module Surface.Bool where

data Bexp : Set where
    𝔹_ : Bool → Bexp

    _≐_ : Aexp → Aexp → Bexp
    _≤_ : Aexp → Aexp → Bexp

    ¬_  : Bexp → Bexp
    _∧_ : Bexp → Bexp → Bexp

    _≠_ : Aexp → Aexp → Bexp
    _≥_ : Aexp → Aexp → Bexp
    _<_ : Aexp → Aexp → Bexp
    _>_ : Aexp → Aexp → Bexp

    _∨_  : Bexp → Bexp → Bexp
    _⇒_ : Bexp → Bexp → Bexp
    _⇔_ : Bexp → Bexp → Bexp

compile : Bexp → CBexp
compile (𝔹 x)      = c𝔹 x
compile (a₁ ≐ a₂)  = acompile a₁ c≐ acompile a₂
compile (a₁ ≤ a₂)  = acompile a₁ c≤ acompile a₂
compile (¬ b)      = c¬ compile b
compile (b₁ ∧ b₂)  = compile b₁ c∧ compile b₂
compile (a₁ ≠ a₂)  = c¬ (acompile a₁ c≐ acompile a₂)
compile (a₁ ≥ a₂)  = c¬ ((ca₁ c≤ ca₂) c∧ (c¬ (ca₁ c≐ ca₂)))
    where
        ca₁ = acompile a₁
        ca₂ = acompile a₂
compile (a₁ < a₂)  = (ca₁ c≤ ca₂) c∧ (c¬ (ca₁ c≐ ca₂))
    where
        ca₁ = acompile a₁
        ca₂ = acompile a₂
compile (a₁ > a₂)  = acompile a₁ c≤ acompile a₂
compile (b₁ ∨  b₂) = c¬ ((c¬ compile b₁) c∧ (c¬ compile b₂))
compile (b₁ ⇒ b₂) = c¬ ((c¬ (cb₁ c∧ cb₂)) c∧ cb₁)
    where
        cb₁ = compile b₁
        cb₂ = compile b₂
compile (b₁ ⇔ b₂) = c¬ ((c¬ (cb₁ c∧ cb₂)) c∧ (c¬ ((c¬ cb₁) c∧ (c¬ cb₂))))
    where
        cb₁ = compile b₁
        cb₂ = compile b₂
