open import Data.Bool using (Bool; not; if_then_else_; true; false) renaming (
    _∧_ to _b∧_; _∨_ to _b∨_)
open import Data.Bool.Properties using (∧-comm)
open import Data.Integer using (_≟_; _≤?_; _<?_; ℤ) renaming (_<_ to _b<_)
open import Data.Integer.Properties using (n≮n; <⇒≤; ≤∧≢⇒<)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc) renaming (
    _≤_ to _b≤_; _<?_ to _b<?_; _≤?_ to _b≤?_; _≟_ to _b≟_)
open import Relation.Nullary.Negation using (contradiction)

open import Surface.Arith using (Aexp; 𝓐〚_〛_) renaming (
    compile to acompile; compile≡eval to acompile≡eval)
open import Core.Arith using () renaming (𝓐〚_〛_ to c𝓐〚_〛_)
open import Core.Bool using () renaming (
    Bexp to CBexp; _≐_ to _c≐_; _≤_ to _c≤_; ¬_ to c¬_; _∧_ to _c∧_;
    𝔹_ to c𝔹_; 𝓑〚_〛_ to c𝓑〚_〛_)
open import Core.State using (State)

module Surface.Bool where

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

    _≠_ : Aexp → Aexp → Bexp
    _≥_ : Aexp → Aexp → Bexp
    _<_ : Aexp → Aexp → Bexp
    _>_ : Aexp → Aexp → Bexp

    _∨_  : Bexp → Bexp → Bexp
    _⇒_ : Bexp → Bexp → Bexp
    _⇔_ : Bexp → Bexp → Bexp

𝓑〚_〛_ : Bexp → State → Bool
𝓑〚 𝔹 x 〛      s = x
𝓑〚 a₁ ≐ a₂ 〛  s = ⌊ 𝓐〚 a₁ 〛 s ≟ 𝓐〚 a₂ 〛 s ⌋
𝓑〚 a₁ ≤ a₂ 〛  s = ⌊ 𝓐〚 a₁ 〛 s ≤? 𝓐〚 a₂ 〛 s ⌋
𝓑〚 ¬ b 〛      s = not (𝓑〚 b 〛 s)
𝓑〚 b₁ ∧ b₂ 〛  s = 𝓑〚 b₁ 〛 s b∧ 𝓑〚 b₂ 〛 s
𝓑〚 a₁ ≠ a₂ 〛  s = not ⌊ 𝓐〚 a₁ 〛 s ≟ 𝓐〚 a₂ 〛 s ⌋
𝓑〚 a₁ ≥ a₂ 〛  s = not ⌊ 𝓐〚 a₁ 〛 s <? 𝓐〚 a₂ 〛 s ⌋
𝓑〚 a₁ < a₂ 〛  s = ⌊ 𝓐〚 a₁ 〛 s <? 𝓐〚 a₂ 〛 s ⌋
𝓑〚 a₁ > a₂ 〛  s = not ⌊ 𝓐〚 a₁ 〛 s ≤? 𝓐〚 a₂ 〛 s ⌋
𝓑〚 b₁ ∨  b₂ 〛 s = 𝓑〚 b₁ 〛 s b∨ 𝓑〚 b₂ 〛 s
𝓑〚 b₁ ⇒ b₂ 〛 s = if 𝓑〚 b₁ 〛 s then 𝓑〚 b₂ 〛 s else true
𝓑〚 b₁ ⇔ b₂ 〛 s = if 𝓑〚 b₁ 〛 s then 𝓑〚 b₂ 〛 s else not (𝓑〚 b₂ 〛 s)

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
compile (a₁ > a₂)  = c¬ (acompile a₁ c≤ acompile a₂)
compile (b₁ ∨  b₂) = c¬ ((c¬ compile b₁) c∧ (c¬ compile b₂))
compile (b₁ ⇒ b₂) = c¬ ((c¬ (cb₁ c∧ cb₂)) c∧ cb₁)
    where
        cb₁ = compile b₁
        cb₂ = compile b₂
compile (b₁ ⇔ b₂) = c¬ ((c¬ (cb₁ c∧ cb₂)) c∧ (c¬ ((c¬ cb₁) c∧ (c¬ cb₂))))
    where
        cb₁ = compile b₁
        cb₂ = compile b₂

private
    α : ∀ (a b : Bool) → a b∨ b ≡ not (not a b∧ not b)
    α false false = refl
    α false true  = refl
    α true  false = refl
    α true  true  = refl

    β : ∀ (a b : Bool) → (if a then b else true) ≡ not (not (a b∧ b) b∧ a)
    β false false = refl
    β false true  = refl
    β true  false = refl
    β true  true  = refl

    γ : ∀ (a b : Bool)
      → (if a then b else not b) ≡ not (not (a b∧ b) b∧ not (not a b∧ not b))
    γ false false = refl
    γ false true  = refl
    γ true  false = refl
    γ true  true  = refl


    δ : (a b : ℤ) → ⌊ a <? b ⌋ ≡ (⌊ a ≤? b ⌋) b∧ (not (⌊ a ≟ b ⌋))
    δ a b with a <? b | a ≤? b | a ≟ b
    ... | yes a<b | _       | yes refl = contradiction a<b n≮n
    ... | yes _   | yes _   | no _     = refl
    ... | yes a<b | no a≰b  | no _     = contradiction (<⇒≤ a<b) a≰b
    ... | no  _   | i       | yes refl rewrite ∧-comm ⌊ i ⌋ false
                                       = refl
    ... | no  _   | no  _   | no _     = refl
    ... | no  a≮b | yes a≤b | no a≠b   = contradiction (≤∧≢⇒< a≤b a≠b) a≮b


compile≡eval : (s : State) → (b : Bexp)
             → 𝓑〚 b 〛 s ≡ c𝓑〚 compile b 〛 s
compile≡eval s (𝔹 x)      = refl
compile≡eval s (a₁ ≐ a₂)  rewrite acompile≡eval s a₁
                          |       acompile≡eval s a₂
                          = refl
compile≡eval s (a₁ ≤ a₂)  rewrite acompile≡eval s a₁
                          |       acompile≡eval s a₂
                          = refl
compile≡eval s (¬ b)      rewrite compile≡eval s b
                          = refl
compile≡eval s (b₁ ∧ b₂)  rewrite compile≡eval s b₁
                          |       compile≡eval s b₂
                          = refl
compile≡eval s (a₁ ≠ a₂)  rewrite acompile≡eval s a₁
                          |       acompile≡eval s a₂
                          = refl
compile≡eval s (a₁ ≥ a₂)  rewrite acompile≡eval s a₁
                          |       acompile≡eval s a₂
                          |       δ (c𝓐〚 acompile a₁ 〛 s) (c𝓐〚 acompile a₂ 〛 s)
                          = refl
compile≡eval s (a₁ < a₂)  rewrite acompile≡eval s a₁
                          |       acompile≡eval s a₂
                          |       δ (c𝓐〚 acompile a₁ 〛 s) (c𝓐〚 acompile a₂ 〛 s)
                          = refl
compile≡eval s (a₁ > a₂)  rewrite acompile≡eval s a₁
                          |       acompile≡eval s a₂
                          = refl
compile≡eval s (b₁  ∨ b₂) rewrite compile≡eval s b₁
                          |       compile≡eval s b₂
                          |       α (c𝓑〚 compile b₁ 〛 s) (c𝓑〚 compile b₂ 〛 s)
                          = refl
compile≡eval s (b₁ ⇒ b₂) rewrite compile≡eval s b₁
                          |       compile≡eval s b₂
                          |       β (c𝓑〚 compile b₁ 〛 s) (c𝓑〚 compile b₂ 〛 s)
                          = refl
compile≡eval s (b₁ ⇔ b₂) rewrite compile≡eval s b₁
                          |       compile≡eval s b₂
                          |       γ (c𝓑〚 compile b₁ 〛 s) (c𝓑〚 compile b₂ 〛 s)
                          = refl
