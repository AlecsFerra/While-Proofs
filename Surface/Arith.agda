open import Data.Integer using (ℤ) renaming (
    +_ to ℤ+; _+_ to _ℤ+_; _-_ to _ℤ-_; _*_ to _ℤ*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Identifier using (Id)
open import Core.State using (State)
open import Core.Arith using () renaming (
    Aexp to CAexp; `_ to c`_; ℤ_ to cℤ_; _+_ to _c+_;
    _-_ to _c-_; _*_ to _c*_; 𝓐〚_〛_ to c𝓐〚_〛_)

module Surface.Arith where

data Aexp : Set where
    `_ : Id → Aexp
    ℤ_ : ℤ  → Aexp

    _+_ : Aexp → Aexp → Aexp
    _-_ : Aexp → Aexp → Aexp
    _*_ : Aexp → Aexp → Aexp

    -_  : Aexp → Aexp

𝓐〚_〛_ : Aexp → State → ℤ
𝓐〚 ` x 〛     s = s x
𝓐〚 ℤ x 〛     s = x
𝓐〚 a₁ + a₂ 〛 s = 𝓐〚 a₁ 〛 s ℤ+ 𝓐〚 a₂ 〛 s
𝓐〚 a₁ - a₂ 〛 s = 𝓐〚 a₁ 〛 s ℤ- 𝓐〚 a₂ 〛 s
𝓐〚 a₁ * a₂ 〛 s = 𝓐〚 a₁ 〛 s ℤ* 𝓐〚 a₂ 〛 s
𝓐〚 - a 〛     s = ℤ+ 0 ℤ- 𝓐〚 a 〛 s

compile : Aexp → CAexp
compile (` x)     = c` x
compile (ℤ n)     = cℤ n
compile (a₁ + a₂) = compile a₁ c+ compile a₂
compile (a₁ - a₂) = compile a₁ c- compile a₂
compile (a₁ * a₂) = compile a₁ c* compile a₂
compile (- a)     = cℤ ℤ+ 0    c- compile a

compile≡eval : (s : State) → (a : Aexp)
             → 𝓐〚 a 〛 s ≡ c𝓐〚 compile a 〛 s
compile≡eval s (` x)     = refl
compile≡eval s (ℤ x)     = refl
compile≡eval s (a₁ + a₂) rewrite compile≡eval s a₁
                         |       compile≡eval s a₂
                         = refl
compile≡eval s (a₁ - a₂) rewrite compile≡eval s a₁
                         |       compile≡eval s a₂
                         = refl
compile≡eval s (a₁ * a₂) rewrite compile≡eval s a₁
                         |       compile≡eval s a₂
                         = refl
compile≡eval s (- a)     rewrite compile≡eval s a
                         = refl
