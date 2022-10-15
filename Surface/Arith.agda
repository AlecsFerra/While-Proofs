open import Data.Integer using (ℤ) renaming (+_ to ℤ+)

open import Core.Identifier using (Id)
open import Core.Arith renaming (
    Aexp to CAexp; `_ to c`_; ℤ_ to cℤ_; _+_ to _c+_;
    _-_ to _c-_; _*_ to _c*_)

module Surface.Arith where

data Aexp : Set where
    `_ : Id → Aexp
    ℤ_ : ℤ  → Aexp

    _+_ : Aexp → Aexp → Aexp
    _-_ : Aexp → Aexp → Aexp
    _*_ : Aexp → Aexp → Aexp

    -_  : Aexp → Aexp

compile : Aexp → CAexp
compile (` x)     = c` x
compile (ℤ n)     = cℤ n
compile (a₁ + a₂) = compile a₁ c+ compile a₂
compile (a₁ - a₂) = compile a₁ c- compile a₂
compile (a₁ * a₂) = compile a₁ c* compile a₂
compile (- a)     = cℤ ℤ+ 0    c- compile a
