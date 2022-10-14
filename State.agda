open import Data.Integer using (ℤ)
open import Relation.Nullary using (yes; no)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)

open import Identifier using (Id; _≟_)

State : Set
State = Id → ℤ

infix 10 _[_↦_]

_[_↦_] : State → Id → ℤ → State
_[_↦_] s id v id' with (id ≟ id')
... | yes _ = v
... | no  _ = s id'

insert≡ : ∀ (s : State) → ∀ (id : Id) → ∀ (z : ℤ) → (s [ id ↦ z ]) id ≡ z
insert≡ s id z with id ≟ id
... | yes refl  = refl
... | no ¬id≡id = contradiction refl ¬id≡id

insert¬≡ : ∀ (s : State) → ∀ (id id' : Id) → ¬ (id ≡ id') → ∀ (z : ℤ)
         → (s [ id' ↦ z ]) id ≡ s id
insert¬≡ s id id' ¬id≡id' z with id' ≟ id
... | yes refl = contradiction refl ¬id≡id'
... | no _     = refl
