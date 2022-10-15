module Core.Arith where

open import Data.Integer using (ℤ) renaming (_+_ to _ℤ+_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Core.Identifier using (Id; _≟_)
open import Core.State using (State; insert≡; insert¬≡) renaming (_[_↦_] to _s[_↦_])

infix 10 `_ ℤ_

infixl 6 _+_ _-_
infixl 7 _*_

data Aexp : Set where
    `_ : Id → Aexp
    ℤ_ : ℤ  → Aexp

    _+_ : Aexp → Aexp → Aexp
    _-_ : Aexp → Aexp → Aexp
    _*_ : Aexp → Aexp → Aexp

𝓐〚_〛_ : Aexp → State → ℤ
𝓐〚 ` x 〛     s = s x
𝓐〚 ℤ n 〛     s = n
𝓐〚 a₁ + a₂ 〛 s = 𝓐〚 a₁ 〛 s ℤ+ 𝓐〚 a₂ 〛 s
𝓐〚 a₁ - a₂ 〛 s = 𝓐〚 a₁ 〛 s ℤ+ 𝓐〚 a₂ 〛 s
𝓐〚 a₁ * a₂ 〛 s = 𝓐〚 a₁ 〛 s ℤ+ 𝓐〚 a₂ 〛 s

infix 1 _∋_

data _∋_ : Aexp → Id → Set where
    H : ∀ {id : Id} → ` id ∋ id

    T+ : ∀ {a₁ a₂ : Aexp} {id : Id}
       → (a₁ ∋ id) ⊎ (a₂ ∋ id) → a₁ + a₂ ∋ id
    T* : ∀ {a₁ a₂ : Aexp} {id : Id}
       → (a₁ ∋ id) ⊎ (a₂ ∋ id) → a₁ * a₂ ∋ id
    T- : ∀ {a₁ a₂ : Aexp} {id : Id}
       → (a₁ ∋ id) ⊎ (a₂ ∋ id) → a₁ - a₂ ∋ id

_∋?_ : (a : Aexp) → (id : Id) → Dec (a ∋ id)
(` x)     ∋? id with x ≟ id
... | yes refl  = yes H
... | no  x≠id  = no λ{ H → x≠id refl}
(ℤ n)     ∋? id = no (λ ())
(a₁ + a₂) ∋? id with (a₁ ∋? id) | (a₂ ∋? id)
... | yes a₁∋id | _         = yes (T+ (inj₁ a₁∋id))
... | no _      | yes a₂∋id = yes (T+ (inj₂ a₂∋id))
... | no  a₁∌id | no  a₂∌id = no λ{ (T+ (inj₁ a₁∋id)) → a₁∌id a₁∋id
                                  ; (T+ (inj₂ a₂∋id)) → a₂∌id a₂∋id }
(a₁ - a₂) ∋? id with (a₁ ∋? id) | (a₂ ∋? id)
... | yes a₁∋id | _         = yes (T- (inj₁ a₁∋id))
... | no _      | yes a₂∋id = yes (T- (inj₂ a₂∋id))
... | no  a₁∌id | no  a₂∌id = no λ{ (T- (inj₁ a₁∋id)) → a₁∌id a₁∋id
                                  ; (T- (inj₂ a₂∋id)) → a₂∌id a₂∋id }
(a₁ * a₂) ∋? id with (a₁ ∋? id) | (a₂ ∋? id)
... | yes a₁∋id | _         = yes (T* (inj₁ a₁∋id))
... | no _      | yes a₂∋id = yes (T* (inj₂ a₂∋id))
... | no  a₁∌id | no  a₂∌id = no λ{ (T* (inj₁ a₁∋id)) → a₁∌id a₁∋id
                                  ; (T* (inj₂ a₂∋id)) → a₂∌id a₂∋id }

weakstate : (a : Aexp)
          → (s s' : State)
          → (∀ {id : Id} → a ∋ id → s id ≡ s' id)
          → 𝓐〚 a 〛 s ≡ 𝓐〚 a 〛 s'
weakstate (` x)     s s' p = p H
weakstate (ℤ x)     s s' p = refl
weakstate (a₁ + a₂) s s' p rewrite (weakstate a₁ s s' λ z → p (T+ (inj₁ z)))
                           |       (weakstate a₂ s s' λ z → p (T+ (inj₂ z)))
                           = refl
weakstate (a₁ - a₂) s s' p rewrite (weakstate a₁ s s' λ z → p (T- (inj₁ z)))
                           |       (weakstate a₂ s s' λ z → p (T- (inj₂ z)))
                           = refl
weakstate (a₁ * a₂) s s' p rewrite (weakstate a₁ s s' λ z → p (T* (inj₁ z)))
                           |       (weakstate a₂ s s' λ z → p (T* (inj₂ z)))
                           = refl

infix 10 _[_↦_]
infix 11 𝓐〚_〛_

_[_↦_] : Aexp → Id → Aexp → Aexp
(` x)     [ y ↦ a₀ ] with x ≟ y
...                   | yes refl = a₀
...                   | no x≠y   = ` x
(ℤ n)     [ y ↦ a₀ ] = ℤ_ n
(a₁ + a₂) [ y ↦ a₀ ] = a₁ [ y ↦ a₀  ] + a₂ [ y ↦ a₀ ]
(a₁ - a₂) [ y ↦ a₀ ] = a₁ [ y ↦ a₀  ] - a₂ [ y ↦ a₀ ]
(a₁ * a₂) [ y ↦ a₀ ] = a₁ [ y ↦ a₀  ] * a₂ [ y ↦ a₀ ]

subst≡ : ∀ (a a₀ : Aexp) → (s : State) → (y : Id)
       → 𝓐〚 a [ y ↦ a₀ ] 〛 s ≡ 𝓐〚 a 〛 (s s[ y ↦ 𝓐〚 a₀ 〛 s ])
subst≡ (` x)     a₀ s y with x ≟ y
...                     | yes refl rewrite insert≡  s x       (𝓐〚 a₀ 〛 s)
                                   = refl
...                     | no x≠y   rewrite insert¬≡ s x y x≠y (𝓐〚 a₀ 〛 s)
                                   = refl
subst≡ (ℤ x)     a₀ s y = refl
subst≡ (a₁ + a₂) a₀ s y rewrite subst≡ a₁ a₀ s y
                        |       subst≡ a₂ a₀ s y
                        = refl
subst≡ (a₁ - a₂) a₀ s y rewrite subst≡ a₁ a₀ s y
                        |       subst≡ a₂ a₀ s y
                        = refl
subst≡ (a₁ * a₂) a₀ s y rewrite subst≡ a₁ a₀ s y
                        |       subst≡ a₂ a₀ s y
                        = refl
