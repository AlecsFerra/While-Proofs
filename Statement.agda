open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (inj₁-injective)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Bool.Properties using (not-¬)

open import Identifier using (Id)
open import Arith using (Aexp; 𝓐〚_〛_)
open import Bool using (Bexp; 𝓑〚_〛_)
open import State using (State; _[_↦_])


infixr 9 _﹔_
data Stm : Set where

    _≔_  : Id → Aexp → Stm
    skip : Stm

    _﹔_ : Stm → Stm → Stm

    if_then_else_  : Bexp → Stm → Stm → Stm
    while_perform_ : Bexp → Stm → Stm

data Done : Set where
    done : Done

infixr 10 _⟶_

data _⟶_ : Stm × State → (Stm ⊎ Done) × State → Set where

    ass : ∀ {s x a}
        → ⟨ x ≔ a , s ⟩ ⟶ ⟨ inj₂ done , s [ x ↦ 𝓐〚 a 〛 s ] ⟩

    skip : ∀ {s}
         → ⟨ skip , s ⟩ ⟶ ⟨ inj₂ done , s ⟩

    comp₁ : ∀ {S₁ s S₁′ s′ S₂}
          → ⟨ S₁ , s ⟩ ⟶ ⟨ inj₁ S₁′ , s′ ⟩
          → ⟨ S₁ ﹔ S₂ , s ⟩ ⟶ ⟨ inj₁ (S₁′ ﹔ S₂) , s′ ⟩

    comp₂ : ∀ {S₁ s s′ S₂}
          → ⟨ S₁ , s ⟩ ⟶ ⟨ inj₂ done , s′ ⟩
          → ⟨ S₁ ﹔ S₂ , s ⟩ ⟶ ⟨ inj₁ S₂ , s′ ⟩

    if⊤ : ∀ {b S₁ S₂ s}
        → 𝓑〚 b 〛 s ≡ true
        → ⟨ if b then S₁ else S₂ , s ⟩ ⟶ ⟨ inj₁ S₁ , s ⟩

    if⊥ :  ∀ {b S₁ S₂ s}
        → 𝓑〚 b 〛 s ≡ false
        → ⟨ if b then S₁ else S₂ , s ⟩ ⟶ ⟨ inj₁ S₂ , s ⟩

    while : ∀ {b S s}
          → ⟨ while b perform S , s ⟩ ⟶ ⟨ inj₁ (if b then (S ﹔ while b perform S) else skip) , s ⟩

deterministic : ∀ {A B B′} → A ⟶ B → A ⟶ B′ → B ≡ B′
deterministic ass          ass           = refl
deterministic skip         skip          = refl
deterministic (if⊤ _)      (if⊤ _)       = refl
deterministic (if⊤ x)      (if⊥ y)       rewrite x
                                         = contradiction refl (not-¬ y)
deterministic (if⊥ x)      (if⊤ y)       rewrite x
                                         = contradiction refl (not-¬ y)
deterministic (if⊥ _)      (if⊥ _)       = refl
deterministic while        while         = refl
deterministic (comp₁ ())   (comp₂ ass)
deterministic (comp₁ ())   (comp₂ skip)
deterministic (comp₂ ass)  (comp₂ ass)   = refl
deterministic (comp₂ skip) (comp₂ skip)  = refl
deterministic (comp₁ A⟶B) (comp₁ A⟶B′) with deterministic A⟶B A⟶B′
... | ind rewrite cong proj₂ ind | inj₁-injective (cong proj₁ ind) = refl
