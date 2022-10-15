open import Core.Identifier using (Id)
open import Core.Arith using (Aexp; 𝓐〚_〛_)
open import Core.Bool using (Bexp; 𝓑〚_〛_)

module Core.Statement where

infixr 9 _﹔_
data Stm : Set where

    _≔_  : Id → Aexp → Stm
    skip : Stm

    _﹔_ : Stm → Stm → Stm

    if_then_else_  : Bexp → Stm → Stm → Stm
    while_perform_ : Bexp → Stm → Stm
