open import Core.Identifier using (Id)
open import Core.Arith using (Aexp; đã_ã_)
open import Core.Bool using (Bexp; đã_ã_)

module Core.Statement where

infixr 9 _īš_
data Stm : Set where

    _â_  : Id â Aexp â Stm
    skip : Stm

    _īš_ : Stm â Stm â Stm

    if_then_else_  : Bexp â Stm â Stm â Stm
    while_perform_ : Bexp â Stm â Stm
