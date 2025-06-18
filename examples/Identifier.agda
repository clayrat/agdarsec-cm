module Identifier where

open import Foundations.Prelude
open import Meta.Effect

open import Data.List
open import Data.Char

open import Data.List.NonEmpty as List⁺
open import Data.List.Sized.Interface as SZ
open import Level.Bounded
open import Base 0ℓ

{-
import Level
open import Level.Bounded using ([_])

open import Data.Char.Base using (Char)
open import Data.List as List using ([]; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.List.Sized.Interface using ()

open import Base Level.zero
-}

record Identifier : 𝒰 where
  constructor mkIdentifier
  field getIdentifier : List⁺ Char

identifier : ∀[ Parser {ℓ = 0ℓ} (chars {ℓb = 0ℓ} {E = ⊤ℓ} {A = ⊥ℓ} ⦃ bd = Bind-Id ⦄) (Identifier 0↑ℓ) ]
identifier {x} =
   _<$>C_ ⦃ mp = map-agdarsecT ⦃ bd = Bind-Id ⦄ ⦄
          mkIdentifier
          (list⁺ ⦃ bd = bind-agdarsecT ⦃ bd = Bind-Id ⦄ ⦄
                 ⦃ ch = choice-agdarsecT ⦃ bd = Bind-Id ⦄  ⦄
                 {x = x} $
          alpha {ℓ = 0ℓ}
                 {P = (chars {ℓb = 0ℓ} {E = ⊤ℓ} {A = ⊥ℓ} ⦃ bd = Bind-Id ⦄)}
                 ⦃ bd = bind-agdarsecT ⦃ bd = Bind-Id ⦄ ⦄
                 ⦃ alt = alt-agdarsecT ⦃ bd = Bind-Id ⦄ ⦃ S = record { into = λ _ → lift tt } ⦄ ⦄)

-- tests

_ : _∈P_ {P = (chars {ℓb = 0ℓ} {E = ⊤ℓ} {A = ⊥ℓ} ⦃ bd = Bind-Id ⦄)}
         ⦃ ch = choice-agdarsecT ⦃ bd = Bind-Id ⦄ ⦄
         "hi"
         identifier
_ = mkIdentifier ('h' ∷¹ 'i' ∷ []) !
