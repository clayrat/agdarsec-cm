module Identifier where

open import Foundations.Prelude
open import Meta.Effect

open import Data.List
open import Data.Char

open import Data.List.NonEmpty as List⁺
open import Data.List.Sized.Interface as SZ
open import Level.Bounded
open import Base 0ℓ

record Identifier : 𝒰 where
  constructor mkIdentifier
  field getIdentifier : List⁺ Char

identifier : ∀[ Parser {ℓ = 0ℓ}
                       (chars {ℓb = 0ℓ} {E = ⊤ℓ} {A = ⊥ℓ} ⦃ bd = Bind-Id ⦄)
                       (Identifier 0↑ℓ) ]
identifier {x} =
   mkIdentifier <$>C list⁺ alpha
  where instance _ = Bind-Id


-- tests

_ : _∈P_ {P = (chars {ℓb = 0ℓ} {E = ⊤ℓ} {A = ⊥ℓ} ⦃ bd = Bind-Id ⦄)}
         ⦃ ch = choice-agdarsecT ⦃ bd = Bind-Id ⦄ ⦄
         "hi"
         identifier
_ = mkIdentifier ('h' ∷¹ 'i' ∷ []) !
