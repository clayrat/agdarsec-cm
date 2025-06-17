{-# OPTIONS --safe #-}
module Data.Subset where

open import Foundations.Prelude

record Subset {ℓa ℓb} (A : 𝒰 ℓa) (B : 𝒰 ℓb) : 𝒰 (ℓa ⊔ ℓb) where
  field into : A → B
open Subset public

open import Data.List
open import Data.Char
open import Data.String

instance

  Subset-list : ∀ {ℓa} {A : 𝒰 ℓa} → Subset A (List A)
  Subset-list .into a = a ∷ []

  Subset-chars : Subset Char String
  Subset-chars .into c = list→string (c ∷ [])

  Subset-refl : ∀ {ℓa} {A : 𝒰 ℓa} → Subset A A
  Subset-refl .into x = x

