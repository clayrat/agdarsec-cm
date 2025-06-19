{-# OPTIONS --safe #-}

module Data.Singleton where

open import Foundations.Prelude

-- open import Level using (Level; levelOfType)
open import Data.Empty -- .Polymorphic using (⊥)
open import Data.Maybe.Base --using (Maybe; nothing; just)
open import Data.Sum.Base -- using (_⊎_; inj₁; inj₂)

private
  variable
    ℓa ℓb : Level
    A : 𝒰 ℓa
    B : 𝒰 ℓb

infix 0 _!
data Singleton {A : 𝒰 ℓa} : A → 𝒰 ℓa where
  _! : (a : A) → Singleton a

fromJust : Maybe A → 𝒰 (level-of-type A)
fromJust (just a) = Singleton a
fromJust nothing  = ⊥

fromInl : A ⊎ B → 𝒰 (level-of-type A)
fromInl (inl a) = Singleton a
fromInl (inr _) = ⊥

fromInr : A ⊎ B → 𝒰 (level-of-type B)
fromInr (inl _) = ⊥
fromInr (inr b) = Singleton b
