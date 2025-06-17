{-# OPTIONS --safe #-}
module Data.List.Sized.Interface where

open import Meta.Prelude

open import Data.Nat
open import Data.Unit
open import Data.Vec.Inductive as Vec

open import Level.Bounded

module _ {ℓ} (A : 𝒰≤ ℓ) (As : ℕ → 𝒰≤ ℓ) where

 Viewˢ : ℕ → 𝒰 ℓ
 Viewˢ  zero   = ⊤
 Viewˢ (suc n) = Liftℓ (A ×ℓ As n)

 record Sized : 𝒰 ℓ where
   field view : ∀ {n} → Liftℓ (As n) → Viewˢ n

instance
  vec : ∀ {l} {A : 𝒰≤ l} → Sized A (Vecℓ A)
  vec {A} .Sized.view xs =
    Vec.recU {P = Viewˢ A (Vecℓ A)}
             (lift tt)
             (λ x {xs} _ → liftℓ (x , xs))
             (lowerℓ xs)
