{-# OPTIONS --safe #-}

module Induction.Nat.Strong where

open import Meta.Prelude
open Variadics _

open import Data.Empty
open import Data.Nat.Base
open import Data.Nat.Order.Base
open import Data.Nat.Properties
-- open import Relation.Unary
-- open import Function

infix 9 □_
record □_ {ℓ} (A : ℕ → 𝒰 ℓ) (n : ℕ) : 𝒰 ℓ where
  constructor mk-nbox
  field call : ∀ {m} → (@0 m<n : m < n) → A m
open □_ public

module _ {ℓ} {A B : ℕ → 𝒰 ℓ} where

 map : ∀[ A ⇒ B ] → ∀[ □ A ⇒ □ B ]
 map f a .call m<n = f (a .call m<n)

module _ {ℓ} {A : ℕ → 𝒰 ℓ} where

 pure : ∀[ A ] → ∀[ □ A ]
 pure a .call _ = a

 extract : ∀[ □ A ] → ∀[ A ]
 extract a = a .call <-ascend

 duplicate : ∀[ □ A ⇒ □ □ A ]
 duplicate a .call m<n .call p<m = a .call (<-trans p<m m<n)

 ≤↓ : {m n : ℕ} → (@0 m≤n : m ≤ n) → (□ A) n → (□ A) m
 ≤↓ m≤n a .call p<m = a .call (<-≤-trans p<m m≤n)

 <↓ : {m n : ℕ} → (@0 m<n : m < n) → (□ A) n → (□ A) m
 <↓ m<n a .call p<m = a .call (<-trans p<m m<n)

 fix□ : ∀[ □ A ⇒ A ] → ∀[ □ A ]
 fix□ f {x = zero}  .call m<0 = absurd (≮z m<0)
 fix□ f {x = suc x} .call m<s = f (≤↓ (≤≃<suc ⁻¹ $ m<s) (fix□ f))

module _ {ℓ} {A B : ℕ → 𝒰 ℓ} where

 map² : {C : ℕ → 𝒰 ℓ} → ∀[ A ⇒ B ⇒ C ] → ∀[ □ A ⇒ □ B ⇒ □ C ]
 map² f A B .call m<n = f (A .call m<n) (B .call m<n)

 app : ∀[ □ (A ⇒ B) ⇒ (□ A ⇒ □ B) ]
 app F A .call m<n = F .call m<n (A .call m<n)

fix : ∀ {ℓ} (A : ℕ → 𝒰 ℓ) → ∀[ □ A ⇒ A ] → ∀[ A ]
fix A = extract ∘ fix□

module _ {ℓ} {A : ℕ → 𝒰 ℓ} where

 <-close : (∀ {m n} → (@0 m<n : m < n) → A n → A m) → ∀[ A ⇒ □ A ]
 <-close d a .call m<n = d m<n a

 ≤-close : (∀ {m n} → (@0 m≤n : m ≤ n) → A n → A m) → ∀[ A ⇒ □ A ]
 ≤-close d = <-close λ m<n → d (<-weaken _ _ m<n)

 loeb : ∀[ □ (□ A ⇒ A) ⇒ □ A ]
 loeb = fix (□ (□ A ⇒ A) ⇒ □ A) $
        λ rec f → mk-nbox λ m<n →
                            f .call m<n (rec .call m<n (duplicate f .call m<n))
