{-# OPTIONS --safe #-}

open import Meta.Prelude
open import Meta.Effect
open Variadics _

open import Text.Parser.Types.Core using (Parameters)

module Text.Parser.Success {ℓ} (P : Parameters ℓ) where

open import Data.Nat -- .Base using (ℕ; zero; suc; _≤_; _<_)
open import Data.Nat.Order.Base
-- open import Data.Nat.Properties using (≤-trans; <⇒≤; ≤-refl)
open import Data.Maybe -- .Base as Maybe using (Maybe; nothing; just)
-- open import Data.Product using (_,_)
-- open import Function.Base using (_∘′_; _$_)
-- open import Relation.Unary using (IUniversal; _⇒_)

open import Level.Bounded as Level≤ -- using (_≤l_; Set≤; Σ; _×_; mkSet≤; theSet; lift; lower)
open import Data.List.Sized.Interface using (Sized)
open Text.Parser.Types.Core
open import Text.Parser.Types P
open Parameters P
open Success

module _ {A B : 𝒰≤ ℓ} where

  mapS : (A .ty → B .ty) → ∀[ Success Toks A ⇒ Success Toks B ]
  mapS f (a ^ m≤n ⸴ s) = mapℓ f a ^ m≤n ⸴ s

  guardMS : (A .ty → Maybe (B .ty)) →
           ∀[ Success Toks A ⇒ Maybe ∘ Success Toks B ]
  guardMS f (a ^ m≤n ⸴ s) = map ((_^ m≤n ⸴ s) ∘ liftℓ {A = B}) (f (lowerℓ a))

module _ {A : 𝒰≤ ℓ} {m n : ℕ} where

  ≤-lift : (@0 le : m ≤ n) → Success Toks A m → Success Toks A n
  ≤-lift m≤n (a ^ p<m ⸴ s) = a ^ <-≤-trans p<m m≤n ⸴ s

  <-lift : (@0 le : m < n) → Success Toks A m → Success Toks A n
  <-lift m<n = ≤-lift (<→≤ m<n)

module _ {A : 𝒰≤ ℓ} {ℓb} ⦃ b≤l : ℓb ≤ℓ ℓ ⦄ {B : A .ty → 𝒰 ℓb} where

  and : ∀ {n} (p : Success Toks A n) →
        Success Toks (mk𝒰≤ (B (lowerℓ $ value p))) (p .ssize) →
        Success Toks (Σℓ A B) n
  and (a ^ m<n ⸴ v) q = <-lift m<n (mapS (lowerℓ a ,_) q)

module _ {A B : 𝒰≤ ℓ} where

  and′ : ∀ {n} (p : Success Toks A n)
       → Success Toks B (p .ssize)
       → Success Toks (A ×ℓ B) n
  and′ (a ^ m<n ⸴ v) q = <-lift m<n (mapS (lowerℓ a ,_) q)

module _ {{𝕊 : Sized Tok Toks}} where

  view : ∀ {n} → (Toks n) .ty → Maybe (Success Toks Tok n)
  view {n = zero}   ts = nothing
  view {n = suc n}  ts =
    just $
    let (t , ts) = lowerℓ (Sized.view 𝕊 (liftℓ ts)) in
    liftℓ t ^ <-ascend ⸴ liftℓ ts
