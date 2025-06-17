{-# OPTIONS --safe #-}
module Level.Bounded where

open import Prelude

open import Data.Id.Inductive
open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Maybe
open import Data.List
open import Data.Nat
open import Data.Vec.Inductive

open import Data.List.NonEmpty

-- Bounded levels

_≤ℓ_ : Level → Level → 𝒰
ℓ₁ ≤ℓ ℓ₂ = (ℓ₂ ⊔ ℓ₁) ＝ⁱ ℓ₂

≤ℓ-refl : ∀ {ℓ} → ℓ ≤ℓ ℓ
≤ℓ-refl = refl

≤ℓ-trans : ∀ {ℓ₁ ℓ₂ ℓ₃} → ℓ₁ ≤ℓ ℓ₂ → ℓ₂ ≤ℓ ℓ₃ → ℓ₁ ≤ℓ ℓ₃
≤ℓ-trans {ℓ₁} {ℓ₃} le12 le23 = apⁱ (ℓ₁ ⊔_) (le23 ⁻¹) ∙ apⁱ (_⊔ ℓ₃) le12 ∙ le23

≤ℓ-antisym : ∀ {ℓ₁ ℓ₂} → ℓ₁ ≤ℓ ℓ₂ → ℓ₂ ≤ℓ ℓ₁ → ℓ₁ ＝ⁱ ℓ₂
≤ℓ-antisym le12 le21 = le21 ⁻¹ ∙ le12

z≤ℓ : ∀ {ℓ} → 0ℓ ≤ℓ ℓ
z≤ℓ = refl

-- TODO order ?

record Level≤ (l : Level) : 𝒰 where
  constructor mk-level-≤
  field level   : Level
        ⦃ bound ⦄ : level ≤ℓ l
open Level≤ public

zlev : ∀ {ℓ} → Level≤ ℓ
zlev = mk-level-≤ 0ℓ ⦃ bound = z≤ℓ ⦄

infixl 6 _⊔lev_
_⊔lev_ : ∀ {ℓ₁ ℓ₂} (a : Level≤ ℓ₁) (b : Level≤ ℓ₂) → Level≤ (ℓ₁ ⊔ ℓ₂)
(a ⊔lev b) .level = a .level ⊔ b .level
(a ⊔lev b) .bound = apⁱ² _⊔_ (a .bound) (b .bound)

-- Bounded sets

record 𝒰≤ (ℓ : Level) : 𝒰ω where
  field lev≤ : Level≤ ℓ
        ty   : 𝒰 (level lev≤)
open 𝒰≤ public

mk𝒰≤ : {ℓ₁ ℓ₂ : Level} → ⦃ bnd : ℓ₁ ≤ℓ ℓ₂ ⦄ → 𝒰 ℓ₁ → 𝒰≤ ℓ₂
mk𝒰≤ {ℓ₁} A .lev≤ = mk-level-≤ ℓ₁
mk𝒰≤            A .ty   = A

-- Type constructors

_0↑ℓ : 𝒰 → ∀ {ℓ} → 𝒰≤ ℓ
(A 0↑ℓ) .lev≤ = zlev
(A 0↑ℓ) .ty   = A

embed : ∀ {ℓ} → 𝒰 ℓ → 𝒰≤ ℓ
embed {ℓ} A .lev≤ = mk-level-≤ ℓ
embed     A .ty   = A

⊤ℓ : ∀ {ℓ} → 𝒰≤ ℓ
⊤ℓ = embed ⊤

⊥ℓ : ∀ {ℓ} → 𝒰≤ ℓ
⊥ℓ = embed ⊥

_→ℓ_ : ∀ {ℓ} → 𝒰≤ ℓ → 𝒰≤ ℓ → 𝒰≤ ℓ
(A →ℓ B) .lev≤ = A .lev≤ ⊔lev B .lev≤
(A →ℓ B) .ty   = A .ty → B .ty

_×ℓ_ : ∀ {ℓ} → 𝒰≤ ℓ → 𝒰≤ ℓ → 𝒰≤ ℓ
(A ×ℓ B) .lev≤ = A .lev≤ ⊔lev B .lev≤
(A ×ℓ B) .ty   = A .ty × B .ty

Σℓ : ∀ {ℓ₁ ℓ₂} (A : 𝒰≤ ℓ₂) ⦃ ℓ₁≤ℓ₂ : ℓ₁ ≤ℓ ℓ₂ ⦄ (B : A .ty → 𝒰 ℓ₁) → 𝒰≤ ℓ₂
Σℓ {ℓ₁} A ⦃ ℓ₁≤ℓ₂ ⦄ B .lev≤ = A .lev≤ ⊔lev mk-level-≤ ℓ₁ ⦃ bound = ℓ₁≤ℓ₂ ⦄
Σℓ      A           B .ty   = Σ (A .ty) B

infixr 1 _⊎ℓ_
_⊎ℓ_ : ∀ {ℓ} → 𝒰≤ ℓ → 𝒰≤ ℓ → 𝒰≤ ℓ
(A ⊎ℓ B) .lev≤ = A .lev≤ ⊔lev B .lev≤
(A ⊎ℓ B) .ty   = A .ty ⊎ B .ty

infixr 0 _$ℓ_
_$ℓ_ : (∀ {ℓ} → 𝒰 ℓ → 𝒰 ℓ) → ∀ {ℓ} → 𝒰≤ ℓ → 𝒰≤ ℓ
(F $ℓ A) .lev≤ = A .lev≤
(F $ℓ A) .ty = F (A .ty)

Maybeℓ : ∀ {ℓ} → 𝒰≤ ℓ → 𝒰≤ ℓ
Maybeℓ = Maybe $ℓ_

Listℓ : ∀ {ℓ} → 𝒰≤ ℓ → 𝒰≤ ℓ
Listℓ = List $ℓ_

Vecℓ : ∀ {ℓ} → 𝒰≤ ℓ → ℕ → 𝒰≤ ℓ
Vecℓ A n = (λ A → Vec A n) $ℓ A

List⁺ℓ : ∀ {ℓ} → 𝒰≤ ℓ → 𝒰≤ ℓ
List⁺ℓ = List⁺ $ℓ_

-- Going back and forth between `Set≤ l`  and `Set l`

Liftℓ : ∀ {ℓ} → 𝒰≤ ℓ → 𝒰 ℓ
Liftℓ {ℓ} A = castℓ (A .lev≤ .bound) (A .ty) module Liftℓ where
  castℓ : ∀ {ℓ′} → ℓ ⊔ (A .lev≤ .level) ＝ⁱ ℓ′
       → 𝒰 (A .lev≤ .level) → 𝒰 ℓ′
  castℓ {ℓ′} reflⁱ = Lift ℓ′


liftℓ : ∀ {ℓ} {A : 𝒰≤ ℓ} → A .ty → Liftℓ A
liftℓ {ℓ} {A} = castℓ (A .lev≤ .bound) where
  castℓ : ∀ {ℓ′} → (e : ℓ ⊔ (A .lev≤ .level) ＝ⁱ ℓ′)
        → A .ty → Liftℓ.castℓ A e (A .ty)
  castℓ reflⁱ = lift

lowerℓ : ∀ {ℓ} {A : 𝒰≤ ℓ} → Liftℓ A → A .ty
lowerℓ {ℓ} {A} = castℓ (A .lev≤ .bound) where
  castℓ : ∀ {ℓ′} → (e : ℓ ⊔ (A .lev≤ .level) ＝ⁱ ℓ′)
        → Liftℓ.castℓ A e (A .ty) → A .ty
  castℓ reflⁱ = lower

mapℓ : ∀ {ℓ} {A B : 𝒰≤ ℓ} → (A .ty → B .ty) → Liftℓ A → Liftℓ B
mapℓ f a = liftℓ (f (lowerℓ a))
