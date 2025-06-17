{-# OPTIONS --safe #-}
module Text.Parser.Monad.Result where

open import Foundations.Prelude
open import Meta.Effect
open Variadics _

open import Data.Maybe as Maybe
open import Data.Sum as Sum

open import Level.Bounded

{-
open import Level using (Level)
open import Level.Bounded using (Set≤; Lift)
open import Effect.Monad using (RawMonad; mkRawMonad)
open import Effect.Empty
open import Effect.Choice
open import Data.Maybe.Base using (Maybe; maybe′)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘′_)
import Function.Identity.Effectful as Id
-}

private
  variable
    ℓ ℓe ℓa ℓb : Level
    E : 𝒰 ℓe
    A : 𝒰 ℓa
    B : 𝒰 ℓb

data Result (E : 𝒰 ℓe) (A : 𝒰 ℓa) : 𝒰 (ℓa ⊔ ℓe) where
  SoftFail : E → Result E A
  HardFail : E → Result E A
  Value    : A → Result E A

result : (soft hard : E → B) (val : A → B) → Result E A → B
result soft hard val (SoftFail e) = soft e
result soft hard val (HardFail e) = hard e
result soft hard val (Value v) = val v

to-sum : Result E A → E ⊎ A
to-sum = result inl inl inr

from-maybe : E → Maybe A → Result E A
from-maybe e = Maybe.rec (SoftFail e) Value

map-res : (A → B) → Result E A → Result E B
map-res f (SoftFail e) = SoftFail e
map-res f (HardFail e) = HardFail e
map-res f (Value v)    = Value (f v)

app-res : Result E (A → B) → Result E A → Result E B
app-res (SoftFail e)  _           = SoftFail e
app-res (HardFail e)  _           = HardFail e
app-res (Value _)    (SoftFail e) = SoftFail e
app-res (Value _)    (HardFail e) = HardFail e
app-res (Value f)    (Value x)    = Value (f x)

ResultT : 𝒰≤ ℓe        -- Error
        → (M : Effect)  -- Monad
        → 𝒰 ℓa → 𝒰 (Effect.adj M (ℓe ⊔ ℓa))
ResultT E M A =
  let module M = Effect M in
  M.₀ (Result (Liftℓ E) A)

-- TODO how to automate instance passing?
instance
  ResultT-map : {E : 𝒰≤ ℓe} {M : Effect}
                ⦃ mp : Map M ⦄
              → Map (eff (ResultT E M))
  ResultT-map ⦃ mp ⦄ .Map.map = map ⦃ r = mp ⦄ ∘ map-res

  ResultT-idiom : {E : 𝒰≤ ℓe} {M : Effect}
                  ⦃ app : Idiom M ⦄
                → Idiom (eff (ResultT E M))
  ResultT-idiom ⦃ app ⦄ .Idiom.Map-idiom = ResultT-map ⦃ mp = app .Map-idiom ⦄
  ResultT-idiom ⦃ app ⦄ .Idiom.pure = pure ⦃ r = app ⦄ ∘ Value
  ResultT-idiom ⦃ app ⦄ .Idiom._<*>_ mf mx = _<*>_ ⦃ r = app ⦄ (map ⦃ r = app .Map-idiom ⦄ app-res mf)  mx

  ResultT-bind : {E : 𝒰≤ ℓe} {M : Effect}
                 ⦃ bd : Bind M ⦄
                → Bind (eff (ResultT E M))
  ResultT-bind ⦃ bd ⦄ .Bind.Idiom-bind = ResultT-idiom ⦃ app = bd .Idiom-bind ⦄
  ResultT-bind ⦃ bd ⦄ .Bind._>>=_ x f = _>>=_ ⦃ r = bd ⦄ x (result (pure ⦃ r = bd .Idiom-bind ⦄ ∘ SoftFail) (pure ⦃ r = bd .Idiom-bind ⦄ ∘ HardFail) f)

  Result-bind : {E : 𝒰≤ ℓe}
              → Bind (eff (Result (Liftℓ E)))
  Result-bind = ResultT-bind ⦃ bd = Bind-Id ⦄

  ResultT-choice : {E : 𝒰≤ ℓe} {M : Effect}
                   ⦃ bd : Bind M ⦄
                 → Choice (eff (ResultT E M))
  ResultT-choice ⦃ bd ⦄ .Choice._<|>_ r1 r2 =
    _>>=_ ⦃ r = bd ⦄ r1
       (λ where
            (SoftFail _) → r2
            r → pure ⦃ r = bd .Idiom-bind ⦄ r)
