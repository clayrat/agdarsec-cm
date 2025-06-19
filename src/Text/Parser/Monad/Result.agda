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
    ℓe ℓa ℓb ℓ : Level
    E : 𝒰 ℓe
    A : 𝒰 ℓa
    B : 𝒰 ℓb

data Result (E : 𝒰 ℓe) (A : 𝒰 ℓa) : 𝒰 (ℓa ⊔ ℓe) where
  SoftFail : E → Result E A
  HardFail : E → Result E A
  Value    : A → Result E A

result : (E → B) → (E → B) → (A → B) → Result E A → B
result soft hard val (SoftFail e) = soft e
result soft hard val (HardFail e) = hard e
result soft hard val (Value v) = val v

to-sum : Result E A → E ⊎ A
to-sum = result inl inl inr

from-maybe : E → Maybe A → Result E A
from-maybe e = Maybe.rec (SoftFail e) Value

map-res : (A → B) → Result E A → Result E B
map-res f r = result SoftFail HardFail (Value ∘ f) r

app-res : Result E (A → B) → Result E A → Result E B
app-res f r = result SoftFail HardFail (λ g → map-res g r) f

bind-res : Result E A → (A → Result E B) → Result E B
bind-res r f = result SoftFail HardFail f r

record ResultT (E : 𝒰≤ ℓe)  -- Error
               (M : Effect) -- Monad
               (A : 𝒰 ℓa) : 𝒰 (M .Effect.adj (ℓe ⊔ ℓa))
       where
  constructor mkresultT
  private module M = Effect M
  field run-resultT : M.₀ (Result (Liftℓ E) A)
open ResultT public

{-
ResultT : 𝒰≤ ℓe                -- Error
        → (𝒰 (ℓa ⊔ ℓe) → 𝒰 ℓ) -- Monad
        → 𝒰 ℓa → 𝒰 ℓ
ResultT E M A = M (Result (Liftℓ E) A)
-}

module _ {M : Effect} (let module M = Effect M) ⦃ mp : Map M ⦄ where

  instance
    ResultT-map : {E : 𝒰≤ ℓe}
                → Map (eff (ResultT E M))
    ResultT-map .Map.map f x .run-resultT = map (map-res f) (x .run-resultT)


module _ {M : Effect} (let module M = Effect M) ⦃ app : Idiom M ⦄ where

  instance
    ResultT-idiom : {E : 𝒰≤ ℓe}
                  → Idiom (eff (ResultT E M))
    ResultT-idiom .Idiom.Map-idiom = ResultT-map
    ResultT-idiom .Idiom.pure x .run-resultT = pure (Value x)
    ResultT-idiom .Idiom._<*>_ mf mx .run-resultT =
      map app-res (mf .run-resultT) <*> mx .run-resultT

module _ {M : Effect} (let module M = Effect M) ⦃ bd : Bind M ⦄ where

  instance
    ResultT-bind : {E : 𝒰≤ ℓe}
                 → Bind (eff (ResultT E M))
    ResultT-bind .Bind.Idiom-bind = ResultT-idiom
    ResultT-bind .Bind._>>=_ x f .run-resultT =
      (x .run-resultT) >>= result (pure ∘ SoftFail) (pure ∘ HardFail) (run-resultT ∘ f)

    ResultT-choice : {E : 𝒰≤ ℓe}
                   → Choice (eff (ResultT E M))
    ResultT-choice .Choice._<|>_ r1 r2 .run-resultT =
      (r1 .run-resultT) >>= λ where
                                (SoftFail _) → r2 .run-resultT
                                r → pure r

{-
instance
  Result-bind : {E : 𝒰≤ ℓe}
              → Bind (eff (Result (Liftℓ E)))
  Result-bind =
     let qq = ResultT-bind ⦃ bd = Bind-Id ⦄ in
     {!!}
-}
