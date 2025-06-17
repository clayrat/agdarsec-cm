{-# OPTIONS --safe #-}

module Text.Parser.Monad where

open import Foundations.Prelude
open import Meta.Effect
{-
open import Meta.Effect.Base
open import Meta.Effect.Map.Base
open import Meta.Effect.Idiom
open import Meta.Effect.Bind
open import Meta.Effect.Choice
open import Meta.Effect.Alt
-}
open import Meta.Effect.Bind.State
open Variadics _

open import Data.Char -- .Base using (Char)
open import Data.List as List -- using ([]; _∷_)
open import Data.String
open import Data.Maybe as Maybe

{-

open import Level using (Level)
open import Level.Bounded as Level≤ hiding (map)

open import Data.Char.Base using (Char)
open import Data.List.Base as List using ([]; _∷_; drop)
open import Data.Maybe.Base as Maybe using (nothing; just; maybe′)
open import Data.Product using (_,_; proj₁; proj₂; map₁; map₂)
open import Data.String.Base using (String)
open import Data.Text.Sized using (Text)

open import Data.Subset using (Subset; into)
open import Function.Base using (_∘′_; _$′_)

open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad
open import Effect.Empty
open import Effect.Choice

open import Function.Identity.Effectful as Id using (Identity)
open import Effect.Monad.State.Transformer as StateT
  using (StateT; mkStateT; runStateT; RawMonadState)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Relation.Unary
open import Text.Parser.Types.Core
open import Text.Parser.Types
open import Text.Parser.Position
open import Text.Parser.Monad.Result

-}

open import Level.Bounded

open import Data.Subset
open import Data.List.NonEmpty as List⁺ -- using (List⁺)
open import Data.List.Sized.Interface using (Sized)

open import Text.Parser.Types.Core
open import Text.Parser.Types
open import Text.Parser.Position
open import Text.Parser.Monad.Result

private
  variable
    ℓ ℓa ℓb : Level

-- AGDARSECT

record AgdarsecT (E : 𝒰≤ ℓb)               -- Error
                 (A : 𝒰≤ ℓb)               -- Annotation
                 (M : 𝒰 (ℓb ⊔ ℓa) → 𝒰 ℓ)  -- Monad
                 (T : 𝒰 ℓa) : 𝒰 (ℓb ⊔ ℓ)
                 where
  constructor mkagdarsecT
  field run-agdarsecT : StateT (Liftℓ ((Position 0↑ℓ) ×ℓ Listℓ A)) (ResultT E M) T
open AgdarsecT public

{-
AgdarsecT : 𝒰≤ ℓb        -- Error
          → 𝒰≤ ℓb        -- Annotation
          → (M : Effect)  -- Monad
          → 𝒰 ℓ → 𝒰 (ℓb ⊔ Effect.adj M (ℓb ⊔ ℓ))
AgdarsecT E A M = StateT (Liftℓ ((Position 0↑ℓ) ×ℓ Listℓ A)) (ResultT E M)
-}

Agdarsec : 𝒰≤ ℓb        -- Error
         → 𝒰≤ ℓb        -- Annotation
         → 𝒰 ℓ → 𝒰 (ℓb ⊔ ℓ)
Agdarsec E A = AgdarsecT E A id

module _ {E A : 𝒰≤ ℓb}
         {M : Effect} (let module M = Effect M)
         ⦃ bd : Bind M ⦄
         ⦃ S : Subset (((Position 0↑ℓ) ×ℓ Listℓ A) .ty) (E .ty) ⦄
        where

  open Map ⦃ ... ⦄
  open BindState ⦃ ... ⦄

  instance
    map-agdarsecT : Map (eff (AgdarsecT E A M.₀))
    map-agdarsecT .Map.map f x .run-agdarsecT = {!!}

      -- map f (x .run-agdarsecT)
      --map-stateT ⦃ mp = ResultT-map ⦃ mp = bd .Idiom-bind .Map-idiom ⦄ ⦄

{-
    idiom-agdarsecT : Idiom (eff (AgdarsecT E A M.₀))
    idiom-agdarsecT = {!!}
     -- idiom-stateT ⦃ bd = ResultT-bind ⦃ bd = bd ⦄ ⦄

    bind-agdarsecT : Bind (eff (AgdarsecT E A M.₀))
    bind-agdarsecT = {!!}
      -- bind-stateT ⦃ bd = ResultT-bind ⦃ bd = bd ⦄ ⦄

    bindstate-agdarsecT : BindState (Liftℓ ((Position 0↑ℓ) ×ℓ Listℓ A))
                                    (eff (AgdarsecT E A M.₀))
    bindstate-agdarsecT = {!!}
      -- bindstate-stateT ⦃ bd = ResultT-bind ⦃ bd = bd ⦄ ⦄

    choice-agdarsecT : Choice (eff (AgdarsecT E A M.₀))
    choice-agdarsecT = {!!}
    -- choice-stateT ⦃ ch = ResultT-choice ⦃ bd = bd ⦄ ⦄

    alt-agdarsecT : Alt (eff (AgdarsecT E A M.₀))
    alt-agdarsecT .Alt.Choice-alt =
      {!!}
    alt-agdarsecT .Alt.fail .run-agdarsecT .run-stateT =
      {!!}
      -- pure ⦃ r = bd .Idiom-bind ⦄ ∘ SoftFail ∘ mapℓ (S .into)
-}
{-
--  open Bind ⦃ ... ⦄
  open BindState ⦃ ... ⦄

  map-agdarsecT : Map (eff (AgdarsecT E A M))
  map-agdarsecT = map-stateT ⦃ mp = ResultT-map ⦃ mp = bd .Idiom-bind .Map-idiom ⦄ ⦄

  idiom-agdarsecT : Idiom (eff (AgdarsecT E A M))
  idiom-agdarsecT = idiom-stateT ⦃ bd = ResultT-bind ⦃ bd = bd ⦄ ⦄

  bind-agdarsecT : Bind (eff (AgdarsecT E A M))
  bind-agdarsecT = bind-stateT ⦃ bd = ResultT-bind ⦃ bd = bd ⦄ ⦄

  bindstate-agdarsecT : BindState (Liftℓ ((Position 0↑ℓ) ×ℓ Listℓ A))
                                  (eff (AgdarsecT E A M))
  bindstate-agdarsecT = bindstate-stateT ⦃ bd = ResultT-bind ⦃ bd = bd ⦄ ⦄

  choice-agdarsecT : Choice (eff (AgdarsecT E A M))
  choice-agdarsecT = choice-stateT ⦃ ch = ResultT-choice ⦃ bd = bd ⦄ ⦄

  instance
    alt-agdarsecT : Alt (eff (AgdarsecT E A M))
    alt-agdarsecT .Alt.Choice-alt =
      choice-agdarsecT
    alt-agdarsecT .Alt.fail .run-stateT =
      pure ⦃ r = bd .Idiom-bind ⦄ ∘ SoftFail ∘ mapℓ (S .into)

  getPosition : AgdarsecT {ℓ = ℓ} E A M (Liftℓ (Position 0↑ℓ))
  getPosition =
    _<$>_ -- ⦃ map-agdarsecT ⦄
          (mapℓ fst)
          (get
            -- ⦃ r = bindstate-agdarsecT ⦄
            )

  getAnnotations : AgdarsecT E A M (Liftℓ (Listℓ A))
  getAnnotations =
    _<$>_ ⦃ map-agdarsecT ⦄
          (mapℓ snd)
          (get ⦃ r = bindstate-agdarsecT ⦄)
-}

{-
  withAnnotation : {T : 𝒰 ℓ}
                 → A .ty → AgdarsecT E A M T → AgdarsecT E A M T
  withAnnotation c ma =
    do modify {M = eff (AgdarsecT E A M)} ⦃ r = bindstate-agdarsecT ⦄
              (mapℓ $ second (c ∷_))
       a ← ma
       modify {M = eff (AgdarsecT E A M)} ⦃ r = bindstate-agdarsecT ⦄
              (mapℓ $ second (drop 1))
       pure {M = eff (AgdarsecT E A M)} ⦃ r = idiom-agdarsecT ⦄ a
-}

{-

  withAnnotation : ∀ {A} → theSet Ann → AgdarsecT E Ann M A → AgdarsecT E Ann M A
  withAnnotation c ma = let open ST in do
    modify (Level≤.map $′ map₂ (c ∷_))
    a ← ma
    modify (Level≤.map $′ map₂ (drop 1))
    pure a

  recordChar : Char → AgdarsecT E Ann M (Lift ⊤)
  recordChar c = _ ST.<$ ST.modify (Level≤.map $′ map₁ (update c))

  -- Commiting to a branch makes all the failures in that branch hard failures
  -- that we cannot recover from
  commit : ∀ {A} → AgdarsecT E Ann M A → AgdarsecT E Ann M A
  commit m = mkStateT λ s → result HardFail HardFail Value 𝕄.<$> runStateT m s

  param : ∀ Tok Toks recTok → Parameters l
  param Tok Toks recTok = record
    { Tok         = Tok
    ; Toks        = Toks
    ; M           = AgdarsecT E Ann M
    ; recordToken = recTok
    }

  chars : Parameters l
  chars = param [ Char ] (Vec [ Char ]) recordChar

  raw : Parameters l
  raw = param [ Char ] (λ n → [ Text n ]) recordChar

module Agdarsec l (E Ann : Set≤ l) (𝕊 : Subset (theSet ([ Position ] × List Ann)) (theSet E)) where

  private module M = AgdarsecT E Ann Id.monad 𝕊
  open M public renaming (monadT to monad) hiding (commit)

  module _ {Tok Toks recTok} where

    private P = param Tok Toks recTok
    commit : {A : Set≤ l} → ∀[ Parser P A ⇒ Parser P A ]
    runParser (commit p) m≤n s = M.commit (runParser p m≤n s)

module Agdarsec′ {l : Level} where

  open Agdarsec l ⊤ ⊥ _ public

  vec : Set≤ l → Parameters l
  vec Tok = record
    { Tok         = Tok
    ; Toks        = Vec Tok
    ; M           = Agdarsec ⊤ ⊥
    ; recordToken = λ _ → M.pure _
    } where module M = RawMonad monad

  txt : Set≤ l → Parameters l
  txt Tok = record
    { Tok         = Tok
    ; Toks        = λ n → [ Text n ]
    ; M           = Agdarsec ⊤ ⊥
    ; recordToken = λ _ → M.pure _
    } where module M = RawMonad monad
-}
