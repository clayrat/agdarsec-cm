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
open import Data.Vec.Inductive

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
open import Data.Text.Sized

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
         {M : Effect} -- (let module M = Effect M)  -- doesn't work here for some reason
         ⦃ bd : Bind M ⦄
         ⦃ S : Subset (((Position 0↑ℓ) ×ℓ Listℓ A) .ty) (E .ty) ⦄
        where

  private
    module M = Effect M  -- only here

  open BindState ⦃ ... ⦄

  instance
    map-agdarsecT : Map (eff (AgdarsecT E A M.₀))
    map-agdarsecT .Map.map f x .run-agdarsecT =
      map ⦃ r = map-stateT ⦃ mp = ResultT-map ⦃ mp = bd .Idiom-bind .Map-idiom ⦄ ⦄ ⦄  -- why?
          f (x .run-agdarsecT)

    idiom-agdarsecT : Idiom (eff (AgdarsecT E A M.₀))
    idiom-agdarsecT .Idiom.Map-idiom = map-agdarsecT
    idiom-agdarsecT .Idiom.pure x .run-agdarsecT =
      pure ⦃ r = idiom-stateT ⦃ bd = ResultT-bind ⦃ bd = bd ⦄ ⦄ ⦄  -- why?
           x
    idiom-agdarsecT .Idiom._<*>_ f x .run-agdarsecT =
      _<*>_ ⦃ r = idiom-stateT ⦃ bd = ResultT-bind ⦃ bd = bd ⦄ ⦄ ⦄ -- why?
            (f .run-agdarsecT) (x .run-agdarsecT)

    bind-agdarsecT : Bind (eff (AgdarsecT E A M.₀))
    bind-agdarsecT .Bind.Idiom-bind = idiom-agdarsecT
    bind-agdarsecT .Bind._>>=_ x f .run-agdarsecT =
      _>>=_ ⦃ r = bind-stateT ⦃ bd = ResultT-bind ⦃ bd = bd ⦄ ⦄ ⦄ -- why?
            (x .run-agdarsecT) (run-agdarsecT ∘ f)

    bindstate-agdarsecT : BindState (Liftℓ ((Position 0↑ℓ) ×ℓ Listℓ A))
                                    (eff (AgdarsecT E A M.₀))
    bindstate-agdarsecT .BindState.Bind-state = bind-agdarsecT
    bindstate-agdarsecT .BindState.gets f .run-agdarsecT =
      gets ⦃ r = bindstate-stateT ⦃ bd = ResultT-bind ⦃ bd = bd ⦄ ⦄ ⦄ -- why?
           f
    bindstate-agdarsecT .BindState.modify f .run-agdarsecT =
      modify ⦃ r = bindstate-stateT ⦃ bd = ResultT-bind ⦃ bd = bd ⦄ ⦄ ⦄ -- why?
             f

    choice-agdarsecT : Choice (eff (AgdarsecT E A M.₀))
    choice-agdarsecT .Choice._<|>_ a b .run-agdarsecT =
      _<|>_ ⦃ r = choice-stateT ⦃ ch = ResultT-choice ⦃ bd = bd ⦄ ⦄ ⦄ -- why?
            (a .run-agdarsecT) (b .run-agdarsecT)

    alt-agdarsecT : Alt (eff (AgdarsecT E A M.₀))
    alt-agdarsecT .Alt.Choice-alt =
      choice-agdarsecT
    alt-agdarsecT .Alt.fail .run-agdarsecT .run-stateT x .run-resultT =
      pure $ SoftFail $ mapℓ (S .into) x

  getPosition : AgdarsecT E A M.₀ (Liftℓ (Position 0↑ℓ))
  getPosition = mapℓ fst <$> get

  getAnnotations : AgdarsecT E A M.₀ (Liftℓ (Listℓ A))
  getAnnotations = mapℓ snd <$> get

  withAnnotation : {T : 𝒰 ℓ}
                 → A .ty → AgdarsecT E A M.₀ T → AgdarsecT E A M.₀ T
  withAnnotation c ma =
    do modify (mapℓ $ second (c ∷_))
       a ← ma
       modify (mapℓ $ second (drop 1))
       pure ⦃ r = idiom-agdarsecT ⦄  -- why?
            a

  recordChar : ∀ {ℓ} → Char → AgdarsecT E A M.₀ (Liftℓ ⊤ℓ)
  recordChar {ℓ} c = _<$_ ⦃ map-agdarsecT ⦄ -- why?
                          (lift {ℓ′ = ℓ} (lift tt))
                          (modify (mapℓ (first (update c))))

  -- Commiting to a branch makes all the failures in that branch hard failures
  -- that we cannot recover from
  commit : {T : 𝒰 ℓ} → AgdarsecT E A M.₀ T → AgdarsecT E A M.₀ T
  commit m .run-agdarsecT .run-stateT s .run-resultT =
    _<$>_ ⦃ bd .Idiom-bind .Map-idiom ⦄ -- why?
          (result HardFail HardFail Value)
          (m .run-agdarsecT .run-stateT s .run-resultT)

  param : ∀ Tok Toks recTok → Parameters ℓ
  param Tok Toks recTok = record
    { Tok         = Tok
    ; Toks        = Toks
    ; M           = eff (AgdarsecT E A M.₀)
    ; recordToken = recTok
    }

  chars : Parameters ℓ
  chars = param (Char 0↑ℓ) (λ n → Vecℓ (Char 0↑ℓ) n) recordChar

  raw : Parameters ℓ
  raw = param (Char 0↑ℓ) (λ n → (Text n) 0↑ℓ) recordChar

{-

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
