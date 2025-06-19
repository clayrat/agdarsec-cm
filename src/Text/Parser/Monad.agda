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

record AgdarsecT (E : 𝒰≤ ℓb) -- Error
                 (A : 𝒰≤ ℓb) -- Annotation
                 (M : Effect) -- Monad
                 (T : 𝒰 ℓa) : 𝒰 (ℓb ⊔ M .Effect.adj (ℓb ⊔ ℓa))
                 where
  constructor mkagdarsecT
  field run-agdarsecT : StateT (Liftℓ ((Position 0↑ℓ) ×ℓ Listℓ A)) (eff (ResultT E M)) T
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
Agdarsec E A = AgdarsecT E A (eff id)

module _ {E A : 𝒰≤ ℓb}
         {M : Effect} (let module M = Effect M)  -- doesn't work here for some reason
         ⦃ bd : Bind M ⦄
        where

  open BindState ⦃ ... ⦄

  instance
    map-agdarsecT : Map (eff (AgdarsecT E A M))
    map-agdarsecT .Map.map f x .run-agdarsecT = map f (x .run-agdarsecT)

    idiom-agdarsecT : Idiom (eff (AgdarsecT E A M))
    idiom-agdarsecT .Idiom.Map-idiom = map-agdarsecT
    idiom-agdarsecT .Idiom.pure x .run-agdarsecT = pure x
    idiom-agdarsecT .Idiom._<*>_ f x .run-agdarsecT =
      f .run-agdarsecT <*> x .run-agdarsecT

    bind-agdarsecT : Bind (eff (AgdarsecT E A M))
    bind-agdarsecT .Bind.Idiom-bind = idiom-agdarsecT
    bind-agdarsecT .Bind._>>=_ x f .run-agdarsecT =
      x .run-agdarsecT >>= run-agdarsecT ∘ f

    bindstate-agdarsecT : BindState (Liftℓ ((Position 0↑ℓ) ×ℓ Listℓ A))
                                    (eff (AgdarsecT E A M))
    bindstate-agdarsecT .BindState.Bind-state = bind-agdarsecT
    bindstate-agdarsecT .BindState.gets f .run-agdarsecT = gets f
    bindstate-agdarsecT .BindState.modify f .run-agdarsecT = modify f

    choice-agdarsecT : Choice (eff (AgdarsecT E A M))
    choice-agdarsecT .Choice._<|>_ a b .run-agdarsecT =
      a .run-agdarsecT <|> b .run-agdarsecT

    alt-agdarsecT : ⦃ S : Subset (((Position 0↑ℓ) ×ℓ Listℓ A) .ty) (E .ty) ⦄
                  → Alt (eff (AgdarsecT E A M))
    alt-agdarsecT .Alt.Choice-alt =
      choice-agdarsecT
    alt-agdarsecT ⦃ S ⦄ .Alt.fail .run-agdarsecT .run-stateT x .run-resultT =
      pure $ SoftFail $ mapℓ (S .into) x

  getPosition : AgdarsecT E A M (Liftℓ (Position 0↑ℓ))
  getPosition = mapℓ fst <$> get

  getAnnotations : AgdarsecT E A M (Liftℓ (Listℓ A))
  getAnnotations = mapℓ snd <$> get

  withAnnotation : {T : 𝒰 ℓ}
                 → A .ty → AgdarsecT E A M T → AgdarsecT E A M T
  withAnnotation c ma =
    do modify (mapℓ $ second (c ∷_))
       a ← ma
       modify (mapℓ $ second (drop 1))
       pure a

  recordChar : ∀ {ℓ} → Char → AgdarsecT E A M (Liftℓ ⊤ℓ)
  recordChar {ℓ} c = lift {ℓ′ = ℓ} (lift tt) <$ modify (mapℓ (first (update c)))

  -- Commiting to a branch makes all the failures in that branch hard failures
  -- that we cannot recover from
  commit : {T : 𝒰 ℓ} → AgdarsecT E A M T → AgdarsecT E A M T
  commit m .run-agdarsecT .run-stateT s .run-resultT =
    result HardFail HardFail Value <$> m .run-agdarsecT .run-stateT s .run-resultT

  param : (Tok : 𝒰≤ ℓ)
        → (ℕ → 𝒰≤ ℓ)
        → (Tok .ty → AgdarsecT E A M (Liftℓ ⊤ℓ))
        → Parameters ℓ
  param Tok Toks recTok = record
    { Tok         = Tok
    ; Toks        = Toks
    ; M           = eff (AgdarsecT E A M)
    ; recordToken = recTok
    }

  chars : Parameters ℓ
  chars = param (Char 0↑ℓ) (λ n → Vecℓ (Char 0↑ℓ) n) recordChar

  raw : Parameters ℓ
  raw = param (Char 0↑ℓ) (λ n → (Text n) 0↑ℓ) recordChar

module _ {ℓ} {E A : 𝒰≤ ℓ}
         ⦃ S : Subset (((Position 0↑ℓ) ×ℓ Listℓ A) .ty) (E .ty) ⦄
         where

  module _ {Tok : 𝒰≤ ℓ}
           {Toks : ℕ → 𝒰≤ ℓ}
           {recTok : Tok .ty → AgdarsecT E A (eff id) (Liftℓ ⊤ℓ)} where

    private P = param ⦃ bd = Bind-Id ⦄
                      Tok Toks recTok
    commitP : {A : 𝒰≤ ℓ} → ∀[ Parser P A ⇒ Parser P A ]
    commitP p .run-parser m≤n s =
      commit (mkagdarsecT (p .run-parser m≤n s .run-agdarsecT))
        where instance _ = Bind-Id

module _ {ℓ} where

--  open Agdarsec l ⊤ ⊥ _ public

  vec : 𝒰≤ ℓ → Parameters ℓ
  vec t .Parameters.Tok = t
  vec t .Parameters.Toks = Vecℓ t
  vec t .Parameters.M = eff (Agdarsec {ℓb = ℓ} ⊤ℓ ⊥ℓ)
  vec t .Parameters.recordToken _ =
    pure (lift (lift tt))
      where instance _ = Bind-Id

  txt : 𝒰≤ ℓ → Parameters ℓ
  txt t .Parameters.Tok = t
  txt t .Parameters.Toks n = Text n 0↑ℓ
  txt t .Parameters.M = eff (Agdarsec {ℓb = ℓ} ⊤ℓ ⊥ℓ)
  txt t .Parameters.recordToken _ =
    pure (lift (lift tt))
      where instance _ = Bind-Id
