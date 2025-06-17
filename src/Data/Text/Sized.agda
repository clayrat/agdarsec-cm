module Data.Text.Sized where

open import Foundations.Prelude
open import Meta.Effect
open Variadics _

open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Reflects
open import Data.Char
open import Data.String
open import Data.String.Properties.Unsafe
open import Data.List
open import Data.Maybe as Maybe

open import Level.Bounded
open import Data.List.Sized.Interface using (Sized)

private
  variable ℓ : Level

record Text (n : ℕ) : 𝒰 where
  constructor mk-text
  field
    value  : String
    @0 proof : lengthₛ value ＝ n
open Text

record Split (n : ℕ) (str : String) : 𝒰 where
  constructor mk-split
  field
    hd   : Char
    tl   : String
    @0 sz  : lengthₛ tl ＝ n
    @0 prf : (hd , tl) ∈ uncons str

split : ∀ str {n} → (@0 _ : lengthₛ str ＝ suc n) → Split n str
split str {n} lgth with uncons str | recall uncons str
... | just (c , s) | ⟪ eq ⟫ =
  mk-split c s (suc-inj (  ap (λ q → Maybe.rec zero (suc ∘ lengthₛ) (map snd q))
                              (eq ⁻¹)
                         ∙ length-tail {s = str} ⁻¹
                         ∙ lgth))
               (=just→∈ eq)
... | nothing      | ⟪ eq ⟫ =
  absurd $  -- needed because of erasure
  false! (  ap (λ q → Maybe.rec zero (suc ∘ lengthₛ) (map snd q))
               (eq ⁻¹)
          ∙ length-tail {s = str} ⁻¹
          ∙ lgth)

instance
  text : Sized {ℓ} (Char 0↑ℓ) (λ n → (Text n) 0↑ℓ)
  text .Sized.view {n = zero}   t                     = lift tt
  text .Sized.view {n = suc n} (lift (mk-text v prf)) =
    let mk-split c s prf _ = split v prf in
    lift (c , mk-text s prf)
