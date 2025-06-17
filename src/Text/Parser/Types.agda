{-# OPTIONS --safe #-}

open import Text.Parser.Types.Core using (Parameters)

module Text.Parser.Types {ℓ} (P : Parameters ℓ) where

open import Meta.Prelude
open import Meta.Effect
open import Level.Bounded
open import Data.Nat
open import Data.Nat.Order.Base

open Text.Parser.Types.Core using (Success)

--------------------------------------------------------------------------------
-- PARSER

-- A parser is the ability to, given an input, return a computation for
-- a success.

record Parser (A : 𝒰≤ ℓ) (n : ℕ) : 𝒰 (ℓ ⊔ Effect.adj (Parameters.M P) ℓ) where
  constructor mk-parser
  open Parameters P
  field run-parser : ∀ {m} → (@0 m≤n : m ≤ n) → Liftℓ (Toks m) → Effect.₀ M (Success Toks A m)
open Parser public
