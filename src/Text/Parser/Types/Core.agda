{-# OPTIONS --safe #-}

module Text.Parser.Types.Core where

open import Meta.Prelude
open import Meta.Effect
open import Level.Bounded using (𝒰≤; ty; Liftℓ; ⊤ℓ)
open import Data.Unit
open import Data.Nat
open import Data.Nat.Order.Base


--------------------------------------------------------------------------------
-- PARAMETERS

-- A parser is parametrised by some types, type constructors and one function.

record Parameters (ℓ : Level) : 𝒰ω where
   field
-- Token-related parameters:
-- * Tok: tokens
     Tok    : 𝒰≤ ℓ
-- * Toks: sized input (~ Vec Tok)
     Toks   : ℕ → 𝒰≤ ℓ
-- The monad stack used
     M : Effect -- 𝒰 ℓ → 𝒰 ℓ
-- The action allowing us to track consumed tokens
     recordToken : -- let module M = Effect M in
                   Tok .ty → Effect.₀ M ⊤

--------------------------------------------------------------------------------
-- SUCCESS

-- A successful partial parse of an A is a value A together leftovers
-- which are proven to be smaller than the input

infix 1 _^_⸴_
record Success {ℓ} (Toks : ℕ → 𝒰≤ ℓ) (A : 𝒰≤ ℓ) (n : ℕ) : 𝒰 ℓ where
  constructor _^_⸴_
  field
    value     : Liftℓ A
    {ssize}   : ℕ
    @0 small  : ssize < n
    leftovers : Liftℓ (Toks ssize)
