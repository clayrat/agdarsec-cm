{-# OPTIONS --safe #-}
module Text.Parser.Position where

open import Meta.Prelude
open import Logic.Discreteness
open import Data.Bool
open import Data.Nat
open import Data.Char
open import Data.String
open import Data.List
-- open import Function.Base using (flip)

record Position : 𝒰 where
  constructor _∶_
  field line   : ℕ
        offset : ℕ
open Position public

start : Position
start .line = 0
start .offset = 0

update : Char → Position → Position
update c p =
  if c char=? '\n'
    then suc (p .line) ∶ 0
    else (p .line ∶ suc (p .offset))

updates : String → Position → Position
updates str p = fold-l (flip update) p (string→list str)

show : Position → String
show p = show-ℕ (p .line) ++ₛ ":" ++ₛ show-ℕ (p .offset)
