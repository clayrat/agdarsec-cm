-- Parser based on RFC 8259: https://tools.ietf.org/html/rfc8259

{-# OPTIONS --safe #-}

open import Text.Parser.Types.Core using (Parameters)

module Text.Parser.JSON {ℓ} {P : Parameters ℓ} where

open import Foundations.Prelude
open import Meta.Effect
open Variadics _
open import Logic.Discreteness


-- open import Effect.Monad using (RawMonadPlus)
open import Data.Unit
open import Data.Bool.Base using (Bool; true; false)
open import Data.Char.Base using (Char)
open import Data.String.Base using (String)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base as Maybe
{-
open import Data.Float.Base using (Float)
open import Data.Maybe.Base using (maybe′)
open import Data.Product using (_×_; uncurry)
open import Data.Unit.Base using (⊤)


open import Function.Base using (_$_; _∘′_)

open import Relation.Unary
open import Relation.Binary.PropositionalEquality.Decidable using (DecidableEquality)
-}

import Data.List.NonEmpty as List⁺
open import Data.List.Sized.Interface
open import Data.Subset using (Subset; into)

open import Induction.Nat.Strong as Box using (□_; fix)
open import Level.Bounded -- using (theSet; [_])
open import Text.Parser.Types P
open import Text.Parser.Combinators {P = P}
open import Text.Parser.Combinators.Char {P = P}
open import Text.Parser.Combinators.Numbers {P = P}
open Parameters P

open import Data.JSON as JSON using (JSON)

module _ ⦃ bd : Bind M ⦄
         ⦃ alt : Alt M ⦄
         ⦃ S : Sized Tok Toks ⦄
         ⦃ d : is-discrete (Tok .ty) ⦄
         ⦃ C : Subset Char (Tok .ty) ⦄
         ⦃ D : Subset (Tok .ty) Char ⦄
         where

{-
module _ {{𝕄 : RawMonadPlus M}}
         {{𝕊 : Sized Tok Toks}}
         {{𝔻 : DecidableEquality (theSet Tok)}}
         {{ℂ : Subset Char (theSet Tok)}}
         {{ℂ⁻ : Subset (theSet Tok) Char}}
         where
-}

-- We assume that when we call a subparser all of the whitespace before
-- the potential token has been consumed already. So we should systematically
-- consume spaces after the tokens we have happily recognised.

-- Structural characters

  structuralChar : Char → ∀[ Parser (⊤ 0↑ℓ) ]
  structuralChar c = _ <$C (char c <&? box spaces)

  beginArray     = structuralChar '['
  beginObject    = structuralChar '{'
  endArray       = structuralChar ']'
  endObject      = structuralChar '}'
  nameSeparator  = structuralChar ':'
  valueSeparator = structuralChar ','

-- Subparser for members, provided a subparser for smaller JSON objects
-- According to the RFC:
-- member = string name-separator value

  member : ∀[ □ Parser (JSON 0↑ℓ) ⇒ Parser ((String × JSON) 0↑ℓ) ]
  member rec = stringLiteral <&? box spaces
             <&>C box (nameSeparator &>C rec)

-- Subparser for JSON objects, provided a subparser for smaller JSON objects
-- According to the RFC:
-- object = begin-object [ member *( value-separator member ) ] end-object

  object : ∀[ □ Parser (JSON 0↑ℓ) ⇒ Parser (List (String × JSON) 0↑ℓ) ]
  object rec =
    Maybe.rec [] ((λ a mas → a ∷ Maybe.rec [] List⁺.to-list mas) $²_)
    <$>C (beginObject
          &?> box (member rec <&?> box (list⁺ (valueSeparator &>C box (member rec))))
          <&C box endObject)

-- Subparser for JSON arrays, provided a subparser for smaller JSON objects
-- According to the RFC:
-- array = begin-array [ value *( value-separator value ) ] end-array

  array : ∀[ □ Parser (JSON 0↑ℓ) ⇒ Parser ((List JSON) 0↑ℓ) ]
  array rec =
    Maybe.rec [] ((λ a mas → a ∷ Maybe.rec [] List⁺.to-list mas) $²_)
    <$>C (beginArray
          &?> lift²l (λ p q → p <&?> box q) rec (list⁺ (valueSeparator &>C rec))
          <&C box endArray)

-- Parsing JSON values
  value : ∀[ Parser (JSON 0↑ℓ) ]
  value {x} =
    spaces ?&> (fix (Parser (JSON 0↑ℓ)) $ λ rec →
    alts $ (JSON.null       <$C  text "null" {pr = refl}  <&? box spaces)
         ∷ (JSON.bool true  <$C  text "true" {pr = refl}  <&? box spaces)
         ∷ (JSON.bool false <$C  text "false" {pr = refl} <&? box spaces)
         ∷ (JSON.number     <$>C decimalFloat  <&? box spaces)
         ∷ (JSON.string     <$>C stringLiteral <&? box spaces)
         ∷ (JSON.array      <$>C array rec)
         ∷ (JSON.object     <$>C object rec)
         ∷ [])
