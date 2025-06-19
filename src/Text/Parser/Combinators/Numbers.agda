{-# OPTIONS --safe #-}

open import Foundations.Prelude
open import Meta.Effect
open Variadics _

open import Text.Parser.Types.Core using (Parameters)

module Text.Parser.Combinators.Numbers {ℓ} {P : Parameters ℓ} where

open import Data.Bool
open import Data.Char -- .Base using (Char)
open import Data.Nat
open import Data.List as List -- using ([]; _∷_)
open import Data.Int.Base -- using (ℤ; -_; +_; _◃_)
open import Data.Float.Base -- as Float using (Float; fromℕ; fromℤ)
open import Data.Maybe as Maybe
{-
open import Data.Float.Base as Float using (Float; fromℕ; fromℤ)
open import Data.Integer.Base using (ℤ; -_; +_; _◃_)
open import Data.List.Sized.Interface
open import Data.Maybe.Base using (Maybe; fromMaybe; maybe′)
open import Data.Nat.Base as ℕ using (ℕ; _+_; _*_)
import Data.Nat.GeneralisedArithmetic
open import Data.Product as Product using (_×_; _,_; uncurry)
open import Data.Sign.Base using (Sign)
open import Data.Sum.Base using ([_,_]′)

open import Function.Base using (const; id; _$_; _∘′_; case_of_)
open import Effect.Monad using (RawMonadPlus)

open import Relation.Unary
open import Relation.Binary.PropositionalEquality.Decidable using (DecidableEquality)
open import Data.Subset using (Subset; into)
-}

open import Logic.Discreteness

open import Data.Subset
open import Data.List.NonEmpty as List⁺ -- using (List⁺)
open import Data.List.Sized.Interface using (Sized)

open import Level.Bounded -- using (theSet; [_])
open import Text.Parser.Types P
open import Text.Parser.Combinators {P = P}
open Parameters P

module _ -- {{𝕄 : RawMonadPlus M}}
         ⦃ S : Sized Tok Toks ⦄
         ⦃ d : is-discrete (Tok .ty) ⦄
--         {{𝔻 : DecidableEquality (theSet Tok)}}
         ⦃ C : Subset Char (Tok .ty) ⦄ where

-- private module C = Subset C

 decimalDigit : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
              → ∀[ Parser (ℕ 0↑ℓ) ]
 decimalDigit =
   alts $
   map ((λ v c → v <$C exact (C .into c)) $²_) $ -- TODO how make it adhoc
     (0 , '0') ∷ (1 , '1') ∷ (2 , '2') ∷ (3 , '3') ∷ (4 , '4')
   ∷ (5 , '5') ∷ (6 , '6') ∷ (7 , '7') ∷ (8 , '8') ∷ (9 , '9') ∷ []

 hexadecimalDigit : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
                  → ∀[ Parser (ℕ 0↑ℓ) ]
 hexadecimalDigit = decimalDigit <|>C alts hex
   where
   hex : ∀[ List ∘ Parser (ℕ 0↑ℓ) ]
   hex {x} =
     map ((λ v c → v <$C exact (C .into c)) $²_) $ -- TODO how make it adhoc
          (10 , 'a') ∷ (11 , 'b') ∷ (12 , 'c')
        ∷ (13 , 'd') ∷ (14 , 'e') ∷ (15 , 'f') ∷ []

 private
   natFromDigits : List⁺ ℕ → ℕ
   natFromDigits = List⁺.foldl (λ ih v → ih · 10 + v) id

 decimalℕ : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
          → ∀[ Parser (ℕ 0↑ℓ) ]
 decimalℕ = natFromDigits <$>C list⁺ decimalDigit

 sign : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
      → ∀[ Parser (Bool 0↑ℓ) ]
 sign =
         true <$C anyOf (map (C .into) $ '-' ∷ '−' ∷ [])
    <|>C false <$C exact (C .into '+')

 decimalℤ : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
          → ∀[ Parser (ℤ 0↑ℓ) ]
 decimalℤ = convert $²_ <$>C (sign <?&> decimalℕ) where
   convert : Maybe Bool → ℕ → ℤ
   convert ms n =
     Maybe.rec (pos n)
               (λ s → if s and is-positive? n
                        then negsuc (pred n)
                        else pos n)
               ms

 decimalFloat : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
              → ∀[ Parser (Float 0↑ℓ) ]
 decimalFloat = convert <$>C rawDouble where

   fractional : ∀[ Parser ((List⁺ ℕ) 0↑ℓ) ]
   fractional {x} = exact (C .into '.') &>C box (list⁺ decimalDigit)

   fromFractional : List⁺ ℕ → Float
   fromFractional ds =
     float-div (ℕ→float (natFromDigits ds))
               (ℕ→float (10 ^ List⁺.len ds))

   eNotation : ∀[ Parser ((Maybe Bool × ℕ) 0↑ℓ) ]
   eNotation {x} =
     anyOf (C .into 'E' ∷ C .into 'e' ∷ [])
            &>C box (sign <?&> decimalℕ)

   fromENotation : Maybe Bool × ℕ → Float → Float
   fromENotation (ms , e) f =
     if Maybe.from-just false ms
        then float-div f (ℕ→float (10 ^ e))
        else float-times f (ℕ→float (10 ^ e))

   rawDouble : ∀[ Parser (((ℤ × Maybe (List⁺ ℕ)) × Maybe (Maybe Bool × ℕ)) 0↑ℓ) ]
   rawDouble {x} = (decimalℤ <&?> box fractional) <&?> box eNotation

   convert : (ℤ × Maybe (List⁺ ℕ)) × Maybe (Maybe Bool × ℕ) → Float
   convert ((int , mfrac) , menot) =
     Maybe.rec id fromENotation menot $
     Maybe.rec id (λ m f → float-plus f (fromFractional m)) mfrac $
     ℤ→float int
