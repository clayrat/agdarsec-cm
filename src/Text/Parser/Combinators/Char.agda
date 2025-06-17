{-# OPTIONS --safe #-}

open import Foundations.Prelude
open import Meta.Effect
open Variadics _

open import Text.Parser.Types.Core using (Parameters)

module Text.Parser.Combinators.Char {ℓ} {P : Parameters ℓ} where

open import Data.Reflects
open import Data.Bool
open import Data.Char -- .Base using (Char)
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.List as List -- using ([]; _∷_)
open import Data.String
open import Data.Vec.Inductive as Vec hiding ([]; _∷_; _++_)
open import Data.Vec.Inductive.Operations hiding ([]; _∷_; _++_)
open import Data.Maybe as Maybe
{-
open import Data.Unit.Base
open import Data.Bool.Base using (T; not)
open import Data.Char.Base using (Char)
open import Data.List.Base as List using ([]; _∷_; null)
open import Data.List.NonEmpty as List⁺ using (_∷_)
open import Data.Maybe.Base using (nothing; just; maybe; fromMaybe)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Show as ℕ
open import Data.Product using (_,_)
open import Data.String.Base as String using (String)
open import Data.Vec.Base as Vec using (toList)

open import Effect.Monad using (RawMonadPlus)
open import Function.Base using (_∘′_; _$′_; _$_)

open import Relation.Nullary using (does)
open import Relation.Unary
open import Induction.Nat.Strong using (□_)
open import Data.List.Sized.Interface using (Sized)
open import Data.Subset using (Subset; into)
open import Relation.Binary.PropositionalEquality.Decidable using (DecidableEquality; decide)

-}


open import Logic.Discreteness

open import Data.Subset
open import Data.List.NonEmpty as List⁺ -- using (List⁺)
open import Data.List.Sized.Interface using (Sized)

open import Level.Bounded
open import Induction.Nat.Strong as Box using (□_)

open import Text.Parser.Types P
open import Text.Parser.Combinators {P = P}
open import Text.Parser.Combinators.Numbers {P = P}
open Parameters P

module _ -- {{𝕄 : RawMonadPlus M}}
         ⦃ S : Sized Tok Toks ⦄
         ⦃ d : is-discrete (Tok .ty) ⦄
--         {{𝔻 : DecidableEquality (theSet Tok)}}
         ⦃ C : Subset Char (Tok .ty) ⦄ where

{-
 private module ℂ = Subset ℂ
-}

 char : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
      → Char → ∀[ Parser Tok ]
 char = exact ∘ C .into

 anyCharBut : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
            → Char → ∀[ Parser Tok ]
 anyCharBut = anyTokenBut ∘ C .into

 noneOfChars : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
             → List Char → ∀[ Parser Tok ]
 noneOfChars = noneOf ∘ map (C .into)

 anyOfChars : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
            → List Char → ∀[ Parser Tok ]
 anyOfChars = anyOf ∘ map (C .into)

 space : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
       → ∀[ Parser Tok ]
 space = anyOf $ map (C .into) $ ' ' ∷ '\t' ∷ '\n' ∷ []

 spaces : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
        → ∀[ Parser (List⁺ℓ Tok) ]
 spaces = list⁺ space

 text : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
      → (t : String) {pr : is-true (not $ List.is-nil? $ string→list t)}
      → ∀[ Parser (List⁺ℓ Tok) ]
 text t {pr} with string→list t | pr
 ... | []     | p = false! p
 ... | c ∷ cs | _ = exacts (List⁺.map⁺ (C .into) (c ∷¹ cs))

 module _ {A : 𝒰≤ ℓ} where

  parens : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
         → ∀[ □ Parser A ⇒ Parser A ]
  parens = between (char '(') (box (char ')'))

  parens? : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
          → ∀[ Parser A ⇒ Parser A ]
  parens? = between? (char '(') (box (char ')'))

  withSpaces : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
             → ∀[ Parser A ⇒ Parser A ]
  withSpaces A = spaces ?&> A <&? box spaces

 lowerAlpha : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
            → ∀[ Parser Tok ]
 lowerAlpha = anyOf
            $ map (C .into)
            $ string→list "abcdefghijklmnopqrstuvwxyz"

 upperAlpha : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
            → ∀[ Parser Tok ]
 upperAlpha = anyOf
            $ map (C .into)
            $ string→list "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

 alpha : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
       → ∀[ Parser Tok ]
 alpha = lowerAlpha <|>C upperAlpha

 alphas⁺ : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
         → ∀[ Parser (List⁺ℓ Tok) ]
 alphas⁺ = list⁺ alpha

 alphanum : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
          → ∀[ Parser (Tok ⊎ℓ (ℕ 0↑ℓ)) ]
 alphanum = alpha <⊎> decimalDigit

module _ -- {{𝕄 : RawMonadPlus M}}
         ⦃ S : Sized Tok Toks ⦄
         ⦃ d : is-discrete (Tok .ty) ⦄
--         {{𝔻 : DecidableEquality (theSet Tok)}}
         ⦃ C : Subset Char (Tok .ty) ⦄
         ⦃ D : Subset (Tok .ty) Char ⦄
         where

 stringLiteral : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
               → ∀[ Parser (String 0↑ℓ) ]
 stringLiteral =
   convert <$>C (char '"'
           &?> box escaped
           <&>C box (list⁺ (unescaped <&?> box escaped)
           <?& char '"'))

   where

     toks : 𝒰≤ _
     toks = List⁺ℓ Tok

     unescaped : ∀[ Parser toks ]
     unescaped {x} = list⁺ (noneOfChars ('\\' ∷ '"' ∷ []))

     convertUnicode : Vec ℕ 4 → toks .ty
     convertUnicode ds =
       List⁺.map⁺ (C .into) $
       '\\' ∷¹ 'u' ∷ map toChar (vec→list ds .fst)

       where

         toChar : ℕ → Char -- only for hexadecimal digits
         toChar 0  = '0'
         toChar 1  = '1'
         toChar 2  = '2'
         toChar 3  = '3'
         toChar 4  = '4'
         toChar 5  = '5'
         toChar 6  = '6'
         toChar 7  = '7'
         toChar 8  = '8'
         toChar 9  = '9'
         toChar 10 = 'a'
         toChar 11 = 'b'
         toChar 12 = 'c'
         toChar 13 = 'd'
         toChar 14 = 'e'
         toChar _  = 'f'

     escaped : ∀[ Parser toks ]
     escaped =
       let unicode : ∀[ Parser (Maybeℓ toks) ]
           unicode = (just ∘ convertUnicode) <$>C replicateC 4 {z< = z<s}
                                                               hexadecimalDigit

           chunks : ∀[ Parser (List⁺ℓ toks) ]
           chunks = list⁺ ((λ (a , mb) → from-just (a ∷¹ []) mb)
             <$>C (char '\\' -- escaping
             &>C box ((_, nothing) <$>C anyOfChars ('"' ∷ '\\' ∷ 'r' ∷ 'n' ∷ 't' ∷ [])) -- special characters
               <|>C char 'u' <&>C box unicode))
       in List⁺.concat⁺ <$>C chunks

     convert : (Maybeℓ toks ×ℓ Maybeℓ (List⁺ℓ (toks ×ℓ Maybeℓ toks))) .ty → String
     convert (mt , mts) = -- let open Listℓ in
       list→string $
         fromMToks mt ++
          Maybe.rec
             []
             (  concat
              ∘ map (λ (ts , mts) → fromToks ts ++ fromMToks mts)
              ∘ List⁺.to-list)
              mts

       where
         fromToks : toks .ty → List Char
         fromToks = List⁺.to-list ∘ List⁺.map⁺ (D .into)

         fromMToks : (Maybeℓ toks) .ty → List Char
         fromMToks = Maybe.rec [] fromToks
