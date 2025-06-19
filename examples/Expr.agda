-- Example taken from parsec's documentation
-- https://hackage.haskell.org/package/parsec-3.1.11/docs/Text-Parsec-Combinator.html#v:chainl1

module Expr where

open import Foundations.Prelude
open import Meta.Effect
open Variadics _
open import Logic.Discreteness
-- import Level

open import Data.Char

{-
open import Data.Char using (Char)
open import Data.List.Base as List using ()
open import Data.List.NonEmpty as List⁺ using ()
open import Data.Nat.Base using (ℕ)
open import Data.Maybe using ()
open import Data.Product
open import Function.Base
import Induction.Nat.Strong as INS
-}

import Data.List.Sized.Interface
import Induction.Nat.Strong as INS
open import Level.Bounded

open import Base 0ℓ
--open import Identifier

data Expr : 𝒰 where
  Var     : Char → Expr
  Lit     : ℕ → Expr
  Add Sub : Expr → Expr → Expr
  Mul Div : Expr → Expr → Expr

record PExpr (P : Parameters 0ℓ) (n : ℕ) : 𝒰 (Effect.adj (Parameters.M P) 0ℓ) where
  field pvar : Parser P (Expr 0↑ℓ) n
        plit : Parser P (Expr 0↑ℓ) n
        pfac : Parser P (Expr 0↑ℓ) n
        pexp : Parser P (Expr 0↑ℓ) n
open PExpr

pExpr : ∀[ PExpr (chars {ℓb = 0ℓ} {E = ⊤ℓ} {A = ⊥ℓ} ⦃ bd = Bind-Id ⦄) ]
pExpr = INS.fix (PExpr (chars {ℓb = 0ℓ} {E = ⊤ℓ} {A = ⊥ℓ} ⦃ bd = Bind-Id ⦄)) $
        λ rec →
        let factor = parens (INS.map pexp rec) <|>C var <|>C lit
            term   = chainl1 factor $ box mulop
            expr   = chainl1 term   $ box addop
        in record { pvar = var
                  ; plit = lit
                  ; pfac = factor
                  ; pexp = expr }

 module Details where
   instance _ = Bind-Id

   var : ∀[ Parser (chars {ℓb = 0ℓ} {E = ⊤ℓ} {A = ⊥ℓ} ⦃ bd = Bind-Id ⦄)
                   (Expr 0↑ℓ) ]
   lit : ∀[ Parser (chars {ℓb = 0ℓ} {E = ⊤ℓ} {A = ⊥ℓ} ⦃ bd = Bind-Id ⦄)
                   (Expr 0↑ℓ) ]

   var {x} = Var <$>C alpha
     where instance _ = Bind-Id
   lit {x} = Lit <$>C decimalℕ
     where instance _ = Bind-Id

   addop : ∀[ Parser (chars {ℓb = 0ℓ} {E = ⊤ℓ} {A = ⊥ℓ} ⦃ bd = Bind-Id ⦄)
                     ((Expr 0↑ℓ) →ℓ ((Expr 0↑ℓ) →ℓ (Expr 0↑ℓ)))]
   mulop : ∀[ Parser (chars {ℓb = 0ℓ} {E = ⊤ℓ} {A = ⊥ℓ} ⦃ bd = Bind-Id ⦄)
                     ((Expr 0↑ℓ) →ℓ ((Expr 0↑ℓ) →ℓ (Expr 0↑ℓ)))]

   addop {x} = withSpaces (     Add <$C char '+'
                           <|>C Sub <$C char '-')
     where instance _ = Bind-Id
   mulop {x} = withSpaces (     Mul <$C char '*'
                           <|>C Div <$C char '/')
     where instance _ = Bind-Id

Expr′ : ∀[ Parser (chars {ℓb = 0ℓ} {E = ⊤ℓ} {A = ⊥ℓ} ⦃ bd = Bind-Id ⦄)
                  (Expr 0↑ℓ) ]
Expr′ {x} = pexp pExpr

-- tests

_ : _∈P_ {P = (chars {ℓb = 0ℓ} {E = ⊤ℓ} {A = ⊥ℓ} ⦃ bd = Bind-Id ⦄)}
         ⦃ ch = choice-agdarsecT ⦃ bd = Bind-Id ⦄ ⦄
         "x+y+z"
         Expr′
_ = Add (Add (Var 'x') (Var 'y')) (Var 'z') !

_ : _∈P_ {P = (chars {ℓb = 0ℓ} {E = ⊤ℓ} {A = ⊥ℓ} ⦃ bd = Bind-Id ⦄)}
         ⦃ ch = choice-agdarsecT ⦃ bd = Bind-Id ⦄ ⦄
         "x + y + z"
         Expr′
_ = Add (Add (Var 'x') (Var 'y')) (Var 'z') !

_ : _∈P_ {P = (chars {ℓb = 0ℓ} {E = ⊤ℓ} {A = ⊥ℓ} ⦃ bd = Bind-Id ⦄)}
         ⦃ ch = choice-agdarsecT ⦃ bd = Bind-Id ⦄ ⦄
         "x+y*z+t"
         Expr′
_ = Add (Add (Var 'x') (Mul (Var 'y') (Var 'z'))) (Var 't') !

_ : _∈P_ {P = (chars {ℓb = 0ℓ} {E = ⊤ℓ} {A = ⊥ℓ} ⦃ bd = Bind-Id ⦄)}
         ⦃ ch = choice-agdarsecT ⦃ bd = Bind-Id ⦄ ⦄
         "(x+y)*z*t+u"
         Expr′
_ = Add (Mul (Mul (Add (Var 'x') (Var 'y')) (Var 'z')) (Var 't')) (Var 'u') !

_ : _∈P_ {P = (chars {ℓb = 0ℓ} {E = ⊤ℓ} {A = ⊥ℓ} ⦃ bd = Bind-Id ⦄)}
         ⦃ ch = choice-agdarsecT ⦃ bd = Bind-Id ⦄ ⦄
         "10*(x+5*y)+z*7"
         Expr′
_ = Add (Mul (Lit 10) (Add (Var 'x') (Mul (Lit 5) (Var 'y')))) (Mul (Var 'z') (Lit 7)) !

