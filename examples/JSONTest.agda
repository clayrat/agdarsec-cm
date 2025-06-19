module JSONTest where

open import Foundations.Prelude
open import Meta.Effect

open import Data.List.Base -- using (_∷_; [])
open import Data.List.Sized.Interface as SZ
open import Data.String
open import Data.Char
open import Data.Bool


open import Data.JSON
open import Level.Bounded

open import Base 0ℓ
open import Text.Parser.JSON using (value)

--open import IO.Base
--open import IO.Finite

--open import System.Environment

--main : Main
--main = run $ do
--  (fp ∷ []) ← getArgs
--    where _ → putStrLn "Pass a single filepath"
--  txt  ← readFile fp
--  json ← runParserIO value txt
--  putStrLn "Success!"

jsn : String
jsn = "{\"menu\": {
  \"id\": \"file\",
  \"quant\": 1.5,
  \"toggle\": true,
  \"value\": \"File\",
  \"popup\": {
    \"menuitem\": [
      {\"value\": \"New\", \"onclick\": \"CreateNewDoc()\"},
      {\"value\": \"Open\", \"onclick\": \"OpenDoc()\"},
      {\"value\": \"Close\", \"onclick\": \"CloseDoc()\"}
    ]
  }
}}"

_ : _∈P_ {P = (chars {ℓb = 0ℓ} {E = ⊤ℓ} {A = ⊥ℓ} ⦃ bd = Bind-Id ⦄)}
         ⦃ ch = choice-agdarsecT ⦃ bd = Bind-Id ⦄ ⦄
         jsn
         (value ⦃ bd = bind-agdarsecT ⦃ bd = Bind-Id ⦄ ⦄
                ⦃ alt = alt-agdarsecT ⦃ bd = Bind-Id ⦄ ⦃ S = record { into = λ _ → lift tt } ⦄ ⦄)
_ = object
      (("menu" ,
          object (  ("id"     , string "file")
                  ∷ ("quant"  , number 1.5)
                  ∷ ("toggle" , bool true)
                  ∷ ("value"  , string "File")
                  ∷ ("popup"  , object (("menuitem" ,
                                           array (  object (  ("value"   , string "New")
                                                            ∷ ("onclick" , string "CreateNewDoc()")
                                                            ∷ [])
                                                  ∷ object (  ("value"   , string "Open")
                                                            ∷ ("onclick" , string "OpenDoc()")
                                                            ∷ [])
                                                  ∷ object (  ("value"   , string "Close")
                                                            ∷ ("onclick" , string "CloseDoc()")
                                                            ∷ [])
                                                  ∷ []))
                                        ∷ []))
                  ∷ [])
       ) ∷ []) !
