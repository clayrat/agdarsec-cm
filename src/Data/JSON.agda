{-# OPTIONS --safe #-}

module Data.JSON where

open import Foundations.Prelude

open import Data.Bool.Base -- using (Bool)
open import Data.Float.Base -- using (Float)
open import Data.List.Base -- using (List)
-- open import Data.Product using (_×_)
open import Data.String.Base -- using (String)

data JSON : 𝒰 where
  null   : JSON
  bool   : Bool → JSON
  number : Float → JSON
  string : String → JSON
  array  : List JSON → JSON
  object : List (String × JSON) → JSON
