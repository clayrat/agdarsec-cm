{-# OPTIONS --safe #-}
module Data.List.Sized where

open import Meta.Prelude
open import Meta.Effect

open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.List

open import Level.Bounded
open import Data.List.Sized.Interface

module _ {ℓ : Level} {A : 𝒰 ℓ} where

 ∣_∣=_ : List A → ℕ → 𝒰
 ∣ []     ∣= zero  = ⊤
 ∣ _ ∷ xs ∣= suc n = ∣ xs ∣= n
 ∣ []     ∣= suc _ = ⊥
 ∣ _ ∷ _  ∣= zero  = ⊥

module _ {ℓ : Level} where

 record ∣List_∣=_ (A : 𝒰 ℓ) (n : ℕ) : 𝒰 ℓ where
   constructor mk-szlist
   field list     : List A
         @0 proof : ∣ list ∣= n
 open ∣List_∣=_ public

 data View (A : 𝒰 ℓ) : (n : ℕ) → ∣List A ∣= n → 𝒰 ℓ where
   []  : View A 0       (mk-szlist [] tt)
   _∷_ : ∀ {n} a (as : ∣List A ∣= n) {@0 e : ∣ a ∷ list as ∣= suc n}
       → View A (suc n) (mk-szlist (a ∷ list as) e)

module _ {ℓ : Level} {A : 𝒰 ℓ} where

 trivial : (xs : List A) → ∣ xs ∣= length xs
 trivial []       = tt
 trivial (_ ∷ xs) = trivial xs

 fromList : (xs : List A) → ∣List A ∣= length xs
 fromList xs = mk-szlist xs (trivial xs)

 view : ∀ {n} (xs : ∣List A ∣= n) → View A n xs
 view {n = 0}     (mk-szlist [] tt)        = []
 view {n = suc n} (mk-szlist (x ∷ xs) prf) = x ∷ mk-szlist xs prf
 view {n = 0}     (mk-szlist (_ ∷ _) ())
 view {n = suc n} (mk-szlist [] ())

module _ {ℓ ℓ′ : Level} {A : 𝒰 ℓ} {B : 𝒰 ℓ′} where

 size-map : (f : A → B) (xs : List A)
          → ∀ {n} → ∣ xs ∣= n → ∣ mapₗ f xs ∣= n  -- TODO ∀-notation fails (levels?)
 size-map f []       {n = zero} prf = tt
 size-map f (x ∷ xs) {n = suc n} prf = size-map f xs prf

 mapsz : (A → B) → ∀ {n} → ∣List A ∣= n → ∣List B ∣= n
 mapsz f (mk-szlist xs prf) = mk-szlist (mapₗ f xs) (size-map f xs prf)

instance
  sized-szlist : ∀ {ℓ} {A : 𝒰≤ ℓ} → Sized A (λ n → ∣List_∣= n $ℓ A)
  sized-szlist .Sized.view  xs with {lowerℓ xs} | view (lowerℓ xs)
  ... | []     = lift tt
  ... | a ∷ as = liftℓ (a , as)
