{-# OPTIONS --safe #-}
module Data.List.NonEmpty.Base where

open import Foundations.Base
open import Meta.Effect.Map

open import Data.Nat
open import Data.List as List
open import Data.Maybe as Maybe
{-
open import Level using (Level)
open import Data.Bool.Base using (Bool; false; true)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe ; nothing; just)
open import Data.Nat.Base as ℕ using (ℕ; suc; zero; pred)
open import Data.Product.Base as Prod using (∃; _×_; proj₁; proj₂; _,_; -,_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.These.Base as These using (These; this; that; these)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Function.Base using (id; _∘′_; _∘_; const)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl)
open import Relation.Unary using (Pred; Decidable; U; ∅)
open import Relation.Unary.Properties using (U?; ∅?)
open import Relation.Nullary.Decidable using (does)
-}

private
  variable
    ℓ ℓ′ : Level
    A B C : 𝒰 ℓ

infixr 5 _∷¹_

record List⁺ (A : 𝒰 ℓ) : 𝒰 ℓ where
  constructor _∷¹_
  field
    hd : A
    tl : List A

open List⁺ public

uncons : List⁺ A → A × List A
uncons (hd ∷¹ tl) = hd , tl

[_] : A → List⁺ A
[ x ] = x ∷¹ []

infixr 5 _∷⁺_

_∷⁺_ : A → List⁺ A → List⁺ A
x ∷⁺ y ∷¹ xs = x ∷¹ y ∷ xs

len : List⁺ A → ℕ
len (x ∷¹ xs) = suc (List.length xs)

------------------------------------------------------------------------
-- Conversion

to-list : List⁺ A → List A
to-list (x ∷¹ xs) = x ∷ xs

{-
fromList : List A → Maybe (List⁺ A)
fromList []       = nothing
fromList (x ∷ xs) = just (x ∷ xs)

fromVec : ∀ {n} → Vec A (suc n) → List⁺ A
fromVec (x ∷ xs) = x ∷ Vec.toList xs

toVec : (xs : List⁺ A) → Vec A (length xs)
toVec (x ∷ xs) = x ∷ Vec.fromList xs

lift : (∀ {m} → Vec A (suc m) → ∃ λ n → Vec B (suc n)) →
       List⁺ A → List⁺ B
lift f xs = fromVec (proj₂ (f (toVec xs)))

------------------------------------------------------------------------
-}
-- Other operations

map⁺ : (A → B) → List⁺ A → List⁺ B
map⁺ f (x ∷¹ xs) = (f x ∷¹ mapₗ f xs)

{-
replicate : ∀ n → n ≢ 0 → A → List⁺ A
replicate n n≢0 a = a ∷ List.replicate (pred n) a

-- when dropping more than the size of the length of the list, the
-- last element remains
drop+ : ℕ → List⁺ A → List⁺ A
drop+ zero    xs           = xs
drop+ (suc n) (x ∷ [])     = x ∷ []
drop+ (suc n) (x ∷ y ∷ xs) = drop+ n (y ∷ xs)
-}

-- Right fold. Note that s is only applied to the last element (see
-- the examples below).

foldr : (A → B → B) → (A → B) → List⁺ A → B
foldr {A = A} {B = B} c s (x ∷¹ xs) = foldr′ x xs
  where
  foldr′ : A → List A → B
  foldr′ x []       = s x
  foldr′ x (y ∷ xs) = c x (foldr′ y xs)

-- Right fold.

foldr₁ : (A → A → A) → List⁺ A → A
foldr₁ f = foldr f id

-- Left fold. Note that s is only applied to the first element (see
-- the examples below).

foldl : (B → A → B) → (A → B) → List⁺ A → B
foldl c s (x ∷¹ xs) = List.fold-l c (s x) xs

-- Left fold.

foldl₁ : (A → A → A) → List⁺ A → A
foldl₁ f = foldl f id

-- Append (several variants).

infixr 5 _⁺++⁺_ _++⁺_ _⁺++_

_⁺++⁺_ : List⁺ A → List⁺ A → List⁺ A
(x ∷¹ xs) ⁺++⁺ (y ∷¹ ys) = x ∷¹ (xs List.++ y ∷ ys)

_⁺++_ : List⁺ A → List A → List⁺ A
(x ∷¹ xs) ⁺++ ys = x ∷¹ (xs List.++ ys)

_++⁺_ : List A → List⁺ A → List⁺ A
xs ++⁺ ys = List.rec ys _∷⁺_ xs

concat⁺ : List⁺ (List⁺ A) → List⁺ A
concat⁺ (xs ∷¹ xss) = xs ⁺++ List.concat (mapₗ to-list xss)

concat-map⁺ : (A → List⁺ B) → List⁺ A → List⁺ B
concat-map⁺ f = concat⁺ ∘ map⁺ f

{-
ap : List⁺ (A → B) → List⁺ A → List⁺ B
ap fs as = concatMap (λ f → map f as) fs

-- Inits

inits : List A → List⁺ (List A)
inits xs = [] ∷ List.Inits.tail xs

-- Tails

tails : List A → List⁺ (List A)
tails xs = xs ∷ List.Tails.tail xs
-}

-- Reverse

reverse⁺ : List⁺ A → List⁺ A
reverse⁺ (hd ∷¹ tl) =
  let r = reverse tl in
  Maybe.rec (hd ∷¹ []) (_∷¹ snoc r hd) (r !ᵐ 0)

{-
-- Align and Zip

alignWith : (These A B → C) → List⁺ A → List⁺ B → List⁺ C
alignWith f (a ∷ as) (b ∷ bs) = f (these a b) ∷ List.alignWith f as bs

zipWith : (A → B → C) → List⁺ A → List⁺ B → List⁺ C
zipWith f (a ∷ as) (b ∷ bs) = f a b ∷ List.zipWith f as bs

unalignWith : (A → These B C) → List⁺ A → These (List⁺ B) (List⁺ C)
unalignWith f = foldr (These.alignWith mcons mcons ∘′ f)
                    (These.map [_] [_] ∘′ f)

  where mcons : ∀ {e} {E : Set e} → These E (List⁺ E) → List⁺ E
        mcons = These.fold [_] id _∷⁺_

unzipWith : (A → B × C) → List⁺ A → List⁺ B × List⁺ C
unzipWith f (a ∷ as) = Prod.zip _∷_ _∷_ (f a) (List.unzipWith f as)

align : List⁺ A → List⁺ B → List⁺ (These A B)
align = alignWith id

zip : List⁺ A → List⁺ B → List⁺ (A × B)
zip = zipWith _,_

unalign : List⁺ (These A B) → These (List⁺ A) (List⁺ B)
unalign = unalignWith id

unzip : List⁺ (A × B) → List⁺ A × List⁺ B
unzip = unzipWith id

-- Snoc.

infixl 5 _∷ʳ_ _⁺∷ʳ_

_∷ʳ_ : List A → A → List⁺ A
[]       ∷ʳ y = [ y ]
(x ∷ xs) ∷ʳ y = x ∷ (xs List.∷ʳ y)

_⁺∷ʳ_ : List⁺ A → A → List⁺ A
xs ⁺∷ʳ x = toList xs ∷ʳ x

-- A snoc-view of non-empty lists.

infixl 5 _∷ʳ′_

data SnocView {A : Set a} : List⁺ A → Set a where
  _∷ʳ′_ : (xs : List A) (x : A) → SnocView (xs ∷ʳ x)

snocView : (xs : List⁺ A) → SnocView xs
snocView (x ∷ xs)              with List.initLast xs
snocView (x ∷ .[])             | []            = []       ∷ʳ′ x
snocView (x ∷ .(xs List.∷ʳ y)) | xs List.∷ʳ′ y = (x ∷ xs) ∷ʳ′ y

-- The last element in the list.

private
  last′ : ∀ {l} → SnocView {A = A} l → A
  last′ (_ ∷ʳ′ y) = y

last : List⁺ A → A
last = last′ ∘ snocView

-- Groups all contiguous elements for which the predicate returns the
-- same result into lists. The left sums are the ones for which the
-- predicate holds, the right ones are the ones for which it doesn't.
groupSeqsᵇ : (A → Bool) → List A → List (List⁺ A ⊎ List⁺ A)
groupSeqsᵇ p []       = []
groupSeqsᵇ p (x ∷ xs) with p x | groupSeqsᵇ p xs
... | true  | inj₁ xs′ ∷ xss = inj₁ (x ∷⁺ xs′) ∷ xss
... | true  | xss            = inj₁ [ x ]      ∷ xss
... | false | inj₂ xs′ ∷ xss = inj₂ (x ∷⁺ xs′) ∷ xss
... | false | xss            = inj₂ [ x ]      ∷ xss

-- Groups all contiguous elements /not/ satisfying the predicate into
-- lists. Elements satisfying the predicate are dropped.
wordsByᵇ : (A → Bool) → List A → List (List⁺ A)
wordsByᵇ p = List.mapMaybe Sum.[ const nothing , just ] ∘ groupSeqsᵇ p

groupSeqs : {P : Pred A p} → Decidable P → List A → List (List⁺ A ⊎ List⁺ A)
groupSeqs P? = groupSeqsᵇ (does ∘ P?)

wordsBy : {P : Pred A p} → Decidable P → List A → List (List⁺ A)
wordsBy P? = wordsByᵇ (does ∘ P?)

-- Inverse operation for groupSequences.
ungroupSeqs : List (List⁺ A ⊎ List⁺ A) → List A
ungroupSeqs = List.concat ∘ List.map Sum.[ toList , toList ]

------------------------------------------------------------------------
-- Examples

-- Note that these examples are simple unit tests, because the type
-- checker verifies them.

private
 module Examples {A B : Set}
                 (_⊕_ : A → B → B)
                 (_⊗_ : B → A → B)
                 (_⊙_ : A → A → A)
                 (f : A → B)
                 (a b c : A)
                 where

  hd : head (a ∷⁺ b ∷⁺ [ c ]) ≡ a
  hd = refl

  tl : tail (a ∷⁺ b ∷⁺ [ c ]) ≡ b ∷ c ∷ []
  tl = refl

  mp : map f (a ∷⁺ b ∷⁺ [ c ]) ≡ f a ∷⁺ f b ∷⁺ [ f c ]
  mp = refl

  right : foldr _⊕_ f (a ∷⁺ b ∷⁺ [ c ]) ≡ (a ⊕ (b ⊕ f c))
  right = refl

  right₁ : foldr₁ _⊙_ (a ∷⁺ b ∷⁺ [ c ]) ≡ (a ⊙ (b ⊙ c))
  right₁ = refl

  left : foldl _⊗_ f (a ∷⁺ b ∷⁺ [ c ]) ≡ ((f a ⊗ b) ⊗ c)
  left = refl

  left₁ : foldl₁ _⊙_ (a ∷⁺ b ∷⁺ [ c ]) ≡ ((a ⊙ b) ⊙ c)
  left₁ = refl

  ⁺app⁺ : (a ∷⁺ b ∷⁺ [ c ]) ⁺++⁺ (b ∷⁺ [ c ]) ≡
          a ∷⁺ b ∷⁺ c ∷⁺ b ∷⁺ [ c ]
  ⁺app⁺ = refl

  ⁺app : (a ∷⁺ b ∷⁺ [ c ]) ⁺++ (b ∷ c ∷ []) ≡
          a ∷⁺ b ∷⁺ c ∷⁺ b ∷⁺ [ c ]
  ⁺app = refl

  app⁺ : (a ∷ b ∷ c ∷ []) ++⁺ (b ∷⁺ [ c ]) ≡
          a ∷⁺ b ∷⁺ c ∷⁺ b ∷⁺ [ c ]
  app⁺ = refl

  conc : concat ((a ∷⁺ b ∷⁺ [ c ]) ∷⁺ [ b ∷⁺ [ c ] ]) ≡
         a ∷⁺ b ∷⁺ c ∷⁺ b ∷⁺ [ c ]
  conc = refl

  rev : reverse (a ∷⁺ b ∷⁺ [ c ]) ≡ c ∷⁺ b ∷⁺ [ a ]
  rev = refl

  snoc : (a ∷ b ∷ c ∷ []) ∷ʳ a ≡ a ∷⁺ b ∷⁺ c ∷⁺ [ a ]
  snoc = refl

  snoc⁺ : (a ∷⁺ b ∷⁺ [ c ]) ⁺∷ʳ a ≡ a ∷⁺ b ∷⁺ c ∷⁺ [ a ]
  snoc⁺ = refl

  groupSeqs-true : groupSeqs U? (a ∷ b ∷ c ∷ []) ≡
               inj₁ (a ∷⁺ b ∷⁺ [ c ]) ∷ []
  groupSeqs-true = refl

  groupSeqs-false : groupSeqs ∅? (a ∷ b ∷ c ∷ []) ≡
                inj₂ (a ∷⁺ b ∷⁺ [ c ]) ∷ []
  groupSeqs-false = refl

  groupSeqs-≡1 : groupSeqsᵇ (ℕ._≡ᵇ 1) (1 ∷ 2 ∷ 3 ∷ 1 ∷ 1 ∷ 2 ∷ 1 ∷ []) ≡
                 inj₁ [ 1 ] ∷
                 inj₂ (2 ∷⁺ [ 3 ]) ∷
                 inj₁ (1 ∷⁺ [ 1 ]) ∷
                 inj₂ [ 2 ] ∷
                 inj₁ [ 1 ] ∷
                 []
  groupSeqs-≡1 = refl

  wordsBy-true : wordsByᵇ (const true) (a ∷ b ∷ c ∷ []) ≡ []
  wordsBy-true = refl

  wordsBy-false : wordsByᵇ (const false) (a ∷ b ∷ c ∷ []) ≡
                  (a ∷⁺ b ∷⁺ [ c ]) ∷ []
  wordsBy-false = refl

  wordsBy-≡1 : wordsByᵇ (ℕ._≡ᵇ 1) (1 ∷ 2 ∷ 3 ∷ 1 ∷ 1 ∷ 2 ∷ 1 ∷ []) ≡
               (2 ∷⁺ [ 3 ]) ∷
               [ 2 ] ∷
               []
  wordsBy-≡1 = refl
-}
