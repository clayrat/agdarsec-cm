{-# OPTIONS --safe #-}

open import Foundations.Prelude
open import Meta.Effect
open Variadics _

open import Text.Parser.Types.Core using (Parameters)

module Text.Parser.Combinators {ℓ} {P : Parameters ℓ} where

open import Data.Reflects
open import Data.Dec
open import Data.Nat -- .Base using (ℕ; _≤_; _<_)
open import Data.Nat.Order.Base
open import Data.Bool -- .Base as Bool using (Bool; if_then_else_; not; _∧_)
open import Data.List as List -- .Base as List using (_∷_; []; null)
open import Data.Maybe as Maybe -- .Base as M using (just; nothing; maybe)

-- open import Data.Nat -- .Base using (suc; NonZero)
-- open import Data.Product as Product using (Σ-syntax; _,_; proj₁; proj₂; uncurry)

open import Data.Sum -- .Base as Sum using (inj₁; inj₂)
open import Data.Vec.Inductive --- Base as Vec using (_∷_; [])

open import Logic.Discreteness

open import Level.Bounded as Level≤ -- hiding (map)

-- open import Relation.Unary using (IUniversal; _⇒_)

open import Induction.Nat.Strong as Box using (□_)
open import Data.List.NonEmpty as List⁺ -- using (_∷⁺_ ; _∷_)

-- open import Data.Nat.Properties as Nat using (≤-refl; ≤-trans; <⇒≤; <-trans)
-- import Data.List.Relation.Unary.Any as Any
-- open import Relation.Nullary using (yes; no)
-- open import Relation.Nullary.Decidable using (⌊_⌋)
-- open import Relation.Binary.PropositionalEquality.Decidable.Core using (DecidableEquality; decide)
-- open import Effect.Monad using (RawMonadPlus)
-- open import Function.Base using (const; _$_; _∘_; _∘′_; flip; case_of_)

open import Data.List.Sized.Interface using (Sized)

open import Text.Parser.Types.Core
open import Text.Parser.Types P
open import Text.Parser.Success P as S -- hiding (guardM)

open Parameters P

module _ ⦃ 𝕊 : Sized Tok Toks ⦄
         -- ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
         where

-- private module M = Effect M

  anyTok : ⦃ mp : Map M ⦄ ⦃ alt : Alt M ⦄
         → ∀[ Parser Tok ]
  anyTok .run-parser m≤n s =
    Maybe.rec fail (λ t → t <$ recordToken (lowerℓ (Success.value t)))
              (view (lowerℓ s))

  module _ {A B : 𝒰≤ ℓ} where

    guardMC : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
            → (A →ℓ Maybeℓ B) .ty → ∀[ Parser A ⇒ Parser B ]
    guardMC p A .run-parser m≤n s =
      do rA ← A .run-parser m≤n s
         Maybe.rec fail pure $ guardMS p rA

  module _ {A : 𝒰≤ ℓ} where

    guardC : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
          → (A →ℓ (Bool 0↑ℓ)) .ty → ∀[ Parser A ⇒ Parser A ]
    guardC p = guardMC λ a → if p a then just a else nothing

    maybeTok : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
             → (Tok →ℓ Maybeℓ A) .ty → ∀[ Parser A ]
    maybeTok p = guardMC p anyTok

    ≤-lower : {m n : ℕ} → (@0 m≤n : m ≤ n) → Parser A n → Parser A m
    ≤-lower m≤n A .run-parser p≤m = A .run-parser (≤-trans p≤m m≤n)

    <-lower : {m n : ℕ} → (@0 m<n : m < n) → Parser A n → Parser A m
    <-lower m<n = ≤-lower (<→≤ m<n)

    box : ∀[ Parser A ⇒ □ Parser A ]
    box = Box.≤-close ≤-lower

    failC : ⦃ alt : Alt M ⦄ → ∀[ Parser A ]
    failC .run-parser _ _ = fail

    infixr 3 _<|>C_
    _<|>C_ : ⦃ ch : Choice M ⦄ → ∀[ Parser A ⇒ Parser A ⇒ Parser A ]
    (A₁ <|>C A₂) .run-parser m≤n s = A₁ .run-parser m≤n s <|> A₂ .run-parser m≤n s

  module _ {A B C : 𝒰≤ ℓ} where

    lift² : ∀[ Parser A ⇒ Parser B ⇒ Parser C ]
          → ∀[ □ (Parser A) ⇒ □ (Parser B) ⇒ □ (Parser C) ]
    lift² = Box.map²

    lift²l : ∀[ Parser A ⇒ Parser B ⇒ Parser C ]
           → ∀[ □ (Parser A) ⇒ Parser B ⇒ □ (Parser C) ]
    lift²l f a b = lift² f a (box b)

    lift²r : ∀[ Parser A ⇒ Parser B ⇒ Parser C ]
           → ∀[ Parser A ⇒ □ (Parser B) ⇒ □ (Parser C) ]
    lift²r f a b = lift² f (box a) b

  module _ {A : 𝒰≤ ℓ} {ℓb} ⦃ b≤l : ℓb ≤ℓ ℓ ⦄ {B : A .ty → 𝒰 ℓb} where

    _&?>>=_ : ⦃ bd : Bind M ⦄ ⦃ ch : Choice M ⦄
            → ∀ {n} → Parser A n
            → ((a : A .ty) → (□ Parser (mk𝒰≤ (B a))) n)
            → Parser (Σℓ A λ a → Maybe (B a)) n
    (A &?>>= B) .run-parser m≤n s =
      do rA ← A .run-parser m≤n s
         let (a ^ p<m ⸴ s′) = rA
         (do rB ← (Box.call (B (lowerℓ a)) (<-≤-trans p<m m≤n)) .run-parser ≤-refl s′
             pure (and rA (mapS just rB)))
           <|>
          pure ((liftℓ (lowerℓ a , nothing)) ^ p<m ⸴ s′)

    _&>>=_ : ⦃ bd : Bind M ⦄
           → ∀ {n} → Parser A n → ((a : A .ty) → (□ Parser (mk𝒰≤ (B a))) n)
           → Parser (Σℓ A B) n
    (A &>>= B) .run-parser m≤n s =
      do rA ← A .run-parser m≤n s
         let (a ^ p<m ⸴ s′) = rA
         rB ← (Box.call (B (lowerℓ a)) (<-≤-trans p<m m≤n)) .run-parser ≤-refl s′
         pure (and rA rB)

  module _ {A B : 𝒰≤ ℓ} where

    infixr 5 _<$>C_
    _<$>C_ : ⦃ mp : Map M ⦄
           → (A →ℓ B) .ty → ∀[ Parser A ⇒ Parser B ]
    (f <$>C p) .run-parser m≤n s = mapS f <$> p .run-parser m≤n s

    infixr 5 _<$C_
    _<$C_ : ⦃ mp : Map M ⦄
          → B .ty → ∀[ Parser A ⇒ Parser B ]
    b <$C p = (λ _ → b) <$>C p  -- TODO const is erased

  module _ {A : 𝒰≤ ℓ} {ℓb} ⦃ b≤l : ℓb ≤ℓ ℓ ⦄ {B : (Maybeℓ A) .ty → 𝒰 ℓb} where

    _?&>>=_ : ⦃ bd : Bind M ⦄ ⦃ ch : Choice M ⦄
            → ∀ {n} → Parser A n → ((ma : (Maybeℓ A) .ty) → Parser (mk𝒰≤ (B ma)) n)
            → Parser (Σℓ (Maybeℓ A) B) n
    (_?&>>=_ {n} pA pB) .run-parser m≤n s =
      let p : Parser (A ⊎ℓ mk𝒰≤ (B nothing)) n
          p = inl <$>C pA <|>C inr <$>C pB nothing
        in
      do (v ^ p<m ⸴ ts) ← p .run-parser m≤n s
         ([ (λ a → mapS (just a ,_) ∘ <-lift p<m
                   <$> pB (just a) .run-parser (≤-trans (<→≤ p<m) m≤n) ts)
          , (λ b → pure ((liftℓ (nothing , b)) ^ p<m ⸴ ts))
          ]ᵤ (lowerℓ v))

  module _ {A B : 𝒰≤ ℓ} where

    _&?>>=′_ : ⦃ bd : Bind M ⦄ ⦃ ch : Choice M ⦄
             → ∀[   Parser A ⇒ ((λ _ → A .ty) ⇒ □ Parser B)
                  ⇒ Parser (A ×ℓ Maybeℓ B) ]
    (A &?>>=′ B) .run-parser m≤n s =
      do rA ← A .run-parser m≤n s
         let (a ^ p<m ⸴ s′) = rA
         (do rB ← (Box.call (B (lowerℓ a)) (<-≤-trans p<m m≤n)) .run-parser ≤-refl s′
             pure (and′ rA (mapS just rB)))
           <|>
          pure ((liftℓ (lowerℓ a , nothing)) ^ p<m ⸴ s′)

    _&>>=′_ : ⦃ bd : Bind M ⦄
           → ∀[ Parser A ⇒ ((λ _ → A .ty) ⇒ □ Parser B) ⇒ Parser (A ×ℓ B) ]
    (A &>>=′ B) .run-parser m≤n s =
      do rA ← A .run-parser m≤n s
         let (a ^ p<m ⸴ s′) = rA
         rB ← (Box.call (B (lowerℓ a)) (<-≤-trans p<m m≤n)) .run-parser ≤-refl s′
         pure (and′ rA rB)

    _?&>>=′_ : ⦃ bd : Bind M ⦄ ⦃ ch : Choice M ⦄
             → ∀[ Parser A ⇒ ((λ _ → (Maybeℓ A) .ty) ⇒ Parser B) ⇒
                  Parser (Maybeℓ A ×ℓ B) ]
    _?&>>=′_ = _?&>>=_

    _>>=C_ : ⦃ bd : Bind M ⦄
          → ∀[ Parser A ⇒ ((λ _ → A .ty) ⇒ □ Parser B) ⇒ Parser B ]
    A >>=C B = snd <$>C A &>>=′ B

    infixl 4 _<&>C_ _<&C_ _&>C_
    _<&>C_ : ⦃ bd : Bind M ⦄
           → ∀[ Parser A ⇒ □ Parser B ⇒ Parser (A ×ℓ B) ]
    A <&>C B = A &>>=′ (λ _ → B)

    _<&C_ : ⦃ bd : Bind M ⦄
          → ∀[ Parser A ⇒ □ Parser B ⇒ Parser A ]
    A <&C B = fst <$>C (A <&>C B)

    _&>C_ : ⦃ bd : Bind M ⦄
          → ∀[ Parser A ⇒ □ Parser B ⇒ Parser B ]
    A &>C B = snd <$>C (A <&>C B)

  module _ {A : 𝒰≤ ℓ} where

    alts : ⦃ alt : Alt M ⦄
         → ∀[ List ∘ Parser A ⇒ Parser A ]
    alts = fold-r _<|>C_ failC

    ands : ⦃ bs : Bind M ⦄
         → ∀[ List⁺ ∘ Parser A ⇒ Parser (List⁺ℓ A) ]
    ands ps = List⁺.foldr₁
                (λ p ps → List⁺._⁺++⁺_ $²_ <$>C (p <&>C box ps))
                (List⁺.map⁺ (List⁺.[_] <$>C_) ps)

  module _ {A B : 𝒰≤ ℓ} where

    infixl 4 _<*>C_
    _<*>C_ : ⦃ bd : Bind M ⦄
           → ∀[ Parser (A →ℓ B) ⇒ □ Parser A ⇒ Parser B ]
    F <*>C A = (_$_ $²_) <$>C (F <&>C A)

    infixl 4 _<&M>_ _<&M_ _&M>_
    _<&M>_ : ⦃ bs : Bind M ⦄
           → ∀[ Parser A ⇒ (λ _ → Effect.₀ M (Liftℓ B)) ⇒ Parser (A ×ℓ B) ]
    (A <&M> B) .run-parser m≤n s =
      do rA ← A .run-parser m≤n s
         b ← B
         pure (mapS (_, lowerℓ b) rA)

    _<&M_ : ⦃ bd : Bind M ⦄
          → ∀[ Parser A ⇒ (λ _ → Effect.₀ M (Liftℓ B)) ⇒ Parser A ]
    A <&M B = fst <$>C (A <&M> B)

    _&M>_ : ⦃ bd : Bind M ⦄
          → ∀[ Parser A ⇒ (λ _ → Effect.₀ M (Liftℓ B)) ⇒ Parser B ]
    A &M> B = snd <$>C (A <&M> B)

    infixl 4 _<&?>_ _<&?_ _&?>_
    _<&?>_ : ⦃ bd : Bind M ⦄ ⦃ ch : Choice M ⦄
           → ∀[ Parser A ⇒ □ Parser B ⇒ Parser (A ×ℓ Maybeℓ B) ]
    A <&?> B = A &?>>=′ λ _ → B

    _<&?_ : ⦃ bd : Bind M ⦄ ⦃ ch : Choice M ⦄
          → ∀[ Parser A ⇒ □ Parser B ⇒ Parser A ]
    A <&? B = fst <$>C (A <&?> B)

    _&?>_ : ⦃ bd : Bind M ⦄ ⦃ ch : Choice M ⦄
          → ∀[ Parser A ⇒ □ Parser B ⇒ Parser (Maybeℓ B) ]
    A &?> B = snd <$>C (A <&?> B)

    infixr 3 _<⊎>_
    _<⊎>_ : ⦃ bd : Bind M ⦄ ⦃ ch : Choice M ⦄
          → ∀[ Parser A ⇒ Parser B ⇒ Parser (A ⊎ℓ B) ]
    A <⊎> B = inl <$>C A <|>C inr <$>C B

  module _ {A B R : 𝒰≤ ℓ} where

    <[_,_]> : ⦃ bd : Bind M ⦄
            → ∀[ (λ _ → A .ty → R. ty) ⇒ ((λ _ → B .ty) ⇒ □ Parser R)
                 ⇒ Parser (A ⊎ℓ B) ⇒ Parser R ]
    <[ f , k ]> u .run-parser m≤n s =
      do ru ← u .run-parser m≤n s
         let (v ^ p<m ⸴ s′) = ru
         ([ (λ a → pure (liftℓ (f a) ^ p<m ⸴ s′))
          , (λ b → <-lift p<m <$> (Box.call (k b) (<-≤-trans p<m m≤n)) .run-parser ≤-refl s′)
          ]ᵤ (lowerℓ v))

  module _ {A B : 𝒰≤ ℓ} where

    infixl 4 _<?&>_ _<?&_ _?&>_
    _<?&>_ : ⦃ bd : Bind M ⦄ ⦃ ch : Choice M ⦄
           → ∀[ Parser A ⇒ Parser B ⇒ Parser (Maybeℓ A ×ℓ B) ]
    A <?&> B = just <$>C A <&>C box B <|>C (nothing ,_) <$>C B

    _<?&_ : ⦃ bd : Bind M ⦄ ⦃ ch : Choice M ⦄
          → ∀[ Parser A ⇒ Parser B ⇒ Parser (Maybeℓ A) ]
    A <?& B = fst <$>C (A <?&> B)

    _?&>_ : ⦃ bd : Bind M ⦄ ⦃ ch : Choice M ⦄
          → ∀[ Parser A ⇒ Parser B ⇒ Parser B ]
    A ?&> B = snd <$>C (A <?&> B)

    infixl 4 _<M&>_ _<M&_ _M&>_
    _<M&>_ : ⦃ bd : Bind M ⦄
           → ∀[ (λ _ → Effect.₀ M (Liftℓ A)) ⇒ Parser B ⇒ Parser (A ×ℓ B) ]
    (A <M&> B) .run-parser m≤n s =
      do a ← A
         mapS (lowerℓ a ,_) <$> B .run-parser m≤n s

    _<M&_ : ⦃ bd : Bind M ⦄
          → ∀[ (λ _ → Effect.₀ M (Liftℓ A)) ⇒ Parser B ⇒ Parser A ]
    A <M& B = fst <$>C (A <M&> B)

    _M&>_ : ⦃ bd : Bind M ⦄
          → ∀[ (λ _ → Effect.₀ M (Liftℓ A)) ⇒ Parser B ⇒ Parser B ]
    A M&> B = snd <$>C (A <M&> B)

  module _ {A B C : 𝒰≤ ℓ} where

    between : ⦃ bd : Bind M ⦄
            → ∀[ Parser A ⇒ □ Parser C ⇒ □ Parser B ⇒ Parser B ]
    between A C B = A &>C B <&C C

    between? : ⦃ bd : Bind M ⦄ ⦃ ch : Choice M ⦄
             → ∀[ Parser A ⇒ □ Parser C ⇒ Parser B ⇒ Parser B ]
    between? A C B = between A C (box B) <|>C B

  module _ ⦃ d : is-discrete (Tok .ty) ⦄ where

    anyOf : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
          → (Listℓ Tok) .ty → ∀[ Parser Tok ]
    anyOf ts =
      guardC (λ c → _and_ (not (is-nil? ts)) -- wtf? also seems redundant
                    (List.has c ts))
             anyTok

    exact : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
          → Tok .ty → ∀[ Parser Tok ]
    exact t = guardC (_=? t) anyTok

    exacts : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
           → (List⁺ℓ Tok) .ty → ∀[ Parser (List⁺ℓ Tok) ]
    exacts ts = ands (List⁺.map⁺ (λ t → exact t) ts)

    noneOf : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
           → (Listℓ Tok) .ty → ∀[ Parser Tok ]
    noneOf ts = maybeTok λ t → if List.has t ts then nothing else just t

    anyTokenBut : ⦃ bd : Bind M ⦄ ⦃ alt : Alt M ⦄
                → Tok .ty → ∀[ Parser Tok ]
    anyTokenBut c = maybeTok λ t → if c =? t then nothing else just t

  module _ {A : 𝒰≤ ℓ} where

    schainl-ty : ℕ → 𝒰 (ℓ ⊔ Effect.adj M ℓ)
    schainl-ty = Success Toks A ⇒ □ Parser (A →ℓ A) ⇒ Effect.₀ M ∘ Success Toks A

    schainl : ⦃ bd : Bind M ⦄ ⦃ ch : Choice M ⦄
            → ∀[ schainl-ty ]
    schainl = Box.fix schainl-ty $ λ rec sA op → rest rec sA op <|> pure sA
      where
      rest : ∀[ □ schainl-ty ⇒ schainl-ty ]
      rest rec (a ^ p<m ⸴ s) op =
        do sOp ← (Box.call op p<m) .run-parser ≤-refl s
           r ← Box.call rec p<m (mapS (_$ lowerℓ a) sOp) (Box.<↓ p<m op)
           pure (<-lift p<m r)

    iterate : ⦃ bd : Bind M ⦄ ⦃ ch : Choice M ⦄
            → ∀[ Parser A ⇒ □ Parser (A →ℓ A) ⇒ Parser A ]
    iterate a op .run-parser m≤n s =
      do sA ← a .run-parser m≤n s
         schainl sA $ Box.≤↓ m≤n op

  module _ {A B : 𝒰≤ ℓ} where

    hchainl : ⦃ bd : Bind M ⦄ ⦃ ch : Choice M ⦄
            → ∀[ Parser A ⇒ □ Parser (A →ℓ (B →ℓ A)) ⇒ □ Parser B ⇒ Parser A ]
    hchainl A op B = iterate A (Box.map² _<*>C_ (Box.map (flip <$>C_) op) (Box.duplicate B))

  module _ {A : 𝒰≤ ℓ} where

    chainl1 : ⦃ bd : Bind M ⦄ ⦃ ch : Choice M ⦄
            → ∀[ Parser A ⇒ □ Parser (A →ℓ (A →ℓ A)) ⇒ Parser A ]
    chainl1 a op = hchainl a op (box a)

    chainr1-ty : ℕ → 𝒰 (ℓ ⊔ Effect.adj M ℓ)
    chainr1-ty = Parser A ⇒ □ Parser (A →ℓ (A →ℓ A)) ⇒ Parser A

    chainr1 : ⦃ bd : Bind M ⦄ ⦃ ch : Choice M ⦄
            → ∀[ chainr1-ty ]
    chainr1 = Box.fix chainr1-ty $ λ rec A op →
                mk-parser λ m≤n s →
                do sA ← A .run-parser m≤n s
                   rest (Box.≤↓ m≤n rec) (≤-lower m≤n A) (Box.≤↓ m≤n op) sA <|> pure sA
      where
      rest : ∀[ □ chainr1-ty ⇒ Parser A ⇒ □ Parser (A →ℓ (A →ℓ A)) ⇒
                Success Toks A ⇒ Effect.₀ M ∘ Success Toks A ]
      rest rec A op sA@(a ^ m<n ⸴ s) =
        do sOp ← (Box.call op m<n) .run-parser ≤-refl s
           let (f ^ p<m ⸴ s′) = sOp
           let @0 p<n : _ < _
               p<n = <-trans p<m m<n
           let rec′ = Box.call rec p<n (<-lower p<n A) (Box.<↓ p<n op)
           <-lift p<n ∘ mapS (lowerℓ f (lowerℓ a) $_) <$> rec′ .run-parser ≤-refl s′

    head+tail : ⦃ bd : Bind M ⦄ ⦃ ch : Choice M ⦄
              → ∀[ Parser A ⇒ □ Parser A ⇒ Parser (List⁺ℓ A) ]
    head+tail hd tl =
      reverse⁺ <$>C (iterate {A = List⁺ℓ A}
                             (List⁺.[_] <$>C hd)
                             (Box.map (List⁺._∷⁺_ <$>C_) tl))

    list⁺ : ⦃ bd : Bind M ⦄ ⦃ ch : Choice M ⦄
          → ∀[ Parser A ⇒ Parser (List⁺ℓ A) ]
    list⁺ = Box.fix (Parser A ⇒ Parser (List⁺ℓ A)) $ λ rec pA →
                 ((λ hd → (hd ∷¹_) ∘ Maybe.rec [] List⁺.to-list) $²_)
            <$>C (pA <&?> (Box.app rec (box pA)))

    replicateC : ⦃ bd : Bind M ⦄
               → (n : ℕ) → { z< : 0 < n } → ∀[ Parser A ⇒ Parser (Vecℓ A n) ]
    replicateC  zero           {z<} p = false! z<
    replicateC (suc zero)           p = (_∷ []) <$>C p
    replicateC (suc n@(suc _))      p = (_∷_ $²_) <$>C (p <&>C box (replicateC n {z< = z<s} p))
