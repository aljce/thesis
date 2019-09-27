open import Level using (_⊔_)
open import Size using (Size; Size<_; ∞; ↑_)
open import Data.Nat using (ℕ; _+_)
open ℕ
open import Data.Vec using (Vec)
open Vec
open import Relation.Binary using (Transitive)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; refl) renaming (trans to ≡-trans)

module Stream where

record Thunk {a} (f : Size → Set a) (i : Size) : Set a where
  coinductive
  field
    force : ∀ (j : Size< i) → f j
open Thunk

infixr 5 _∷_
record Stream {a} (A : Set a) (i : Size) : Set a where
  inductive
  constructor _∷_
  field
    head : A
    tail : Thunk (Stream A) i
open Stream

map : ∀ {a b} {A : Set a} {B : Set b} → (i : Size) → (A → B) → Stream A i → Stream B i
map i f (x ∷ xs) = f x ∷ λ where .force j → map j f (force xs j)

index : ∀ {a} {A : Set a} → ℕ → Stream A ∞ → A
index zero (x ∷ _) = x
index (suc n) (_ ∷ xs) = index n (force xs ∞)

take : ∀ {a} {A : Set a} → (n : ℕ) → Stream A ∞ → Vec A n
take zero _ = []
take (suc n) (x ∷ xs) = x ∷ take n (force xs ∞)

zipWith
  : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  → (i : Size) → (A → B → C) → Stream A i → Stream B i → Stream C i
zipWith i _⊕_ (a ∷ as) (b ∷ bs) = a ⊕ b ∷ λ where .force j → zipWith j _⊕_ (force as j) (force bs j)

fib : ∀ i → Stream ℕ i
fib i = 0 ∷ λ where .force j → 1 ∷ λ where .force k → zipWith k _+_ (fib k) (force (tail (fib j)) k)

module Lexicographic {a r} {A : Set a} (_<_ : A → A → Set r) (<-trans : Transitive _<_) where

  infix 3 _⊢_≤_
  data _⊢_≤_ (i : Size) (xs : Stream A ∞) (ys : Stream A ∞) : Set (a ⊔ r) where
    <-lex : head xs < head ys → i ⊢ xs ≤ ys
    ≡-lex : head xs ≡ head ys → Thunk (λ j → j ⊢ force (tail xs) ∞ ≤ force (tail ys) ∞) i → i ⊢ xs ≤ ys

  ≤-refl : ∀ i {xs : Stream A ∞} → i ⊢ xs ≤ xs
  ≤-refl i = ≡-lex refl λ where .force j → ≤-refl j

  ≤-trans : ∀ i {xs : Stream A ∞} {ys : Stream A ∞} {zs : Stream A ∞} → i ⊢ xs ≤ ys → i ⊢ ys ≤ zs → i ⊢ xs ≤ zs
  ≤-trans i (<-lex x<y) (<-lex y<z) = <-lex (<-trans x<y y<z)
  ≤-trans i (<-lex x<y) (≡-lex y≡z _) rewrite y≡z = <-lex x<y
  ≤-trans i (≡-lex x≡y _) (<-lex y<z) rewrite sym x≡y = <-lex y<z
  ≤-trans i (≡-lex x≡y xs≤ys) (≡-lex y≡z ys≤zs) =
    ≡-lex (≡-trans x≡y y≡z) λ where .force j → ≤-trans j (force xs≤ys j) (force ys≤zs j)

  -- open import Algebra.Structures {A = A} _≡_ using (IsSemigroup)
  -- module _ (_∙_ : A → A → A) (∙-isSemigroup : IsSemigroup _∙_) where

  --   infix 4 _⊙_
  --   _⊙_ : ∀ {i} → Stream A i → Stream A i → Stream A i
  --   _⊙_ {i} = zipWith i _∙_

  --   ⊙-mono-≤
  --     : ∀ {i} {as : Stream A ∞} {bs : Stream A ∞} {cs : Stream A ∞} {ds : Stream A ∞}
  --     → i ⊢ as ≤ cs
  --     → i ⊢ bs ≤ ds
  --     → i ⊢ as ⊙ bs ≤ cs ⊙ ds
  --   ⊙-mono-≤ (<-lex a<c) (<-lex b<d) = <-lex {!!}
  --   ⊙-mono-≤ (<-lex a<c) (≡-lex b≡d bs≤ds) = <-lex {!!}
  --   ⊙-mono-≤ (≡-lex a≡c as≤cs) (<-lex b<d) = <-lex {!!}
  --   ⊙-mono-≤ (≡-lex a≡c as≤cs) (≡-lex b≡d bs≤ds) = ≡-lex {!!} λ where .force j → ⊙-mono-≤ (force as≤cs j) (force bs≤ds j)

-- module Merge {a} {A : Set a} where
--   open import Data.Product using (_×_)

--   merge : ∀ i → Stream A i → Stream A i → Stream A i
--   merge i (x ∷ xs) ys = x ∷ λ where .force j → merge j ys (force xs j)

--   split : ∀ i → Stream A i → Stream A i × Stream A i
--   split i (x ∷ xs) = {!!}

module Test where

  fib[7] : index 7 (fib ∞) ≡ 13
  fib[7] = refl

  fib[0-10] : take 10 (fib ∞) ≡ 0 ∷ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ 13 ∷ 21 ∷ 34 ∷ []
  fib[0-10] = refl
