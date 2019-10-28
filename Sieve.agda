open import Data.Nat using (ℕ)
open ℕ

open import Size using (Size; ∞; Size<_)
open import Codata.Thunk using (Thunk; force)

record Sieve {a} (f : ℕ → Set a) (n : ℕ) (i : Size) : Set a where
  inductive
  constructor _∷_
  field
    head : f n
    tail : Thunk (Sieve f (suc n)) i
open Sieve

module _ {a b} {f : ℕ → Set a} {g : ℕ → Set b} where

  map : ∀ {m} {i} → (∀ n → f n → g n) → Sieve f m i → Sieve g m i
  map {m = m} eta (f ∷ fs) = eta m f ∷ λ where .force → map eta (force fs)

open import Data.Nat using (_≤_; _<_)

data _⊢_≤_<_ (i : Size) : ℕ → ℕ → ℕ → Set where
  ≤-here : ∀ {x n} → x < n → i ⊢ x ≤ x < n
  ≤-next : ∀ {m x n} {j : Size< i} → j ⊢ suc m ≤ x < n → i ⊢ m ≤ x < n

data 𝕀 (i : Size) : Set where
  zero : 𝕀 i
  suc  : ∀ {j : Size< i} → 𝕀 j → 𝕀 i

module _ {a} {f : ℕ → Set a} where

  index : ∀ {m x n} {i} → Sieve f m i → i ⊢ m ≤ x < n → f x
  index = {!!}

  tabulate : ∀ {m} {i} → (∀ n → (∀ x → m ≤ x → x < n → i ⊢ m ≤ x < n) → f n) → Sieve f m i
  tabulate {m} gen = gen m {!!} ∷ λ where .force → tabulate λ n ix → gen n λ x m≤x x<n → {!!}
    -- where
    -- loop : ∀ {m} {i} → (∀ a) Sieve f m i
    -- loop {m} = {!!}

-- _⊢_<_ : Size → ℕ → ℕ → Set
-- i ⊢ m < n = i ⊢ suc m ≤ n

-- module _ {a} {f : ℕ → Set a} where

--   index : ∀ {m n} {i} → Sieve f m i → i ⊢ m ≤ n → f n
--   index = {!!}

--   tabulate : ∀ {m} {i} → (∀ n → i ⊢ m ≤ n → f n) → Sieve f m i
--   tabulate = {!!}


-- data _⊢_≤_ (i : Size) : ℕ → ℕ → Set where
--   ≤-same : ∀ {n} → i ⊢ n ≤ n
--   ≤-next : ∀ {m n} {j : Size< i} → j ⊢ suc m ≤ n → i ⊢ m ≤ n

-- _⊢_<_ : Size → ℕ → ℕ → Set
-- i ⊢ m < n = i ⊢ suc m ≤ n

-- module _ {a} {f : ℕ → Set a} where

--   index : ∀ {m n} {i} → Sieve f m i → i ⊢ m ≤ n → f n
--   index xs ≤-same = head xs
--   index xs (≤-next i) = index (force (tail xs)) i

--   tabulate : ∀ {m} {i} → (∀ n → i ⊢ m ≤ n → f n) → Sieve f m i
--   tabulate {m} gen = gen m ≤-same ∷ λ where .force → tabulate λ n m<n → gen n (≤-next m<n)




-- open import Data.Nat.Divisibility using (∣-refl)
-- open import Data.Nat.Properties using (≤-isTotalOrder; _≤?_)
-- open import Heap.Indexed _≤_ ≤-isTotalOrder IsComposite
-- open import Data.Maybe using (Maybe)
-- open Maybe

-- unsafe-assert-prime : ∀ n → 1 < n → IsPrime n
-- unsafe-assert-prime n 1<n = IsPrime✓ 1<n n-primality
--   where
--   postulate
--     evil : ⊥
--   n-primality : ∀ {i} → 1 < i → i ∣ n → i ≡ n
--   n-primality {i} _ i∣n with <-cmp i n
--   ... | tri< _ _ _ = ⊥-elim evil -- !UNSOUND!
--   ... | tri≈ _ i≡n _ = i≡n
--   ... | tri> _ _ i>n = ⊥-elim (<-irrefl (a∣n∧a>n⇒n≡0 i∣n i>n) (<-trans 0<1+n 1<n))

-- sieve : ∀ {i} → Sieve Primality 2 i
-- sieve = Prime 2-isPrime ∷ λ where .force → loop 3 (from-yes (1 <? 3)) (singleton 4 ⟨ from-yes (3 ≤? 4) ⟩ 4-isComposite)
--   where
--   open IsComposite
--   next : ∀ {n} → (c : IsComposite n) → IsComposite (p c + n)
--   next (IsComposite✓ p p<n p-isPrime p∣n) = IsComposite✓ p {!!} p-isPrime {!!}
--   adjust : ∀ x → Heap ⟨ x ⟩ → Heap ⟨ 1 + x ⟩
--   adjust x heap₁ with min-view heap₁
--   ... | Node c (IsComposite✓ p p<c p-isPrime p∣c) ⟨ x≤c ⟩ nothing = {!singleton !}
--   ... | Node c c-isComposite ⟨ x≤c ⟩ (just heap₂) with m≤n⇒m<n∨m≡n x≤c
--   ...   | inj₁ x<c = {!!}
--   ...   | inj₂ refl = {!!}
--   loop : ∀ {j} x → 1 < x → Heap ⟨ x ⟩ → Sieve Primality x j
--   loop x 1<x heap₁ with min-view heap₁
--   ... | Node c c-isComposite ⟨ x≤c ⟩ _ with m≤n⇒m<n∨m≡n x≤c
--   ...   | inj₁ x<c = Prime (unsafe-assert-prime x 1<x) ∷ λ where .force → loop (1 + x) (≤-step 1<x) {!insert ? ? ? heap₂!}
--   ...   | inj₂ refl = Composite c-isComposite ∷ λ where .force → loop (1 + x) (≤-step 1<x) (adjust x heap₁)

-- record Tree {a} (f : ℕ → Set a) (n : ℕ) (i : Size) : Set a where
--   inductive
--   constructor Node
--   field
--     value : f n
--     left  : Thunk (Tree f (2 * n)) i
--     right : Thunk (Tree f (1 + 2 * n)) i

-- module _ {a} {f : ℕ → Set a} where

--   naturals : ∀ {m} {i} → (∀ n → m ≤ n → f n) → Tree f m i
--   naturals {m} gen = loop m ≤-refl
--     where
--     loop : ∀ {j} x → m ≤ x → Tree f x j
--     loop x m≤x =
--       Node (gen x m≤x)
--       (λ where .force → loop (2 * x) {!!})
--       (λ where .force → loop (1 + 2 * x) {!!})

--   open import Data.Fin using (0F; 1F)
--   open import Data.Nat.DivMod using (_divMod_; result)
