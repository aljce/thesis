open import Level using (_⊔_)

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; Dec)
open Dec
open import Relation.Nullary.Decidable using (from-yes; from-no)
open import Relation.Unary using (Decidable)
open import Relation.Binary using (Tri)
open Tri
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; resp₂)

open import Data.Sum using (_⊎_)
open _⊎_

open import Data.Nat using (ℕ; _+_; _∸_; _*_; _≤_; _<_; _<?_; _>_)
open ℕ
open _≤_
open import Data.Nat.Properties using (<-irrefl; <-trans; ≤-refl; ≤-step; <-cmp; n≮n; m≤m*n; 0<1+n; m≤n+m; n∸m≤n; ≤-stepsʳ)
open import Data.Nat.Properties using (+-suc; *-comm; m∸n+n≡m)
open import Data.Nat.Divisibility using (_∣_; divides; _∣?_; _∤_; ∣-trans)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Nat.Properties using (≤-isPreorder; <⇒≤; <-transˡ; <-transʳ)
open import Relation.Binary.Reasoning.Base.Triple ≤-isPreorder <-trans (resp₂ _<_) <⇒≤ <-transˡ <-transʳ

module Primality where

postulate
  TODO : ∀ {a} {A : Set a} → A
  -- .irrelevance : ∀ {a} {A : Set a} -> .A -> A
  -- ≡-recomp : ∀ {a} {A : Set a} {x y : A} → .(x ≡ y) → x ≡ y

-- open import Relation.Binary.PropositionalEquality.WithK using (≡-erase)

-- ≡-recomputable : ∀ {a} {A : Set a} {x y : A} → .(x ≡ y) → x ≡ y
-- ≡-recomputable x≡y = ≡-erase (≡-recomp x≡y)

-- auto : ∀ {a} {A : Set a} {{it : A}} → A
-- auto {{it}} = it

1<2 : 1 < 2
1<2 = from-yes (1 <? 2)

a∣n∧a>n⇒n≡0 : ∀ {a n} → a ∣ n → a > n → 0 ≡ n
a∣n∧a>n⇒n≡0 (divides zero n≡q*a) a>n = sym n≡q*a
a∣n∧a>n⇒n≡0 {a} {n} (divides (suc q) n≡q*a) a>n = ⊥-elim (n≮n a a<a)
  where
  a<a : a < a
  a<a = begin-strict
    a ≤⟨ m≤m*n a 0<1+n ⟩
    a * suc q ≡⟨ *-comm a (suc q) ⟩
    suc q * a ≡⟨ sym (n≡q*a) ⟩
    n <⟨ a>n ⟩ a ∎

record IsPrime (p : ℕ) : Set where
  constructor IsPrime✓
  field
    1<p : 1 < p
    ∀i∣p[i≡p] : ∀ {i} → 1 < i → i ∣ p → i ≡ p

record IsComposite (c : ℕ) : Set where
  constructor IsComposite✓
  field
    p : ℕ
    p<c : p < c
    P[c] : IsPrime p
    p∣c : p ∣ c

open import Data.Nat.Properties using ()

2-isPrime : IsPrime 2
2-isPrime = IsPrime✓ (from-yes (1 <? 2)) 2-primality
  where
  2-primality : ∀ {i} → 1 < i → i ∣ 2 → i ≡ 2
  2-primality {1} (s≤s ()) _
  2-primality {2} _ _ = refl
  2-primality {suc (suc (suc i))} 1<i i∣2
    = ⊥-elim (<-irrefl (a∣n∧a>n⇒n≡0 i∣2 (≤-stepsʳ i ≤-refl)) (from-yes (0 <? 2)))

3-isPrime : IsPrime 3
3-isPrime = IsPrime✓ (from-yes (1 <? 3)) 3-primality
  where
  3-primality : ∀ {i} → 1 < i → i ∣ 3 → i ≡ 3
  3-primality {1} (s≤s ()) _
  3-primality {2} _ 2∣3 = ⊥-elim (from-no (2 ∣? 3) 2∣3)
  3-primality {3} _ _ = refl
  3-primality {suc (suc (suc (suc i)))} 1<i i∣3
    = ⊥-elim (<-irrefl (a∣n∧a>n⇒n≡0 i∣3 (≤-stepsʳ i ≤-refl)) (from-yes (0 <? 3)))

4-isComposite : IsComposite 4
4-isComposite = IsComposite✓ 2 (from-yes (2 <? 4)) 2-isPrime (from-yes (2 ∣? 4))

data Primality (n : ℕ) : Set where
  Prime : IsPrime n → Primality n
  Composite : IsComposite n → Primality n

exclusive : ∀ {n} → IsPrime n → IsComposite n → ⊥
exclusive (IsPrime✓ _ ∀i∣n[i≡n]) (IsComposite✓ p p<n (IsPrime✓ 1<p _) p∣n)
  = <-irrefl (∀i∣n[i≡n] 1<p p∣n) p<n
  -- p is a prime divisor of n so p must be n but p < n ⇒⇐

¬prime<2 : ∀ p → p < 2 → ¬ (IsPrime p)
¬prime<2 _ (s≤s (s≤s ())) (IsPrime✓ (s≤s (s≤s _)) _)

module Accessibility where

  data Upward (bot : ℕ) (top : ℕ) : Set where
    acc : (∀ {mid} → bot < mid → mid ≤ top → Upward mid top) → Upward bot top

  ∸-mono-< : ∀ {m n o} → m < n → n ≤ o → o ∸ n < o ∸ m
  ∸-mono-< {zero}  {suc n} {suc o} (s≤s m<n) (s≤s n<o) = s≤s (n∸m≤n n o)
  ∸-mono-< {suc _} {suc _} {suc _} (s≤s m<n) (s≤s n<o) = ∸-mono-< m<n n<o

  <-upward : ∀ {bot top : ℕ} → Upward bot top
  <-upward {bot} {top} = loop bot (<-wellFounded (top ∸ bot))
    where
    loop : ∀ x → Acc _<_ (top ∸ x) → Upward x top
    loop x (acc downward) = acc λ {mid} x<mid mid≤top →
      loop mid (downward (top ∸ mid) (∸-mono-< x<mid mid≤top))

open Accessibility

open import Data.Nat using (_≟_)
open import Data.Nat.Properties using (<-≤-connex; m<m*n; *-monoʳ-<)
open _∣_ using (equality)

_² : ℕ → ℕ
x ² = x * x

n≡a*b⇒a²≤n : ∀ {n a b} → n ≡ a * b → 0 < a → a < b → a ² < n
n≡a*b⇒a²≤n {n} {suc a} {b} n≡[1+a]*b (s≤s _) a<b = begin-strict
  suc a * suc a <⟨ *-monoʳ-< a a<b ⟩
  suc a * b ≡⟨ sym n≡[1+a]*b ⟩ n ∎

compositionality
  : ∀ n → 2 ² < n
  → (∀ m → 1 < m → m < n → Primality m)
  → IsComposite n ⊎ (∀ p → p < n → IsPrime p → p ∤ n)
compositionality n 2²<n primality<n = loop 2 1<2 2²<n <-upward ¬p<2[p∤n]
  where
  ¬p<2[p∤n] : ∀ p → p < 2 → IsPrime p → p ∤ n
  ¬p<2[p∤n] p p<2 p-isPrime _ = ⊥-elim (¬prime<2 p p<2 p-isPrime)

  x²<n⇒x<n : ∀ {x} → 1 < x → x ² < n → x < n
  x²<n⇒x<n {x} 1<x x²<n = begin-strict
    x <⟨ m<m*n (<-trans 0<1+n 1<x) 1<x ⟩
    x * x <⟨ x²<n ⟩ n ∎

  no-factors>sqrt[n]
    : ∀ x → 1 < x → x ² < n → n ≤ (1 + x) ²
    → (∀ p → p < x → IsPrime p → p ∤ n)
    → (∀ p → p < n → IsPrime p → p ∤ n)
  no-factors>sqrt[n] x 1<x x*x<n n≤[1+x]² ∀p<x[p∤n] p p<n p-isPrime p∣n@(divides _ eq) with <-cmp p x
  ... | tri< p<x _ _ = ∀p<x[p∤n] p p<x p-isPrime p∣n
  ... | tri≈ _ _ _ = TODO
  ... | tri> _ _ p>x = TODO

  loop
    : ∀ x → 1 < x → x ² < n → Upward x n
    → (∀ p → p < x → IsPrime p → p ∤ n)
    → IsComposite n ⊎ (∀ p → p < n → IsPrime p → p ∤ n)
  loop x 1<x x*x<n (acc upward) ∀p<x[p∤n] with <-≤-connex ((1 + x) ²) n | x²<n⇒x<n 1<x x*x<n
  ... | inj₂ [1+x]²≥n | _ = inj₂ TODO
  ... | inj₁ [1+x]²<n | x<n with primality<n x 1<x x<n
  ...   | Composite x-isComposite = loop (1 + x) (≤-step 1<x) [1+x]²<n (upward ≤-refl x<n) TODO
  ...   | Prime x-isPrime with x ∣? n
  ...     | yes x∣n = inj₁ (IsComposite✓ x x<n x-isPrime x∣n)
  ...     | no ¬x∣n = loop (1 + x) (≤-step 1<x) [1+x]²<n (upward ≤-refl x<n) TODO

-- compositionality n 1<n primality<n = loop 2 1<2 1<n (<-upwards 2 (1 + n)) ¬p<2∣n
  -- where
  -- ¬p<2∣n : ∀ p → p < 2 → IsPrime p → p ∤ n
  -- ¬p<2∣n p p<2 p-isPrime = ⊥-elim (¬prime<2 p p<2 p-isPrime)

  -- loop
  --   : ∀ x → 1 < x → x ≤ n → Upward _<_ x (1 + n)
  --   → (∀ p → p < x → IsPrime p → p ∤ n)
  --   → IsComposite n ⊎ (∀ p → p < n → IsPrime p → p ∤ n)
  -- loop x 1<x x≤n (upward next) ∀p<x[p∤n] with m≤n⇒m<n∨m≡n x≤n
  -- ... | inj₂ x≡n rewrite x≡n = inj₂ ∀p<x[p∤n]
  -- ... | inj₁ x<n with primality<n x 1<x x<n
  -- ...   | Composite x-isComposite = loop (1 + x) (≤-step 1<x) x<n (next ≤-refl (s≤s x<n)) {!!}
  -- ...   | Prime x-isPrime with x ∣? n
  -- ...     | yes x∣n = inj₁ (IsComposite✓ x x<n x-isPrime x∣n)
  -- ...     | no ¬x∣n = loop (1 + x) (≤-step 1<x) x<n (next ≤-refl (s≤s x<n)) {!!}


primality≤4 : ∀ n → 1 < n → n ≤ 4 → Primality n
primality≤4 1 (s≤s ()) _
primality≤4 2 _ _ = Prime 2-isPrime
primality≤4 3 _ _ = Prime 3-isPrime
primality≤4 4 _ _ = Composite 4-isComposite
primality≤4 (suc (suc (suc (suc (suc _))))) 1<n (s≤s (s≤s (s≤s (s≤s ()))))

primality : ∀ n → 1 < n  → (∀ m → 1 < m → m < n → Primality m) → Primality n
primality n 1<n primality<n with <-≤-connex (2 ²) n
... | inj₂ 2²≥n = primality≤4 n 1<n 2²≥n
... | inj₁ 2²<n with compositionality n 2²<n primality<n
...   | inj₁ n-isComposite = Composite n-isComposite
      -- n is a composite so just return the proof of compositionality
...   | inj₂ ∀p<n[p∤n] = Prime (IsPrime✓ 1<n ∀i∣n[i≡n])
      -- All prime divisors less then n do not divide n therefore n is prime (#1)
      where
      ∀i∣n[i≡n] : ∀ {i} → 1 < i → i ∣ n → i ≡ n
      ∀i∣n[i≡n] {i} 1<i i∣n with <-cmp i n
      ... | tri> _ _ i>n = ⊥-elim (<-irrefl (a∣n∧a>n⇒n≡0 i∣n i>n) (<-trans 0<1+n 1<n))
          -- i is larger than n so n must be zero but n is greater than 1 ⇒⇐
      ... | tri≈ _ i≡n _ = i≡n
      ... | tri< i<n _ _ with primality<n i 1<i i<n
      ...   | Prime i-isPrime
            = ⊥-elim (∀p<n[p∤n] i i<n i-isPrime i∣n)
            -- i is a prime divisor of n (#1) ⇒⇐
      ...   | Composite (IsComposite✓ p p<i p-isPrime p∣i)
            = ⊥-elim (∀p<n[p∤n] p (<-trans p<i i<n) p-isPrime (∣-trans p∣i i∣n))
            -- i is a composite number with a prime divisor therefore there exists a prime divisor of n (#1) ⇒⇐

-- prime? : Decidable IsPrime
-- prime? n with 1 <? n
-- ... | no ¬1<n = no λ { (IsPrime✓ 1<n _) → ¬1<n 1<n }
-- ... | yes 1<n with primality n 1<n
-- ... | Prime isPrime = yes isPrime
-- ... | Composite isComposite = no λ { isPrime → exclusive isPrime isComposite }

-- composite? : Decidable IsComposite
-- composite? n with 1 <? n
-- ... | no ¬1<n = no λ { (IsComposite✓ p p<n (IsPrime✓ 1<p _) _) → ¬1<n (<-trans 1<p p<n) }
-- ... | yes 1<n with primality n 1<n
-- ... | Prime isPrime = no λ { isComposite → exclusive isPrime isComposite }
-- ... | Composite isComposite = yes isComposite

open import Size using (Size; ∞; Size<_; ↑_)
open import Codata.Conat using (Conat; suc)
open import Codata.Thunk using (Thunk; force)
open import Data.Nat.Properties using (m≤n⇒m<n∨m≡n)

-- record Sieve {a} (f : ℕ → Set a) (n : ℕ) (i : Size) : Set a where
--   inductive
--   constructor _∷_
--   field
--     head : f n
--     tail : Thunk (Sieve f (suc n)) i
-- open Sieve

-- module _ {a} {f : ℕ → Set a} where

--   index : ∀ {n m} → m ≤ n → Sieve f m ∞ → f n
--   index m≤n s = loop m≤n <-upward s
--     where
--     loop : ∀ {n m} → m ≤ n → Upward m n → Sieve f m ∞ → f n
--     loop m≤n (acc upward) (head ∷ tail) with m≤n⇒m<n∨m≡n m≤n
--     ... | inj₁ m<n = loop m<n (upward ≤-refl m<n) (force tail)
--     ... | inj₂ m≡n rewrite m≡n = head

record Sieve {a} (f : ℕ → Set a) (n : ℕ) (i : Size) : Set a where
  inductive
  constructor _∷_
  field
    head : f n
    tail : Thunk (Sieve f (suc n)) i
open Sieve

data _⊢_≤_ (i : Size) : ℕ → ℕ → Set where
  ≤-same : ∀ {n} → i ⊢ n ≤ n
  ≤-next : ∀ {m n} {j : Size< i} → j ⊢ suc m ≤ n → i ⊢ m ≤ n

_⊢_<_ : Size → ℕ → ℕ → Set
i ⊢ m < n = i ⊢ suc m ≤ n

module _ {a} {f : ℕ → Set a} where

  index : ∀ {m n} {i} → Sieve f m i → i ⊢ m ≤ n → f n
  index xs ≤-same = head xs
  index xs (≤-next i) = index (force (tail xs)) i

  tabulate : ∀ {m} {i} → (∀ n → i ⊢ m ≤ n → f n) → Sieve f m i
  tabulate {m} gen = gen m ≤-same ∷ λ where .force → tabulate λ n m<n → gen n (≤-next m<n)

module _ {a b} {f : ℕ → Set a} {g : ℕ → Set b} where

  map : ∀ {m} {i} → (∀ n → f n → g n) → Sieve f m i → Sieve g m i
  map {m = m} eta (f ∷ fs) = eta m f ∷ λ where .force → map eta (force fs)

-- record Iterator (x : ℕ) : Set where
--   constructor Iterator✓
--   field
--     p : ℕ
--     p-isPrime : IsPrime p
--     p∣x : p ∣ x

open import Data.Nat.Divisibility using (∣-refl)
open import Data.Nat.Properties using (≤-isTotalOrder; _≤?_)
open import Heap.Indexed _≤_ ≤-isTotalOrder IsComposite
open import Data.Maybe using (Maybe)
open Maybe

unsafe-assert-prime : ∀ n → 1 < n → IsPrime n
unsafe-assert-prime n 1<n = IsPrime✓ 1<n n-primality
  where
  postulate
    evil : ⊥
  n-primality : ∀ {i} → 1 < i → i ∣ n → i ≡ n
  n-primality {i} _ i∣n with <-cmp i n
  ... | tri< _ _ _ = ⊥-elim evil -- !UNSOUND!
  ... | tri≈ _ i≡n _ = i≡n
  ... | tri> _ _ i>n = ⊥-elim (<-irrefl (a∣n∧a>n⇒n≡0 i∣n i>n) (<-trans 0<1+n 1<n))

sieve : ∀ {i} → Sieve Primality 2 i
sieve = Prime 2-isPrime ∷ λ where .force → loop 3 (from-yes (1 <? 3)) (singleton 4 ⟨ from-yes (3 ≤? 4) ⟩ 4-isComposite)
  where
  open IsComposite
  next : ∀ {n} → (c : IsComposite n) → IsComposite (p c + n)
  next (IsComposite✓ p p<n p-isPrime p∣n) = IsComposite✓ p {!!} p-isPrime {!!}
  adjust : ∀ x → Heap ⟨ x ⟩ → Heap ⟨ 1 + x ⟩
  adjust x heap₁ with min-view heap₁
  ... | Node c (IsComposite✓ p p<c p-isPrime p∣c) ⟨ x≤c ⟩ nothing = {!singleton !}
  ... | Node c c-isComposite ⟨ x≤c ⟩ (just heap₂) with m≤n⇒m<n∨m≡n x≤c
  ...   | inj₁ x<c = {!!}
  ...   | inj₂ refl = {!!}
  loop : ∀ {j} x → 1 < x → Heap ⟨ x ⟩ → Sieve Primality x j
  loop x 1<x heap₁ with min-view heap₁
  ... | Node c c-isComposite ⟨ x≤c ⟩ _ with m≤n⇒m<n∨m≡n x≤c
  ...   | inj₁ x<c = Prime (unsafe-assert-prime x 1<x) ∷ λ where .force → loop (1 + x) (≤-step 1<x) {!insert ? ? ? heap₂!}
  ...   | inj₂ refl = Composite c-isComposite ∷ λ where .force → loop (1 + x) (≤-step 1<x) (adjust x heap₁)
-- fib : ℕ → ℕ
-- fib 0 = 0
-- fib 1 = 1
-- fib (suc (suc n)) = fib n + fib (suc n)


-- data Fib (n : ℕ) : Set where
--   𝔽 : ∀ f → f ≡ fib n → Fib n

-- _𝔽+_ : ∀ {n} → Fib n → Fib (1 + n) → Fib (2 + n)
-- 𝔽 f₁ f₁≡fib[n] 𝔽+ 𝔽 f₂ f₂≡fib[1+n] = 𝔽 (f₁ + f₂) TODO

-- fib-sieve : Sieve Fib 0 ∞
-- fib-sieve = loop
--   where
--   loop : ∀ {i} → Sieve Fib 0 i
--   loop = tabulate
--     λ { .0 ≤-same → 𝔽 0 refl
--       ; .1 (≤-next ≤-same) → 𝔽 1 refl
--       ;  n (≤-next (≤-next m≤n)) → {!!} -- index loop m≤n 𝔽+ index loop (≤-next m≤n)
--       }

-- ⊢≤-trans : ∀ {i} {m n o} → i ⊢ m ≤ n → i ⊢ n ≤ o → i ⊢ m ≤ o
-- ⊢≤-trans i⊢m≤n i⊢m≤o = {!!}

-- idea : ∀ {n m x} {i} → m ≤ x → x ≤ n → i ⊢ m ≤ n → i ⊢ m ≤ x
-- idea z≤n z≤n i⊢m≤n = ≤-same
-- idea z≤n (s≤s x≤n) (≤-next x) = {!!}
-- idea (s≤s m<x) x<n i⊢m≤n = {!!}

-- test : index fib (≤-next (≤-next (≤-next (≤-next (≤-next (≤-next ≤-same)))))) ≡ 8
-- test = refl

  -- memo : ∀ {b} {B : Set b} {m} {i} → (Sieve f m i → B) → Sieve f m i → B
  -- memo = {!!}

-- fib : ∀ {i} → Sieve Fib 0 i
-- fib = tabulate λ n m≤n → {!!}

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

--   index-tree : ∀ {n m} → m ≤ n → Tree f m ∞ → f n
--   index-tree m≤n t = TODO
--     where
--     loop : ∀ {m} {n} → m ≤ n → Upward m n → Tree f m ∞ → f n
--     loop {m} {n} m≤n u (Node value left right) with (n - 1) divMod 2
--     ... | result q 0F h≡q*2 rewrite h≡q*2 = loop q {!!} {!!}
--     ... | result q 1F h≡1+q*2 = {!!}

-- data Bin : ℕ → Set where
--   Zero : Bin 0
--   Even : ∀ {n m} → m ≡ 2 * n     → Bin n → Bin m
--   Odd  : ∀ {n m} → m ≡ 1 + 2 * n → Bin n → Bin m

-- binary : ∀ n → Bin n
-- binary zero = Zero
-- binary (suc m) with binary m
-- ... | Zero = Odd refl Zero
-- ... | Even m≡2*n  bin-n rewrite m≡2*n = Odd refl bin-n
-- ... | Odd {n} m≡1+2*n bin-n = Even {!refl!} bin-n

-- sieve : ∀ {i} → Sieve Primality 2 i
-- sieve = Prime 2-isPrime ∷ λ where .force → Prime 3-isPrime ∷ λ where .force → Composite 4-isComposite ∷ λ where .force → loop 5 (from-yes (2 ² <? 5))
--   where
--   loop : ∀ {j} n → 2 ² < n → Sieve Primality n j
--   loop n 2²<n = primality n TODO (λ m 1<m m<n → index {!!} sieve) ∷ λ where .force → loop (suc n) (≤-step 2²<n)

-- 13-isPrime : IsPrime 13
-- 13-isPrime = from-yes (prime? 13)

-- 24-isComposite : IsComposite 24
-- 24-isComposite = from-yes (composite? 24)
