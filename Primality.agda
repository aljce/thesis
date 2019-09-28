open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; Dec)
open Dec
open import Relation.Nullary.Decidable using (from-yes)
open import Relation.Unary using (Decidable)
open import Relation.Binary using (Tri)
open Tri
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; resp₂)

open import Data.Sum using (_⊎_)
open _⊎_

open import Data.Nat using (ℕ; _+_; _∸_; _*_; _≤_; _<_; _<?_; _>_)
open ℕ
open _≤_
open import Data.Nat.Properties using (<-irrefl; <-trans; ≤-refl; ≤-step; <-cmp; n≮n; m≤m*n; 0<1+n; m≤n+m)
open import Data.Nat.Properties using (+-suc; *-comm; m∸n+n≡m)
open import Data.Nat.Divisibility using (_∣_; divides; _∤_; ∣-trans)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Nat.Properties using (≤-isPreorder; <⇒≤; <-transˡ; <-transʳ)
open import Relation.Binary.Reasoning.Base.Triple ≤-isPreorder <-trans (resp₂ _<_) <⇒≤ <-transˡ <-transʳ

module Primality where

postulate
  TODO : ∀ {a} {A : Set a} → A
  .irrelevance : ∀ {a} {A : Set a} -> .A -> A
  ≡-recomp : ∀ {a} {A : Set a} {x y : A} → .(x ≡ y) → x ≡ y

-- open import Relation.Binary.PropositionalEquality.WithK using (≡-erase)

-- ≡-recomputable : ∀ {a} {A : Set a} {x y : A} → .(x ≡ y) → x ≡ y
-- ≡-recomputable x≡y = ≡-erase (≡-recomp x≡y)

auto : ∀ {a} {A : Set a} {{it : A}} → A
auto {{it}} = it

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

data Primality (n : ℕ) : Set where
  Prime : IsPrime n → Primality n
  Composite : IsComposite n → Primality n

exclusive : ∀ {n} → IsPrime n → IsComposite n → ⊥
exclusive (IsPrime✓ _ ∀i∣n[i≡n]) (IsComposite✓ p p<n (IsPrime✓ 1<p _) p∣n)
  = <-irrefl (∀i∣n[i≡n] 1<p p∣n) p<n
  -- p is a prime divisor of n so p must be n but p < n ⇒⇐

¬prime<2 : ∀ p → p < 2 → ¬ (IsPrime p)
¬prime<2 _ (s≤s (s≤s ())) (IsPrime✓ (s≤s (s≤s _)) _)

-- An induction principle on ℕ that starts at s and counts up to n
upward : ∀ {a} {P : ℕ → Set a} {s n} → s ≤ n → (∀ m → s ≤ m → m < n → P m → P (1 + m)) → P s → P n
upward {P = P} {s} {n} s≤n rec start = loop (n ∸ s) s ≤-refl (m∸n+n≡m s≤n) start
  where
  lemma : ∀ {down up} → down + suc up ≡ n → up < n
  lemma {down} {up} down+[1+up]≡n = begin-strict
    up <⟨ ≤-refl ⟩
    suc up ≤⟨ m≤n+m (suc up) down ⟩
    down + suc up ≡⟨ down+[1+up]≡n ⟩
    n ∎
  -- The down argument satiates the termination checker
  loop : ∀ down up → s ≤ up → down + up ≡ n → P up → P n
  loop zero up s≤up refl p = p
  loop (suc down) up s≤up down+up≡n p rewrite sym (+-suc down up)
    = loop down (suc up) (≤-step s≤up) down+up≡n (rec up s≤up (lemma down+up≡n) p)

module Accessibility where
  open import Level using (_⊔_)
  open import Data.Nat.Properties using (∸-mono; n∸m≤n; ≤-trans)

  data Upwards {a r} {A : Set a} (_<_ : A → A → Set r) (bot : A) (top : A) : Set (a ⊔ r) where
    upwards : (∀ mid → bot < mid → mid < top → Upwards _<_ mid top) → Upwards _<_ bot top

  ∸-mono-< : ∀ {m n o} → m < n → n < o → o ∸ n < o ∸ m
  ∸-mono-< {m} {n} {o} m<n n<o = begin-strict
    o ∸ n <⟨ TODO ⟩ o ∸ m ∎

  <-upwards : ∀ {bot top : ℕ} → bot < top → Upwards _<_ bot top
  <-upwards {bot} {top} bot<top = loop bot (<-wellFounded (top ∸ bot))
    where
    loop : ∀ x → Acc _<_ (top ∸ x) → Upwards _<_ x top
    loop x (acc downward) = upwards λ mid x<mid mid<top →
      loop mid (downward (top ∸ mid) (∸-mono-< x<mid mid<top))

compositionality
  : ∀ n → 1 < n
  → (∀ m → 1 < m → m < n → Primality m)
  → IsComposite n ⊎ (∀ p → p < n → IsPrime p → p ∤ n)
compositionality n 1<n primality = TODO
  where
  -- ¬p<2∣n : ∀ p → p < 2 → IsPrime p → p ∤ n
  -- ¬p<2∣n p p<2 p-isPrime = ⊥-elim (¬prime<2 p p<2 p-isPrime)
  -- loop : ∀ m → 1 < m → m < n → 

  -- test
  --   : ∀ m → 1 < m → m < n
  --   → IsComposite m ⊎ (∀ p → p < m → IsPrime p → p ∤ n)
  --   → IsComposite (1 + m) ⊎ (∀ p → p < 1 + m → IsPrime p → p ∤ n)
  -- test m 1<m m<n (inj₁ n-isComposite) = {!!}
  -- test m 1<m m<n (inj₂ ∀p<m[p∤n]) with primality m 1<m m<n
  -- ... | Prime m-isPrime = {!!}
  -- ... | Composite m-isComposite = {!!}

open import Data.Nat.Properties using (≤-antisym)

data _∈[_∙∙_] {r} (f : ℕ → Set r) : ℕ → ℕ → Set r where
  f∈[n] : ∀ {n} → f n → f ∈[ n ∙∙ n ]
  f∈[n∙∙m-1] : ∀ {n m} → f (suc m) → f ∈[ n ∙∙ m ] → f ∈[ n ∙∙ suc m ]

-- test : Primality ∈[ 2 ∙∙ 4 ]
-- test = f∈[n∙∙m-1] {!!} (f∈[n∙∙m-1] {!!} (f∈[n] {!!}))

module _ {ℓ} {f : ℕ → Set ℓ} where

  index : ∀ {n l r} → l ≤ n → n ≤ r → f ∈[ l ∙∙ r ] → f n
  index = TODO
  -- index l≤n n≤r (f∈[n] f) rewrite ≤-antisym l≤n n≤r = f
  -- index {n} {r = r} l≤n n≤r (f∈[n∙∙m-1] f fs) with <-cmp n r

  -- index zero z≤n (s≤s z≤n) (f∈[n] f) = f
  -- index (suc n) l≤n n<r f = {!!}

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

primality : ∀ n → 1 < n → Primality n
primality n 1<n = loop n 1<n (<-wellFounded n)
  where
  loop : ∀ x → 1 < x → Acc _<_ x → Primality x
  loop x 1<x (acc downward) with compositionality x 1<x λ m 1<m m<x → loop m 1<m (downward m m<x)
  ... | inj₁ x-isComposite = Composite x-isComposite
      -- x is a composite so just return the proof of compositionality
  ... | inj₂ ∀p<x[p∤x] = Prime (IsPrime✓ 1<x ∀i∣x[i≡x])
      -- All prime divisors less then x do not divide x therefore x is prime (#1)
    where
    ∀i∣x[i≡x] : ∀ {i} → 1 < i → i ∣ x → i ≡ x
    ∀i∣x[i≡x] {i} 1<i i∣x with <-cmp i x
    ... | tri> _ _ i>x = ⊥-elim (<-irrefl (a∣n∧a>n⇒n≡0 i∣x i>x) (<-trans 0<1+n 1<x))
        -- i is larger than x so x must be zero but x is greater than 1 ⇒⇐
    ... | tri≈ _ i≡x _ = i≡x
    ... | tri< i<x _ _ with loop i 1<i (downward i i<x)
    ...   | Prime i-isPrime
          = ⊥-elim (∀p<x[p∤x] i i<x i-isPrime i∣x)
          -- i is a prime divisor of x (#1) ⇒⇐
    ...   | Composite (IsComposite✓ p p<i p-isPrime p∣i)
          = ⊥-elim (∀p<x[p∤x] p (<-trans p<i i<x) p-isPrime (∣-trans p∣i i∣x))
          -- i is a composite number with a prime divisor therefore there exists a prime divisor of x (#1) ⇒⇐

prime? : Decidable IsPrime
prime? n with 1 <? n
... | no ¬1<n = no λ { (IsPrime✓ 1<n _) → ¬1<n 1<n }
... | yes 1<n with primality n 1<n
... | Prime isPrime = yes isPrime
... | Composite isComposite = no λ { isPrime → exclusive isPrime isComposite }

composite? : Decidable IsComposite
composite? n with 1 <? n
... | no ¬1<n = no λ { (IsComposite✓ p p<n (IsPrime✓ 1<p _) _) → ¬1<n (<-trans 1<p p<n) }
... | yes 1<n with primality n 1<n
... | Prime isPrime = no λ { isComposite → exclusive isPrime isComposite }
... | Composite isComposite = yes isComposite

-- 13-isPrime : IsPrime 13
-- 13-isPrime = from-yes (prime? 13)

-- 24-isComposite : IsComposite 24
-- 24-isComposite = from-yes (composite? 24)
