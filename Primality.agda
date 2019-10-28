{-# OPTIONS --safe --without-K #-}
open import Level using (_⊔_)

open import Data.Empty using (⊥)
open import Data.Empty.Irrelevant using (⊥-elim)
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
open import Data.Nat.Properties using (<-irrefl; <-trans; <-cmp; n≮n; 0<1+n; m≤n+m; n∸m≤n)
open import Data.Nat.Properties using (≤-antisym; ≤-trans; n≤1+n; ≤-pred; m≤n⇒m<n∨m≡n; ≤-refl; ≤-step; m≤m*n)
open import Data.Nat.Properties using (*-comm)
open import Data.Nat.Divisibility using (_∣_; divides; _∣?_; _∤_; ∣-trans)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Nat.Properties using (≤-isPreorder; <⇒≤; <-transˡ; <-transʳ)
open import Relation.Binary.Reasoning.Base.Triple ≤-isPreorder <-trans (resp₂ _<_) <⇒≤ <-transˡ <-transʳ

module Primality where

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

record Irrelevant {a} (A : Set a) : Set a where
  constructor irr
  field
    .proof : A

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

data Compositionality (n : ℕ) : Set where
  Composite : IsComposite n → Compositionality n
  Prime : Irrelevant (∀ p → p < n → IsPrime p → p ∤ n) → Compositionality n

compositionality
  : ∀ n → 1 < n
  → (∀ m → 1 < m → m < n → Primality m)
  → Compositionality n
compositionality n 1<n primality<n = loop 2 1<2 1<n <-upward (irr ¬p<2[p∤n])
  where
  ¬p<2[p∤n] : ∀ p → p < 2 → IsPrime p → p ∤ n
  ¬p<2[p∤n] p p<2 p-isPrime _ = ⊥-elim (¬prime<2 p p<2 p-isPrime)

  cons : ∀ {x}
    → (IsPrime x → x ∤ n)
    → Irrelevant (∀ p → p < x → IsPrime p → p ∤ n)
    → Irrelevant (∀ p → p < 1 + x → IsPrime p → p ∤ n)
  cons {x} x-isPrime⇒x∤n (irr ∀p<x[p∤n]) = irr λ p p<1+x p-isPrime p∣n →
    case <-cmp p x of
    λ { (tri< p<x _ _) → ∀p<x[p∤n] p p<x p-isPrime p∣n
      ; (tri≈ _ refl _) → x-isPrime⇒x∤n p-isPrime p∣n
      ; (tri> _ ¬p≡x p>x) → ¬p≡x (≤-antisym (≤-pred p<1+x) (≤-trans (n≤1+n x) p>x))
      }

  loop
    : ∀ x → 1 < x → x ≤ n → Upward x n
    → Irrelevant (∀ p → p < x → IsPrime p → p ∤ n)
    → Compositionality n
  loop x 1<x x≤n (acc upward) ∀p<x[p∤n] with m≤n⇒m<n∨m≡n x≤n
  ... | inj₂ x≡n rewrite x≡n = Prime ∀p<x[p∤n]
  ... | inj₁ x<n with primality<n x 1<x x<n
  ...   | Composite x-isComposite = loop (1 + x) (≤-step 1<x) x<n (upward ≤-refl x<n) ∀p<1+x[p∤n]
        where ∀p<1+x[p∤n] = cons (λ x-isPrime _ → exclusive x-isPrime x-isComposite) ∀p<x[p∤n]
  ...   | Prime x-isPrime with x ∣? n
  ...     | yes x∣n = Composite (IsComposite✓ x x<n x-isPrime x∣n)
  ...     | no ¬x∣n = loop (1 + x) (≤-step 1<x) x<n (upward ≤-refl x<n) ∀p<1+x[p∤n]
          where ∀p<1+x[p∤n] = cons (λ _ x∣n → ¬x∣n x∣n) ∀p<x[p∤n]

primalityⁱ : ∀ n → 1 < n → (∀ m → 1 < m → m < n → Primality m) → Primality n
primalityⁱ n 1<n primality<n with compositionality n 1<n primality<n
... | Composite n-isComposite = Composite n-isComposite
    -- n is a composite so just return the proof of compositionality
... | Prime (irr ∀p<n[p∤n]) = Prime (IsPrime✓ 1<n ∀i∣n[i≡n])
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

primality : ∀ n → 1 < n → Primality n
primality n 1<n = loop n 1<n (<-wellFounded n)
  where
  loop : ∀ x → 1 < x → Acc _<_ x → Primality x
  loop x 1<x (acc downward) = primalityⁱ x 1<x λ m 1<m m<x → loop m 1<m (downward m m<x)

open import Function using (_$_)
open import Data.Nat.Properties using (*-identityʳ; m<m*n; *-cancelʳ-<; +-identityʳ)
open import Data.List using (List)
open List

data Factorization : ℕ → Set where
  Unit : Factorization 1
  Factor : ∀ {p ps n} → IsPrime p → Factorization ps → n ≡ p * ps → Factorization n

prime-factorization : ∀ n → 0 < n → Factorization n
prime-factorization (suc zero) 0<n = Unit
prime-factorization (suc (suc n)) 0<n = loop (suc (suc n)) (s≤s (s≤s z≤n)) (<-wellFounded (suc (suc n)))
  where
  loop : ∀ x → 1 < x → Acc _<_ x → Factorization x
  loop x 1<x (acc downward) with primality x 1<x
  ... | Prime x-isPrime = Factor x-isPrime Unit (sym (*-identityʳ x))
  ... | Composite (IsComposite✓ p p<x p-isPrime@(IsPrime✓ 1<p _) (divides q x≡q*p)) rewrite x≡q*p
      = Factor p-isPrime (loop q 1<q (downward q q<q*p)) (*-comm q p)
      where
      1<q : 1 < q
      1<q = *-cancelʳ-< {p} 1 q $ begin-strict
        1 * p ≡⟨ +-identityʳ p ⟩
        p     <⟨ p<x ⟩ q * p ∎
      q<q*p : q < q * p
      q<q*p = m<m*n (<-trans 0<1+n 1<q) 1<p

-- fundamental theorem of arithmetic
-- FTA : ∀ {n} (decomp₁ decomp₂ : Factorization n) → decomp₁ ≡ decomp₂
-- FTA = {!!}

factors : ∀ {n} → Factorization n → List ℕ
factors Unit = []
factors (Factor {p} _ fs _) = p ∷ factors fs

210-factors : factors (prime-factorization 210 (from-yes (0 <? 210))) ≡ 2 ∷ 3 ∷ 5 ∷ 7 ∷ []
210-factors = refl

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

13-isPrime : IsPrime 13
13-isPrime = from-yes (prime? 13)

24-isComposite : IsComposite 24
24-isComposite = from-yes (composite? 24)

-- 7919-isPrime : IsPrime 7919
-- 7919-isPrime = from-yes (prime? 7919)

¬prime⇒composite : ∀ n → 1 < n → ¬ (IsPrime n) → IsComposite n
¬prime⇒composite n 1<n ¬n-isPrime with primality n 1<n
... | Prime n-isPrime = ⊥-elim (¬n-isPrime n-isPrime)
... | Composite n-isComposite = n-isComposite

open import Data.Nat using (_≤′_)
open  _≤′_
open import Data.Nat.Properties using (m≤m+n; *-monoʳ-≤; ≤-<-connex; +-comm; ≤⇒≤′)
open import Data.Nat.Divisibility using (∣1⇒≡1; ∣m+n∣m⇒∣n; 1∣_; ∣-refl; m∣m*n; ∣n⇒∣m*n)

_! : ℕ → ℕ
zero ! = 1
suc n ! = suc n * n !

1≤n! : ∀ n → 1 ≤ n !
1≤n! zero = ≤-refl
1≤n! (suc n) = begin
  1 ≤⟨ 1≤n! n ⟩
  n ! ≤⟨ m≤m+n (n !) (n * n !) ⟩
  n ! + n * n ! ≡⟨ refl ⟩
  (1 + n) ! ∎

n≤n! : ∀ n → n ≤ n !
n≤n! zero = z≤n
n≤n! (suc n) = begin
  suc n ≡⟨ sym (*-identityʳ (suc n)) ⟩
  suc n * 1 ≤⟨ *-monoʳ-≤ (suc n) (1≤n! n) ⟩
  (1 + n) ! ∎

∀m≤n∣n! : ∀ {n m} → 0 < m → m ≤ n → m ∣ n !
∀m≤n∣n! (s≤s 0<m) m≤n = loop (≤⇒≤′ m≤n)
  where
  loop : ∀ {n m} → suc m ≤′ n → suc m ∣ n !
  loop {suc n} ≤′-refl = m∣m*n (n !)
  loop {n} (≤′-step m<n) = ∣n⇒∣m*n n (loop m<n)

¬∣1+n! : ∀ {p₁ p₂} → 1 < p₂ → p₂ ≤ p₁ → p₂ ∤ 1 + p₁ !
¬∣1+n! {p₁} {p₂} 1<p₂ p₂≤p₁ p₂∣1+p₁! = <-irrefl (sym p₂≡1) 1<p₂
  where
  0<p₂ : 0 < p₂
  0<p₂ = <-trans 0<1+n 1<p₂
  p₂≡1 : p₂ ≡ 1
  p₂≡1 rewrite +-comm 1 (p₁ !) = ∣1⇒≡1 (∣m+n∣m⇒∣n p₂∣1+p₁! (∀m≤n∣n! 0<p₂ p₂≤p₁))

record LargerPrime (n : ℕ) : Set where
  constructor Larger
  field
    p : ℕ
    P[n] : IsPrime p
    n<p : n < p

euclid : ∀ p → LargerPrime p
euclid p₁ with primality (1 + p₁ !) (s≤s (1≤n! p₁))
... | Prime P[1+p!] = Larger (1 + p₁ !) P[1+p!] (s≤s (n≤n! p₁))
... | Composite (IsComposite✓ p₂ p₂<1+p₁! P[p₂]@(IsPrime✓ 1<p₂ _) p₂∣1+p₁!) with ≤-<-connex p₂ p₁
...   | inj₂ p₂>p₁ = Larger p₂ P[p₂] p₂>p₁
...   | inj₁ p₂≤p₁ = ⊥-elim (¬∣1+n! 1<p₂ p₂≤p₁ p₂∣1+p₁!)
