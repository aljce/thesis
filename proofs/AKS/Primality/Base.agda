open import Relation.Binary using (Tri)
open Tri
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)

open import Data.Empty using (⊥-elim)

module AKS.Primality.Base where

open import AKS.Nat using (ℕ; _≟_; _<_; _≤_; <-cmp; <-irrefl; <-trans; 0<1+n; ≤-antisym; 0≤n; suc-injective-≤; <⇒≤; ≢⇒¬≟; <⇒≱)
open import AKS.Nat.GCD using (_∣_; gcd; _⊥_; bézout; lemma; Identity; gcd[a,b]∣a; gcd[a,b]∣b; 0∣n⇒n≈0; ∣-respˡ; ∣⇒≤)

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
    p-isPrime : IsPrime p
    p∣c : p ∣ c

record Prime : Set where
  constructor Prime✓
  field
    prime : ℕ
    isPrime : IsPrime prime

prime≢0 : ∀ {p} → IsPrime p → p ≢ 0
prime≢0 (IsPrime✓ 1<p _) p≡0 = <-irrefl (sym p≡0) (<-trans 0<1+n 1<p)

n<1⇒n≡0 : ∀ {n} → n < 1 → n ≡ 0
n<1⇒n≡0 {n} n<1 = ≤-antisym (suc-injective-≤ n<1) 0≤n

n⊥prime : ∀ {p} n {n≢0 : n ≢ 0} → n < p → IsPrime p → n ⊥ p
n⊥prime {p} n {n≢0} n<p (IsPrime✓ 1<p ∀i∣p[i≡p]) with <-cmp 1 (gcd n p)
... | tri> _ _ 1>gcd[n,p] = ⊥-elim (n≢0 (0∣n⇒n≈0 (∣-respˡ (n<1⇒n≡0 1>gcd[n,p]) (gcd[a,b]∣a n p))))
... | tri≈ _ 1≡gcd[n,p] _ = sym 1≡gcd[n,p]
... | tri< 1<gcd[n,p] _ _ = ⊥-elim (<⇒≱ n<p p≤n)
  where
  gcd[n,p]≡p : gcd n p ≡ p
  gcd[n,p]≡p = ∀i∣p[i≡p] 1<gcd[n,p] (gcd[a,b]∣b n p)
  p∣n : p ∣ n
  p∣n = ∣-respˡ gcd[n,p]≡p (gcd[a,b]∣a n p)
  p≤n : p ≤ n
  p≤n = ∣⇒≤ {n≢0 = ≢⇒¬≟ n≢0} p∣n

bézout-prime : ∀ x p → x ≢ 0 → x < p → IsPrime p → Identity 1 x p
bézout-prime x p x≢0 x<p p-isPrime with bézout x p | n⊥prime x {x≢0} x<p p-isPrime
bézout-prime x p x≢0 x<p p-isPrime | lemma d gcd[x,p]≡d ident | gcd[x,p]≡1 with trans (sym gcd[x,p]≡d) gcd[x,p]≡1
bézout-prime x p x≢0 x<p p-isPrime | lemma .1 gcd[x,p]≡d ident | gcd[x,p]≡1 | refl = ident

