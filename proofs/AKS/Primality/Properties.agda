open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (from-yes)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Tri)
open Tri
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)

open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)

module AKS.Primality.Properties where

open import AKS.Nat using (ℕ; _+_; _≟_; _<_; _>_; _<?_; _≤_)
open import AKS.Nat using (<-cmp; <-irrefl; <-trans; 0<1+n; ≤-antisym; 0≤n; suc-injective-≤; <⇒≤; ≢⇒¬≟; <⇒≱; n≤m⇒n<m⊎n≡m; ≤-refl; n<1+n)
open import AKS.Nat using (Acc; acc; <-well-founded; [_,_]; binary-search)
open import AKS.Nat.GCD
  using (_∣_; _∤_; _∣?_; gcd; bézout; lemma; Identity; gcd[a,b]∣a; gcd[a,b]∣b; 0∣n⇒n≈0; ∣-respˡ; ∣⇒≤; ∣-trans)
  renaming (_⊥_ to _coprime_)

open import AKS.Primality.Base

prime≢0 : ∀ {p} → IsPrime p → p ≢ 0
prime≢0 (IsPrime✓ 1<p _) p≡0 = <-irrefl (sym p≡0) (<-trans 0<1+n 1<p)

¬prime<2 : ∀ p → p < 2 → ¬ (IsPrime p)
¬prime<2 p p<2 (IsPrime✓ 1<p ∀i∣p[i≡p]) = contradiction 1<p (<⇒≱ p<2)

exclusive : ∀ {n} → IsPrime n → IsComposite n → ⊥
exclusive {n} (IsPrime✓ 1<n ∀i∣n[i≡n]) (IsComposite✓ p p<n (IsPrime✓ 1<p _) p∣n)
  = contradiction p<n (<-irrefl (∀i∣n[i≡n] 1<p p∣n))

n<1⇒n≡0 : ∀ {n} → n < 1 → n ≡ 0
n<1⇒n≡0 {n} n<1 = ≤-antisym (suc-injective-≤ n<1) 0≤n

n⊥prime : ∀ {p} n {n≢0 : n ≢ 0} → n < p → IsPrime p → n coprime p
n⊥prime {p} n {n≢0} n<p (IsPrime✓ 1<p ∀i∣p[i≡p]) with <-cmp 1 (gcd n p)
... | tri> _ _ 1>gcd[n,p] = contradiction (0∣n⇒n≈0 (∣-respˡ (n<1⇒n≡0 1>gcd[n,p]) (gcd[a,b]∣a n p))) n≢0
... | tri≈ _ 1≡gcd[n,p] _ = sym 1≡gcd[n,p]
... | tri< 1<gcd[n,p] _ _ = contradiction p≤n (<⇒≱ n<p)
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

compositionalityⁱ : ∀ n → 1 < n → Acc _<_ n → Compositionality n
primalityⁱ : ∀ n → 1 < n → Acc _<_ n → Primality n

compositionalityⁱ n 1<n (acc downward)
  = loop 2 (from-yes (1 <? 2)) 1<n binary-search ¬p<2[p∤n]
  where
  ¬p<2[p∤n] : ∀ {p} → p < 2 → IsPrime p → p ∤ n
  ¬p<2[p∤n] {p} p<2 p-isPrime _ = contradiction p-isPrime (¬prime<2 p p<2)
  cons
    : ∀ {x}
    → (IsPrime x → x ∤ n)
    → (∀ {p} → p < x → IsPrime p → p ∤ n)
    → (∀ {p} → p < 1 + x → IsPrime p → p ∤ n)
  cons {x} x-isPrime⇒x∤n ∀p<x[p∤n] {p} p<1+x p-isPrime p∣n with <-cmp p x
  ... | tri< p<x _ _ = contradiction p∣n (∀p<x[p∤n] p<x p-isPrime)
  ... | tri≈ _ refl _ = contradiction p∣n (x-isPrime⇒x∤n p-isPrime)
  ... | tri> _ _ x<p = contradiction (suc-injective-≤ p<1+x) (<⇒≱ x<p)
  loop
    : ∀ x → 1 < x → x ≤ n → [ x , n ]
    → (∀ {p} → p < x → IsPrime p → p ∤ n)
    → Compositionality n
  loop x 1<x x≤n (acc _ upward) ∀p<x[p∤n] with n≤m⇒n<m⊎n≡m x≤n
  ... | inj₂ refl = Prime✓ ∀p<x[p∤n]
  ... | inj₁ x<n with primalityⁱ x 1<x (downward _ x<n)
  ...   | Composite✓ x-isComposite = loop (1 + x) (<-trans 1<x n<1+n) x<n (upward ≤-refl x<n) ∀p<1+x[p∤n]
          where ∀p<1+x[p∤n] = cons (λ x-isPrime _ → exclusive x-isPrime x-isComposite) ∀p<x[p∤n]
  ...   | Prime✓ x-isPrime with x ∣? n
  ...     | yes x∣n = Composite✓ (IsComposite✓ x x<n x-isPrime x∣n)
  ...     | no ¬x∣n = loop (1 + x) (<-trans 1<x n<1+n) x<n (upward ≤-refl x<n) ∀p<1+x[p∤n]
          where ∀p<1+x[p∤n] = cons (λ _ x∣n → ¬x∣n x∣n) ∀p<x[p∤n]

primalityⁱ n 1<n wf@(acc downward) with compositionalityⁱ n 1<n wf
... | Composite✓ isComposite = Composite✓ isComposite
  -- n is a composite so just return the proof of compositionality
... | Prime✓ ∀p<n[p∤n] = Prime✓ (IsPrime✓ 1<n ∀i∣n[i≡n])
  -- All prime divisors less then n do not divide n therefore n is prime (#1)
  where
  n≢0 : n ≢ 0
  n≢0 n≡0 = <-irrefl (sym n≡0) (<-trans 0<1+n 1<n)
  ∀i∣n[i≡n] : ∀ {i} → 1 < i → i ∣ n → i ≡ n
  ∀i∣n[i≡n] {i} 1<i i∣n with <-cmp i n
  ... | tri> _ _ n<i = contradiction (∣⇒≤ {n≢0 = ≢⇒¬≟ n≢0} i∣n) (<⇒≱ n<i)
      -- i is larger than n so i divides n so i is less then or equal to n ⇒⇐
  ... | tri≈ _ i≡n _ = i≡n
  ... | tri< i<n _ _ with primalityⁱ i 1<i (downward _ i<n)
  ...   | Prime✓ i-isPrime
        = contradiction i∣n (∀p<n[p∤n] i<n i-isPrime)
        -- i is a prime divisor of n (#1) ⇒⇐
  ...   | Composite✓ (IsComposite✓ p p<i p-isPrime p∣i)
        = contradiction (∣-trans p∣i i∣n) (∀p<n[p∤n] (<-trans p<i i<n) p-isPrime)
        -- i is a composite number with a prime divisor therefore there exists a prime divisor of n (#1) ⇒⇐

primality : ∀ n → 1 < n → Primality n
primality n 1<n = primalityⁱ n 1<n <-well-founded

prime? : ∀ n → Dec (IsPrime n)
prime? n with 1 <? n
... | no ¬1<n = no λ { (IsPrime✓ 1<n _) → ¬1<n 1<n }
... | yes 1<n with primality n 1<n
... | Prime✓ isPrime = yes isPrime
... | Composite✓ isComposite = no λ { isPrime → exclusive isPrime isComposite }

composite? : ∀ n → Dec (IsComposite n)
composite? n with 1 <? n
... | no ¬1<n = no λ { (IsComposite✓ p p<n (IsPrime✓ 1<p _) _) → ¬1<n (<-trans 1<p p<n) }
... | yes 1<n with primality n 1<n
... | Prime✓ isPrime = no λ { isComposite → exclusive isPrime isComposite }
... | Composite✓ isComposite = yes isComposite

13-isPrime : IsPrime 13
13-isPrime = from-yes (prime? 13)

24-isComposite : IsComposite 24
24-isComposite = from-yes (composite? 24)
