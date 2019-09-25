{-# OPTIONS --without-K --safe #-}
open import Function using (_$_)

open import Data.Sum using (_⊎_)
open _⊎_

open import Data.Nat using (ℕ; _+_; _∸_; _*_; _≤_; _<_; _<?_; _≤?_; _>_; _≟_)
open ℕ
open _≤_
open import Data.Nat.Properties using (1+n≢0; 0<1+n; n≮n; m≤m*n; <-trans; <-irrefl; *-comm)
open import Data.Nat.Properties using (m∸n+n≡m; m+[n∸m]≡n; +-suc; m≤m+n; ≤-refl; ≤-step; <-cmp; <-asym)
open import Data.Nat.Properties using (≤-isPreorder; <⇒≤; <-transˡ; <-transʳ; m≤n+m; m≤m*n; n≢0⇒n>0; suc-injective)
open import Data.Nat.Divisibility using (_∣_; divides; _∤_; _∣?_; 0∣⇒≡0; ∣1⇒≡1; ∣-trans)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded; <-rec)

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; Dec)
open Dec
open import Relation.Nullary.Decidable using (from-yes)
open import Relation.Unary using (Decidable)
open import Relation.Binary using (Tri)
open Tri
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; resp₂) renaming (refl to ≡-refl)
open import Relation.Binary.Reasoning.Base.Triple ≤-isPreorder <-trans (resp₂ _<_) <⇒≤ <-transˡ <-transʳ

module Primality where

-- postulate
--   TODO : ∀ {a} {A : Set a} → A

record IsPrime (p : ℕ) : Set where
  constructor IsPrime✓
  field
    1<p : 1 < p
    primality : ∀ {i} → i ∣ p → 1 ≡ i ⊎ p ≡ i

record IsComposite (c : ℕ) : Set where
  constructor IsComposite✓
  field
    p : ℕ
    p<c : p < c
    P[c] : IsPrime p
    composite : p ∣ c

exclusive : ∀ {n} → IsPrime n → IsComposite n → ⊥
exclusive (IsPrime✓ _ primality) (IsComposite✓ p p<n (IsPrime✓ 1<p _) p∣n) with primality p∣n
... | inj₁ 1≡p = <-irrefl 1≡p 1<p
... | inj₂ n≡p = <-irrefl (sym n≡p) p<n

¬prime<2 : ∀ p → p < 2 → IsPrime p → ⊥
¬prime<2 .(suc (suc _)) (s≤s (s≤s ())) (IsPrime✓ (s≤s (s≤s 1<p)) primality)

compositionality?
  : ∀ n
  → 1 < n
  → (∀ m → 1 < m → m < n → IsPrime m ⊎ IsComposite m)
  → IsComposite n ⊎ (∀ p → p < n → IsPrime p → p ∤ n)
compositionality? n 1<n primality? = loop (n ∸ 2) 2 (m∸n+n≡m 1<n) 1<2 ¬prime∣2
  where
  1<2 : 1 < 2
  1<2 = s≤s (s≤s z≤n)

  ¬prime∣2 : ∀ p → p < 2 → IsPrime p → p ∤ n
  ¬prime∣2 p p<2 p-isPrime = ⊥-elim (¬prime<2 p p<2 p-isPrime)

  cons
    : ∀ {x}
    → (IsPrime x → x ∤ n)
    → (∀ p → p < x → IsPrime p → p ∤ n)
    → (∀ p → p < 1 + x → IsPrime p → p ∤ n)
  cons {x} ¬x-isPrime ∀p<x[p∤x] p p<1+x p-isPrime p∣n with <-cmp p x
  ... | tri< p<x _ _ = ∀p<x[p∤x] p p<x p-isPrime p∣n
  ... | tri≈ _ ≡-refl _ = ¬x-isPrime p-isPrime p∣n
  ... | tri> ¬p<x p≢x _ = ¬p<x (lemma p<1+x p≢x)
    where
    lemma : ∀ {a b} → a < 1 + b → a ≢ b → a < b
    lemma (s≤s z≤n) x≢y = n≢0⇒n>0 λ x≡y → x≢y (sym x≡y)
    lemma (s≤s (s≤s s)) x≢y = s≤s (lemma (s≤s s) (λ { ≡-refl → x≢y ≡-refl }))

  lemma1 : ∀ {count start} → suc count + start ≡ n → start < n
  lemma1 {count} {start} 1+count+start≡n = begin-strict
    start ≤⟨ m≤n+m start count ⟩
    count + start <⟨ ≤-refl ⟩
    suc (count + start) ≡⟨ 1+count+start≡n ⟩ n ∎

  loop : ∀ count start
       → count + start ≡ n
       → 1 < start
       → (∀ p → p < start → IsPrime p → p ∤ n)
       → IsComposite n ⊎ (∀ p → p < n → IsPrime p → p ∤ n)
  loop zero start ≡-refl 1<start ∀p[p∤start] = inj₂ ∀p[p∤start]
  loop (suc count) start count+start≡n 1<start ∀p[p∤start] with primality? start 1<start (lemma1 count+start≡n)
  ... | inj₂ start-isComposite rewrite sym(+-suc count start)
      = loop count (suc start) count+start≡n (≤-step 1<start) (cons (λ start-isPrime _ → exclusive start-isPrime start-isComposite) ∀p[p∤start])
  ... | inj₁ start-isPrime with start ∣? n
  ...   | yes p∣n = inj₁ (IsComposite✓ start (lemma1 count+start≡n) start-isPrime p∣n)
  ...   | no ¬p∣n rewrite sym(+-suc count start) = loop count (suc start) count+start≡n (≤-step 1<start) (cons (λ _ p∣n → ¬p∣n p∣n) ∀p[p∤start])

primality? : ∀ n → 1 < n → (∀ m → 1 < m → m < n → IsPrime m ⊎ IsComposite m) → IsPrime n ⊎ IsComposite n
primality? n 1<n primality<n? with compositionality? n 1<n primality<n?
... | inj₁ n-isComposite = inj₂ n-isComposite
... | inj₂ ∀p<n[p∤n] = inj₁ (IsPrime✓ 1<n n-primality)
  where
  lemma1 : ∀ {a b} → a ∣ b → a > b → b > 0 → ⊥
  lemma1 {a} {b} (divides zero b≡q*a) a>b b>0 = n≮n b $ begin-strict
    b ≡⟨ b≡q*a ⟩
    0 <⟨ b>0 ⟩ b ∎
  lemma1 {a} {b} (divides (suc q) b≡q*a) a>b _ = n≮n a $ begin-strict
    a ≤⟨ m≤m*n a 0<1+n ⟩
    a * suc q ≡⟨ *-comm a (suc q) ⟩
    suc q * a ≡⟨ sym (b≡q*a) ⟩
    b <⟨ a>b ⟩ a ∎

  lemma2 : ∀ {a} → a ∣ n → 1 > a → ⊥
  lemma2 0∣n (s≤s z≤n) = <-irrefl (sym (0∣⇒≡0 0∣n)) (<-trans 0<1+n 1<n)

  n-primality : ∀ {i} → i ∣ n → 1 ≡ i ⊎ n ≡ i
  n-primality {i} i∣n with <-cmp 1 i
  ... | tri> _ _ 1>i = ⊥-elim (lemma2 i∣n 1>i)
  ... | tri≈ _ 1≡i _ = inj₁ 1≡i
  ... | tri< 1<i _ _ with <-cmp i n
  ...   | tri> _ _ i>n = ⊥-elim (lemma1 i∣n i>n (<-trans 0<1+n 1<n))
  ...   | tri≈ _ i≡n _ = inj₂ (sym (i≡n))
  ...   | tri< i<n _ _ with primality<n? i 1<i i<n
  ...     | inj₁ i-isPrime = ⊥-elim (∀p<n[p∤n] i i<n i-isPrime i∣n)
  ...     | inj₂ (IsComposite✓ p p<i p-isPrime p∣i) = ⊥-elim (∀p<n[p∤n] p (<-trans p<i i<n) p-isPrime (∣-trans p∣i i∣n))

primality : ∀ n → 1 < n → IsPrime n ⊎ IsComposite n
primality n 1<n = loop n 1<n (<-wellFounded n)
  where
  loop : ∀ x → 1 < x → Acc _<_ x → IsPrime x ⊎ IsComposite x
  loop x 1<x (acc downward) = primality? x 1<x λ m 1<m m<x → loop m 1<m (downward m m<x)

prime? : Decidable IsPrime
prime? n with 1 <? n
... | no ¬1<n = no λ { (IsPrime✓ 1<n _) → ¬1<n 1<n }
... | yes 1<n with primality n 1<n
... | inj₁ isPrime = yes isPrime
... | inj₂ isComposite = no λ { isPrime → exclusive isPrime isComposite }

composite? : Decidable IsComposite
composite? n with 1 <? n
... | no ¬1<n = no λ { (IsComposite✓ p p<n (IsPrime✓ 1<p _) _) → ¬1<n (<-trans 1<p p<n) }
... | yes 1<n with primality n 1<n
... | inj₁ isPrime = no λ { isComposite → exclusive isPrime isComposite }
... | inj₂ isComposite = yes isComposite

13-isPrime : IsPrime 13
13-isPrime = from-yes (prime? 13)

24-isComposite : IsComposite 24
24-isComposite = from-yes (composite? 24)

-- open import Size using (Size; ∞)
-- open import Codata.Thunk using (Thunk; force)

-- record Sieve {a} (f : ℕ → Set a) (n : ℕ) (i : Size) : Set a where
--   constructor _∷_
--   coinductive
--   field
--     head : f n
--     tail : Thunk (Sieve f (suc n)) i
-- open Sieve public

-- map : ∀ {a b} {f : ℕ → Set a} {g : ℕ → Set b} {n : ℕ} {i : Size} → (∀ m → f m → g m) → Sieve f n i → Sieve g n i
-- map {n = n} eta s = eta n (head s) ∷ λ where .force → map eta (force (tail s))

-- module _ {a} {f : ℕ → Set a} {i : Size} where

--   index : ∀ {s} n → s ≤ n → Sieve f s ∞ → f n
--   index {s} n s≤n = loop (n ∸ s) s (m∸n+n≡m s≤n)
--     where
--     loop : ∀ count start → count + start ≡ n → Sieve f start ∞ → f n
--     loop zero start ≡-refl nums = head nums
--     loop (suc count) start count+start≡n nums rewrite sym(+-suc count start) =
--       loop count (suc start) count+start≡n (force (tail nums))

--   enumerate : ∀ n → (∀ m → n ≤ m → f m) → Sieve f n i
--   enumerate n gen = loop n ≤-refl
--     where
--     loop : ∀ {j} x → n ≤ x → Sieve f x j
--     loop x n≤x = gen x n≤x ∷ λ where .force → loop (suc x) (≤-step n≤x)

-- {-# TERMINATING #-}
-- sieve : Sieve (λ n → IsPrime n ⊎ IsComposite n) 2 ∞
-- sieve = TODO -- enumerate 2 (λ x 1<x → primality? x 1<x (λ m 1<m m<x → index m 1<m sieve))
