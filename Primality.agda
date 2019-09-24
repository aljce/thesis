{-# OPTIONS --without-K #-}
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; Dec)
open Dec
open import Relation.Unary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; resp₂) renaming (refl to ≡-refl)

open import Data.Nat using (ℕ; _+_; _*_; _≤_; _<_; _<?_; _≤?_; _>_; _≟_)
open import Data.Nat.Properties using (1+n≢0; 0<1+n; n≮n; m≤m*n; <-trans; <-irrefl; *-comm)
open ℕ
open _≤_
open import Data.Nat.Divisibility using (_∣_; divides; _∤_; 0∣⇒≡0)

open import Data.Sum using (_⊎_)
open _⊎_

module Primality where

postulate
  TODO : ∀ {a} {A : Set a} → A

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

m>n⇒m∤n : ∀ {m n} → m > n → n ≢ 0 → m ∤ n
m>n⇒m∤n {m} {n} m>n n≢0 (divides zero n≡q*m) = n≢0 n≡q*m
m>n⇒m∤n {m} {n} m>n n≡0 (divides (suc q) n≡q*m) = n≮n m m<m
  where
  open import Data.Nat.Properties using (≤-isPreorder; <⇒≤; <-transˡ; <-transʳ)
  open import Relation.Binary.Reasoning.Base.Triple ≤-isPreorder <-trans (resp₂ _<_) <⇒≤ <-transˡ <-transʳ
  m<m : m < m
  m<m = begin-strict
    m ≤⟨ m≤m*n m 0<1+n ⟩
    m * suc q ≡⟨ *-comm m (suc q) ⟩
    suc q * m ≡⟨ sym n≡q*m ⟩
    n <⟨ m>n ⟩ m ∎

2-isPrime : IsPrime 2
2-isPrime = IsPrime✓ 1<2 2-primality
  where
  1<2 = s≤s (s≤s z≤n)
  2-primality : ∀ {i} → i ∣ 2 → 1 ≡ i ⊎ 2 ≡ i
  2-primality {zero} 0∣2 = ⊥-elim (1+n≢0 (0∣⇒≡0 0∣2))
  2-primality {suc zero} _ = inj₁ ≡-refl
  2-primality {suc (suc zero)} _ = inj₂ ≡-refl
  2-primality {suc (suc (suc i))} d = ⊥-elim (m>n⇒m∤n 3+x>2 1+n≢0 d)
    where
    3+x>2 : ∀ {x} → 3 + x > 2
    3+x>2 = s≤s (s≤s (s≤s z≤n))

exclusive : ∀ {n} → IsPrime n → IsComposite n → ⊥
exclusive (IsPrime✓ _ primality) (IsComposite✓ p p<n (IsPrime✓ 1<p _) p∣n) with primality p∣n
... | inj₁ 1≡p = <-irrefl 1≡p 1<p
... | inj₂ n≡p = <-irrefl (sym n≡p) p<n

open import Size using (Size; ∞)
open import Codata.Thunk using (Thunk; force)
open import Data.Nat using (_∸_)
open import Data.Nat.Properties using (m∸n+n≡m; +-suc; ≤-refl; ≤-step)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded; <-rec)

record Sieve {a} (f : ℕ → Set a) (n : ℕ) (i : Size) : Set a where
  constructor _∷_
  coinductive
  field
    head : f n
    tail : Thunk (Sieve f (suc n)) i
open Sieve public

map : ∀ {a b} {f : ℕ → Set a} {g : ℕ → Set b} {n : ℕ} {i : Size} → (∀ m → f m → g m) → Sieve f n i → Sieve g n i
map {n = n} eta s = eta n (head s) ∷ λ where .force → map eta (force (tail s))

module _ {a} {f : ℕ → Set a} {i : Size} where

  index : ∀ {s} n → s ≤ n → Sieve f s ∞ → f n
  index {s} n s≤n = loop (n ∸ s) s (m∸n+n≡m s≤n)
    where
    loop : ∀ count start → count + start ≡ n → Sieve f start ∞ → f n
    loop zero start ≡-refl nums = head nums
    loop (suc count) start count+start≡n nums rewrite sym(+-suc count start) =
      loop count (suc start) count+start≡n (force (tail nums))

  enumerate : ∀ n → (∀ m → n ≤ m → f m) → Sieve f n i
  enumerate n gen = loop n ≤-refl
    where
    loop : ∀ {j} x → n ≤ x → Sieve f x j
    loop x n≤x = gen x n≤x ∷ λ where .force → loop (suc x) (≤-step n≤x)

primality? : ∀ n → 1 < n → (∀ m → 1 < m → m < n → IsPrime m ⊎ IsComposite m) → IsPrime n ⊎ IsComposite n
primality? n 1<n sub? = TODO

{-# TERMINATING #-}
sieve : Sieve (λ n → IsPrime n ⊎ IsComposite n) 2 ∞
sieve = enumerate 2 (λ x 1<x → primality? x 1<x (λ m 1<m m<x → index m 1<m sieve))

primality : ∀ n → 1 < n → IsPrime n ⊎ IsComposite n
primality n 1<n = index n 1<n sieve

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
