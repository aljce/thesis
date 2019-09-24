{-# OPTIONS --without-K --safe #-}
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_; Dec)
open Dec
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; resp₂) renaming (refl to ≡-refl)

open import Data.Nat using (ℕ; _+_; _*_; _≤_; _<_; _<?_; _>_; _≟_)
open import Data.Nat.Properties using (1+n≢0; 0<1+n; n≮n; m≤m*n; *-comm)
open ℕ
open _≤_
open import Data.Nat.Divisibility using (_∣_; divides; _∤_; 0∣⇒≡0)

open import Data.Sum using (_⊎_)
open _⊎_

module Primality where

record IsPrime (p : ℕ) : Set where
  constructor IsPrime✓
  field
    1<p : 1 < p
    primality : ∀ {i} → i ∣ p → 1 ≡ i ⊎ p ≡ i

m>n⇒m∤n : ∀ {m n} → m > n → n ≢ 0 → m ∤ n
m>n⇒m∤n {m} {n} m>n n≢0 (divides zero n≡q*m) = n≢0 n≡q*m
m>n⇒m∤n {m} {n} m>n n≡0 (divides (suc q) n≡q*m) = n≮n m m<m
  where
  open import Data.Nat.Properties using (≤-isPreorder; <-trans; <⇒≤; <-transˡ; <-transʳ)
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


