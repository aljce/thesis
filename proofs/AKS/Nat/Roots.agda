open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Data.Sum using (_⊎_)
open _⊎_

module AKS.Nat.Roots where

open import AKS.Nat using (ℕ; _≤_; _<_; n≤m⇒n<m⊎n≡m; <-irrefl; *-1-commutativeMonoid)
open ℕ
open import AKS.Nat using ([_,_]; binary-search; acc)
open import AKS.Exponentiation *-1-commutativeMonoid using (_^_)

record Root (n : ℕ) (b : ℕ) : Set where
  constructor Root✓
  field
    root : ℕ
    root^b≤n : root ^ b ≤ n
    n<root^[1+b] : n < (suc root) ^ b

open import AKS.Unsafe using (TODO)

find-root : ∀ n b → Root n b
find-root n b = loop 0 n binary-search
  where
  loop : ∀ l h → [ l , h ] → Root n b
  loop l h (acc downward upward) = TODO

-- root-unique : root ^ b < n → n < (suc root) ^ b

record Power (n : ℕ) (b : ℕ) : Set where
  constructor Power✓
  field
    root : ℕ
    n≡root^b : n ≡ root ^ b

power? : ∀ n b → Dec (Power n b)
power? n b with find-root n b
... | Root✓ root₁ root₁^b≤n n<root₁^[1+b] with n≤m⇒n<m⊎n≡m root₁^b≤n
...   | inj₁ root₁^b<n = no λ { (Power✓ root₂ n≡root₂^b) → TODO }
...   | inj₂ root₁^b≡n = yes (Power✓ root₁ (sym root₁^b≡n))

record Perfect (n : ℕ) : Set where
  constructor Perfect✓
  field
    b : ℕ
    power : Power n b

perfect? : ∀ n → Dec (Perfect n)
perfect? = TODO
