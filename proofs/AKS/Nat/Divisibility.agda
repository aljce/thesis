open import Relation.Nullary.Decidable using (False)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.WithK using (≡-erase)

module AKS.Nat.Divisibility where

open import Data.Nat.Divisibility using (_∣_) public
open import Agda.Builtin.Nat using () renaming (mod-helper to modₕ)
open import Data.Nat.DivMod using (_/_; _%_) public
open import Data.Nat.DivMod.Core using (a≤n⇒a[modₕ]n≡a)
open import Data.Nat.DivMod using (m≡m%n+[m/n]*n)

open import AKS.Nat.Base using (ℕ; _+_; _*_; _≟_; lte; _≤_; _<_)
open ℕ
open import AKS.Nat.Properties using (+-suc)
open import AKS.Nat.Properties using (m≤m+n; suc-mono-≤)
open import AKS.Nat.Properties using (*-comm)

a[modₕ]n≤n : ∀ acc d n → modₕ acc (acc + n) d n ≤ acc + n
a[modₕ]n≤n acc zero n = m≤m+n
a[modₕ]n≤n acc (suc d) zero = a[modₕ]n≤n zero d (acc + 0)
a[modₕ]n≤n acc (suc d) (suc n) rewrite +-suc acc n = a[modₕ]n≤n (suc acc) d n

n%m<m : ∀ n m {≢0 : False (m ≟ 0)} → (n % m) {≢0} < m
n%m<m n (suc m) = suc-mono-≤ (a[modₕ]n≤n 0 n m)

n<m⇒n%m≡n : ∀ {n m} {≢0 : False (m ≟ 0)} → n < m → (n % m) {≢0} ≡ n
n<m⇒n%m≡n {n} {suc m} (lte k refl) = ≡-erase (a≤n⇒a[modₕ]n≡a 0 (n + k) n k)

0%m≡0 : ∀ {m} {≢0 : False (m ≟ 0)} → (0 % m) {≢0} ≡ 0
0%m≡0 {suc m} = refl

record Euclidean (n : ℕ) (m : ℕ) : Set where
  constructor Euclidean✓
  field
    q : ℕ
    r : ℕ
    division : n ≡ r + m * q
    r<m : r < m

_div_ : ∀ n m {≢0 : False (m ≟ 0)} → Euclidean n m
n div suc m = Euclidean✓ (n / suc m) (n % suc m) (≡-erase div-proof) (n%m<m n (suc m))
  where
  div-proof : n ≡ n % suc m + suc m * (n / suc m)
  div-proof rewrite *-comm (suc m) (n / suc m) = m≡m%n+[m/n]*n n m




