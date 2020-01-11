open import Function using (_$_)

open import Relation.Nullary using (yes; no)
open import Relation.Binary using (Decidable; Irrelevant; Antisymmetric; Setoid)
open import AKS.Algebra.Bundles using (IntegralDomain; Field)

module AKS.Algebra.Consequences {c ℓ} (I : IntegralDomain c ℓ) where

open import AKS.Nat using (ℕ)

open import Algebra.Bundles using (CommutativeRing)

open IntegralDomain I using (_+_; _*_; -_; _-_; 0#; 1#) renaming (Carrier to C)
open IntegralDomain I using (_≈_; _≉_; setoid)
open Setoid setoid using (refl; sym)
open import Relation.Binary.Reasoning.Setoid setoid
open IntegralDomain I using (commutativeRing; isIntegralDomain; *-cancelˡ)
open CommutativeRing commutativeRing using (+-identityʳ; +-assoc; +-comm; +-congʳ; +-congˡ; +-cong; -‿cong; -‿inverseʳ)
open CommutativeRing commutativeRing using (*-cong; *-congʳ; *-congˡ; zeroʳ; zeroˡ; commutativeSemiring)
open import AKS.Algebra.Structures C _≈_ using (IsField; IsEuclideanDomain; module Modulus; module Divisibility; IsGCDDomain; IsUniqueFactorizationDomain)
open import AKS.Algebra.Divisibility commutativeSemiring using (module Euclidean)
open Modulus using (Remainder; 0≈)
open Divisibility _*_ using (_∣_; divides)

module Division⇒EuclideanDomain
  (_≈?_ : Decidable _≈_)
  (≈-irrelevant : Irrelevant _≈_)
  (≉-irrelevant : Irrelevant _≉_)
  (∣_∣ : ∀ n {n≉0 : n ≉ 0#} → ℕ)
  (_div_ : ∀ (n m : C) {m≉0 : m ≉ 0#} → C)
  (_mod_ : ∀ (n m : C) {m≉0 : m ≉ 0#} → C)
  (division : ∀ n m {m≉0 : m ≉ 0#} → n ≈ m * (n div m) {m≉0} + (n mod m) {m≉0})
  (modulus : ∀ n m {m≉0 : m ≉ 0#} → Remainder 0# ∣_∣ _mod_ n m {m≉0})
  (div-cong : ∀ {x₁ x₂} {y₁ y₂} → x₁ ≈ x₂ → y₁ ≈ y₂ → ∀ {y₁≉0 y₂≉0} → (x₁ div y₁) {y₁≉0} ≈ (x₂ div y₂) {y₂≉0})
  (mod-distribʳ-* : ∀ c a b {b≉0} {b*c≉0} → ((a * c) mod (b * c)) {b*c≉0} ≈ (a mod b) {b≉0} * c)
  where

  private
    remainder : ∀ n m {m≉0 : m ≉ 0#} → (n mod m) {m≉0} ≈ n - m * (n div m) {m≉0}
    remainder n m {m≉0} = begin
      n mod m                               ≈⟨ sym (+-identityʳ (n mod m)) ⟩
      n mod m + 0#                          ≈⟨ +-congˡ (sym (-‿inverseʳ (m * n div m))) ⟩
      n mod m + (m * n div m - m * n div m) ≈⟨ sym (+-assoc (n mod m) (m * n div m) (- (m * n div m))) ⟩
      (n mod m + m * n div m) - m * n div m ≈⟨ +-congʳ (+-comm (n mod m) (m * n div m)) ⟩
      (m * n div m + n mod m) - m * n div m ≈⟨ +-congʳ (sym (division n m {m≉0})) ⟩
      n - m * n div m                       ∎

    mod-cong : ∀ {x₁ x₂} {y₁ y₂} → x₁ ≈ x₂ → y₁ ≈ y₂ → ∀ {y₁≉0 y₂≉0} → (x₁ mod y₁) {y₁≉0} ≈ (x₂ mod y₂) {y₂≉0}
    mod-cong {x₁} {x₂} {y₁} {y₂} x₁≈x₂ y₁≈y₂ {y₁≉0} {y₂≉0} = begin
      x₁ mod y₁           ≈⟨ remainder x₁ y₁ {y₁≉0} ⟩
      x₁ - y₁ * x₁ div y₁ ≈⟨ +-cong x₁≈x₂ (-‿cong (*-cong y₁≈y₂ (div-cong x₁≈x₂ y₁≈y₂))) ⟩
      x₂ - y₂ * x₂ div y₂ ≈⟨ sym (remainder x₂ y₂ {y₂≉0}) ⟩
      x₂ mod y₂           ∎

  open Euclidean ∣_∣ _div_ _mod_ _≈?_ ≈-irrelevant ≉-irrelevant division modulus mod-cong mod-distribʳ-* using (gcd; gcd-isGCD) public

  isGCDDomain : IsGCDDomain _+_ _*_ -_ 0# 1# gcd
  isGCDDomain = record { isIntegralDomain = isIntegralDomain; gcd-isGCD = gcd-isGCD }

  isUniqueFactorizationDomain : IsUniqueFactorizationDomain _+_ _*_ -_ 0# 1# gcd
  isUniqueFactorizationDomain = record { isGCDDomain = isGCDDomain }

  isEuclideanDomain : IsEuclideanDomain _+_ _*_ -_ 0# 1# ∣_∣ _div_ _mod_ gcd
  isEuclideanDomain = record
    { isUniqueFactorizationDomain = isUniqueFactorizationDomain
    ; division = division
    ; modulus = modulus
    ; div-cong = div-cong
    ; mod-cong = mod-cong
    }

module Inverse⇒Field
  (_≈?_ : Decidable _≈_)
  (≈-irrelevant : Irrelevant _≈_)
  (≉-irrelevant : Irrelevant _≉_)
  (_/_ : ∀ (n m : C) {m≉0 : m ≉ 0#} → C)
  (inverse : ∀ (n m : C) {m≉0 : m ≉ 0#} → n ≈ m * (n / m) {m≉0})
  where

  private
    ∣_∣ : ∀ n {n≉0 : n ≉ 0#} → ℕ
    ∣ _ ∣ = 0

    _mod_ : ∀ (n m : C) {m≉0 : m ≉ 0#} → C
    _ mod _ = 0#

    division : ∀ n m {m≉0 : m ≉ 0#} → n ≈ m * (n / m) {m≉0} + (n mod m) {m≉0}
    division n m {m≉0} = begin
      n ≈⟨ inverse  n m {m≉0} ⟩
      m * (n / m) ≈⟨ sym (+-identityʳ (m * (n / m))) ⟩
      m * (n / m) {m≉0} + (n mod m) {m≉0} ∎

    modulus : ∀ n m {m≉0 : m ≉ 0#} → Remainder 0# ∣_∣ _mod_ n m {m≉0}
    modulus _ _ = 0≈ refl

    div-cong : ∀ {x₁ x₂} {y₁ y₂} → x₁ ≈ x₂ → y₁ ≈ y₂ → ∀ {y₁≉0 y₂≉0} → (x₁ / y₁) {y₁≉0} ≈ (x₂ / y₂) {y₂≉0}
    div-cong {x₁} {x₂} {y₁} {y₂} x₁≈x₂ y₁≈y₂ {y₁≉0} {y₂≉0} = *-cancelˡ y₁ y₁≉0 $ begin
      y₁ * (x₁ / y₁) ≈⟨ sym (inverse x₁ y₁) ⟩
      x₁             ≈⟨ x₁≈x₂ ⟩
      x₂             ≈⟨ inverse x₂ y₂ ⟩
      y₂ * (x₂ / y₂) ≈⟨ *-congʳ (sym y₁≈y₂) ⟩
      y₁ * (x₂ / y₂) ∎

    mod-distribʳ-* : ∀ c a b {b≉0} {b*c≉0} → ((a * c) mod (b * c)) {b*c≉0} ≈ (a mod b) {b≉0} * c
    mod-distribʳ-* c a b = sym (zeroˡ c)

  open Division⇒EuclideanDomain _≈?_ ≈-irrelevant ≉-irrelevant ∣_∣ _/_ _mod_ division modulus div-cong mod-distribʳ-* using (gcd; isEuclideanDomain) public

  isField : IsField _+_ _*_ -_ 0# 1# _/_ gcd
  isField = record { isEuclideanDomain = isEuclideanDomain }

  [field] : Field c ℓ
  [field] = record { isField = isField }
