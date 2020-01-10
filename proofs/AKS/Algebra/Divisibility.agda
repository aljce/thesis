open import Level using (_⊔_)
open import Function using (_$_)

open import Data.Empty using (⊥)

open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Rel; Reflexive; Transitive; Antisymmetric; _Respects₂_; _Respectsʳ_; _Respectsˡ_; Symmetric; Decidable; Irrelevant)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl; cong to ≡-cong)

open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Algebra.Bundles using (CommutativeSemiring)

module AKS.Algebra.Divisibility {c ℓ} (S : CommutativeSemiring c ℓ) where

open import AKS.Nat using (ℕ; _<_; <-irrelevant)
open import AKS.Nat.WellFounded using (Acc; acc; <-well-founded)

open CommutativeSemiring S using (_+_; _*_; 0#; 1#) renaming (Carrier to C)
open CommutativeSemiring S using (_≈_; setoid; refl; sym; trans)
open import Relation.Binary.Reasoning.Setoid setoid
open CommutativeSemiring S using (+-cong; +-congˡ; +-congʳ; +-identityʳ; +-comm; +-assoc)
open CommutativeSemiring S using (*-assoc; *-identityˡ; *-identityʳ; *-congˡ; *-congʳ; zeroˡ; zeroʳ; distribʳ; distribˡ; *-comm)
open import Algebra.Core using (Op₂)
open import Algebra.Definitions _≈_ using (Commutative; Congruent₂; LeftCongruent; RightCongruent)

infix 4 _≉_
_≉_ : Rel C ℓ
x ≉ y = x ≈ y → ⊥

infix 4 _∣_
record _∣_ (d : C) (a : C) : Set (c ⊔ ℓ) where
  constructor divides
  field
    quotient : C
    equality : a ≈ (quotient * d)

∣-refl : Reflexive _∣_
∣-refl {x} = divides 1# (sym (*-identityˡ x))

∣-trans : Transitive _∣_
∣-trans {x} {y} {z} (divides q₁ y≈q₁*x) (divides q₂ z≈q₂*y) = divides (q₂ * q₁) $ begin
  z ≈⟨ z≈q₂*y ⟩
  q₂ * y ≈⟨ *-congˡ y≈q₁*x ⟩
  q₂ * (q₁ * x) ≈⟨ sym (*-assoc q₂ q₁ x) ⟩
  (q₂ * q₁) * x ∎

∣-respʳ : _∣_ Respectsʳ _≈_
∣-respʳ {y} {x₁} {x₂} x₁≈x₂ (divides q x₁≈q*y) = divides q $ begin
  x₂    ≈⟨ sym x₁≈x₂ ⟩
  x₁    ≈⟨ x₁≈q*y ⟩
  q * y ∎

∣-respˡ : _∣_ Respectsˡ _≈_
∣-respˡ {y} {x₁} {x₂} x₁≈x₂ (divides q y≈q*x₁) = divides q $ begin
  y      ≈⟨ y≈q*x₁ ⟩
  q * x₁ ≈⟨ *-congˡ x₁≈x₂ ⟩
  q * x₂ ∎

∣-resp : _∣_ Respects₂ _≈_
∣-resp = ∣-respʳ , ∣-respˡ

infix 10 1∣_ _∣0

1∣_ : ∀ n → 1# ∣ n
1∣ n = divides n (sym (*-identityʳ n))

_∣0 : ∀ n → n ∣ 0#
n ∣0 = divides 0# (sym (zeroˡ n))

0∣n⇒n≈0 : ∀ {n} → 0# ∣ n → n ≈ 0#
0∣n⇒n≈0 {n} (divides q n≈q*0) = begin
  n      ≈⟨ n≈q*0 ⟩
  q * 0# ≈⟨ zeroʳ q ⟩
  0#     ∎

∣n⇒∣m*n : ∀ i n m → i ∣ n → i ∣ m * n
∣n⇒∣m*n i n m (divides q n≈q*i) = divides (m * q) $ begin
  m * n       ≈⟨ *-congˡ n≈q*i ⟩
  m * (q * i) ≈⟨ sym (*-assoc m q i) ⟩
  m * q * i   ∎

∣n⇒∣n*m : ∀ i n m → i ∣ n → i ∣ n * m
∣n⇒∣n*m i n m i∣n = ∣-respʳ (*-comm m n) (∣n⇒∣m*n i n m i∣n)

record IsGCD (gcd : Op₂ C) : Set (c ⊔ ℓ) where
  field
    gcd[a,b]∣a : ∀ a b → gcd a b ∣ a
    gcd[a,b]∣b : ∀ a b → gcd a b ∣ b
    gcd-greatest : ∀ {c a b} → c ∣ a → c ∣ b → c ∣ gcd a b

module GCD {gcd : Op₂ C} (isGCD : IsGCD gcd) (∣-antisym : Antisymmetric _≈_ _∣_) where
  open IsGCD isGCD

  ∣1⇒≈1 : ∀ {n} → n ∣ 1# → n ≈ 1#
  ∣1⇒≈1 {n} n∣1 = ∣-antisym n∣1 (1∣ n)

  gcd[0,0]≈0 : gcd 0# 0# ≈ 0#
  gcd[0,0]≈0 = ∣-antisym (gcd 0# 0# ∣0) (gcd-greatest ∣-refl ∣-refl)

  gcd-comm : Commutative gcd
  gcd-comm a b = ∣-antisym
    (gcd-greatest (gcd[a,b]∣b a b) (gcd[a,b]∣a a b))
    (gcd-greatest (gcd[a,b]∣b b a) (gcd[a,b]∣a b a))

  gcd[0,a]≈a : ∀ a → gcd 0# a ≈ a
  gcd[0,a]≈a a = ∣-antisym (gcd[a,b]∣b 0# a) (gcd-greatest (a ∣0) ∣-refl)

  gcd[a,0]≈a : ∀ a → gcd a 0# ≈ a
  gcd[a,0]≈a a = ∣-antisym (gcd[a,b]∣a a 0#) (gcd-greatest ∣-refl (a ∣0))

  gcd[0,a]≈1⇒a≈1 : ∀ a → gcd 0# a ≈ 1# → a ≈ 1#
  gcd[0,a]≈1⇒a≈1 a gcd[0,a]≈1 = ∣1⇒≈1 (∣-respʳ gcd[0,a]≈1 (gcd-greatest (a ∣0) ∣-refl))

  gcd[a,0]≈1⇒a≈1 : ∀ a → gcd a 0# ≈ 1# → a ≈ 1#
  gcd[a,0]≈1⇒a≈1 a gcd[a,0]≈1 = ∣1⇒≈1 (∣-respʳ gcd[a,0]≈1 (gcd-greatest ∣-refl (a ∣0)))

  gcd[a,b]≈0⇒a≈0 : ∀ {a b} → gcd a b ≈ 0# → a ≈ 0#
  gcd[a,b]≈0⇒a≈0 {a} {b} gcd[a,b]≈0 = 0∣n⇒n≈0 (∣-respˡ gcd[a,b]≈0 (gcd[a,b]∣a a b))

  gcd[a,b]≈0⇒b≈0 : ∀ {a b} → gcd a b ≈ 0# → b ≈ 0#
  gcd[a,b]≈0⇒b≈0 {a} {b} gcd[a,b]≈0 = 0∣n⇒n≈0 (∣-respˡ gcd[a,b]≈0 (gcd[a,b]∣b a b))

  gcd[a,1]≈1 : ∀ a → gcd a 1# ≈ 1#
  gcd[a,1]≈1 a = ∣-antisym (gcd[a,b]∣b a 1#) (gcd-greatest (1∣ a) ∣-refl)

  gcd[1,a]≈1 : ∀ a → gcd 1# a ≈ 1#
  gcd[1,a]≈1 a = ∣-antisym (gcd[a,b]∣a 1# a) (gcd-greatest ∣-refl (1∣ a))

  -- gcd[d*a,d*b]≈d*gcd[a,b] : ∀ a b d → gcd (d * a) (d * b) ≈ d * gcd a b
  -- gcd[d*a,d*b]≈d*gcd[a,b] = ?

  a≉0⇒gcd[a,b]≉0 : ∀ a b → a ≉ 0# → gcd a b ≉ 0#
  a≉0⇒gcd[a,b]≉0 a b a≉0 gcd[a,b]≈0 = a≉0 (gcd[a,b]≈0⇒a≈0 gcd[a,b]≈0)

  b≉0⇒gcd[a,b]≉0 : ∀ a b → b ≉ 0# → gcd a b ≉ 0#
  b≉0⇒gcd[a,b]≉0 a b b≉0 gcd[a,b]≈0 = b≉0 (gcd[a,b]≈0⇒b≈0 gcd[a,b]≈0)

  gcd-cong : Congruent₂ gcd
  gcd-cong {a} {b} {c} {d} a≈b c≈d = ∣-antisym
    (gcd-greatest (∣-respʳ a≈b (gcd[a,b]∣a a c)) (∣-respʳ c≈d (gcd[a,b]∣b a c)))
    (gcd-greatest (∣-respʳ (sym a≈b) (gcd[a,b]∣a b d)) (∣-respʳ (sym c≈d) (gcd[a,b]∣b b d)))

  gcd-congˡ : LeftCongruent gcd
  gcd-congˡ c≈d = gcd-cong refl c≈d

  gcd-congʳ : RightCongruent gcd
  gcd-congʳ a≈b = gcd-cong a≈b refl

  infix 4 _⊥_
  _⊥_ : C → C → Set ℓ
  n ⊥ m = gcd n m ≈ 1#

  ⊥-sym : Symmetric _⊥_
  ⊥-sym {x} {y} gcd[x,y]≡1 = begin
    gcd y x ≈⟨ gcd-comm y x ⟩
    gcd x y ≈⟨ gcd[x,y]≡1 ⟩
    1# ∎

  ⊥-respʳ : _⊥_ Respectsʳ _≈_
  ⊥-respʳ {y} {x₁} {x₂} x₁≈x₂ gcd[y,x₁]≈1 = begin
    gcd y x₂ ≈⟨ gcd-congˡ (sym x₁≈x₂) ⟩
    gcd y x₁ ≈⟨ gcd[y,x₁]≈1 ⟩
    1# ∎

  ⊥-respˡ : _⊥_ Respectsˡ _≈_
  ⊥-respˡ {y} {x₁} {x₂} x₁≈x₂ gcd[x₁,y]≈1 = begin
    gcd x₂ y ≈⟨ gcd-congʳ (sym x₁≈x₂) ⟩
    gcd x₁ y ≈⟨ gcd[x₁,y]≈1 ⟩
    1# ∎

  ⊥-resp : _⊥_ Respects₂ _≈_
  ⊥-resp = ⊥-respʳ , ⊥-respˡ


module _
  (∣_∣ : ∀ n {n≉0 : n ≉ 0#} → ℕ)
  (_div_ : ∀ (n m : C) {m≉0 : m ≉ 0#} → C) (_mod_ : ∀ (n m : C) {m≉0 : m ≉ 0#} → C)
  where

  data Remainder (n : C) (m : C) {m≉0 : m ≉ 0#} : Set (c ⊔ ℓ) where
    0≈ : (r≈0 : (n mod m) {m≉0} ≈ 0#) → Remainder n m
    0≉ : (r≉0 : (n mod m) {m≉0} ≉ 0#) → ∣ n mod m ∣ {r≉0} < ∣ m ∣ {m≉0} → Remainder n m

  module Euclidean
    (_≈?_ : Decidable _≈_)
    (≈-irrelevant : Irrelevant _≈_)
    (≉-irrelevant : Irrelevant _≉_)
    (∣-antisym : Antisymmetric _≈_ _∣_)
    (division : ∀ n m {m≉0 : m ≉ 0#} → n ≈ m * (n div m) {m≉0} + (n mod m) {m≉0})
    (modulus : ∀ n m {m≉0 : m ≉ 0#} → Remainder n m {m≉0})
    (mod-cong : ∀ {x₁ x₂} {y₁ y₂} → x₁ ≈ x₂ → y₁ ≈ y₂ → ∀ {y₁≉0 y₂≉0} → (x₁ mod y₁) {y₁≉0} ≈ (x₂ mod y₂) {y₂≉0})
    (mod-distribʳ-* : ∀ c a b {b≉0} {b*c≉0} → ((a * c) mod (b * c)) {b*c≉0} ≈ (a mod b) {b≉0} * c)
    where

    -- ∣-antisym : Antisymmetric _≈_ _∣_
    -- ∣-antisym {x} {y} (divides q₁ y≈q₁*x) (divides q₂ x≈q₂*y) with q₁ ≈? 0#
    -- ... | yes q₁≈0 = ?
    -- ... | no  q₁≉0 with q₂ ≈? 0#
    -- ...   | yes q₂≈0 = ?
    -- ...   | no  q₂≉0 = q₁≉0∧q₂≉0⇒x≈y q₁≉0 q₂≉0
    --   where
    --   q₁≉0∧q₂≉0⇒x≈y : q₁ ≉ 0# → q₂ ≉ 0# → x ≈ y
    --   q₁≉0∧q₂≉0⇒x≈y q₁≉0 q₂≉0 = ?

    gcdₕ : ∀ (n m : C) {m≉0 : m ≉ 0#} → Acc _<_ (∣ m ∣ {m≉0}) → C
    gcdₕ n m {m≉0} (acc downward) with modulus n m {m≉0}
    ... | 0≈ r≈0 = m
    ... | 0≉ r≉0 r<m = gcdₕ m (n mod m) (downward _ r<m)

    gcd : C → C → C
    gcd n m with m ≈? 0#
    ... | yes m≈0 = n
    ... | no  m≉0 = gcdₕ n m {m≉0} <-well-founded

    ∣b∣a%b⇒∣a : ∀ {c a b} {b≉0 : b ≉ 0#} → c ∣ b → c ∣ (a mod b) {b≉0} → c ∣ a
    ∣b∣a%b⇒∣a {c} {a} {b} {b≉0} (divides q₁ b≈q₁*c) (divides q₂ a%b≈q₂*c) = divides ((a div b) {b≉0} * q₁ + q₂) $ begin
      a                             ≈⟨ division a b {b≉0} ⟩
      b * (a div b) + a mod b       ≈⟨ +-cong (*-congʳ b≈q₁*c) a%b≈q₂*c ⟩
      (q₁ * c) * (a div b) + q₂ * c ≈⟨ +-congʳ (*-comm (q₁ * c) (a div b)) ⟩
      (a div b) * (q₁ * c) + q₂ * c ≈⟨ +-congʳ (sym (*-assoc (a div b) q₁ c)) ⟩
      ((a div b) * q₁) * c + q₂ * c ≈⟨ sym (distribʳ c ((a div b) * q₁) q₂) ⟩
      ((a div b) * q₁ + q₂) * c     ∎

    gcd[a,b]∣a×gcd[a,b]∣b : ∀ a b → (gcd a b ∣ a) × (gcd a b ∣ b)
    gcd[a,b]∣a×gcd[a,b]∣b a b with b ≈? 0#
    ... | yes b≈0 = ∣-refl , (∣-respʳ (sym b≈0) (a ∣0))
    ... | no  b≉0 = loop a b {b≉0} <-well-founded
      where
      loop : ∀ a b {b≉0} (rec : Acc _<_ (∣ b ∣ {b≉0})) → (gcdₕ a b rec ∣ a) × (gcdₕ a b rec ∣ b)
      loop a b {b≉0} (acc downward) with modulus a b {b≉0}
      ... | 0≈ r≈0 = ∣b∣a%b⇒∣a ∣-refl (∣-respʳ (sym r≈0) (b ∣0)) , ∣-refl
      ... | 0≉ r≉0 r<m with loop b (a mod b) (downward _ r<m)
      ...   | gcd∣b , gcd∣a%b = ∣b∣a%b⇒∣a gcd∣b gcd∣a%b , gcd∣b

    ∣a∣b⇒∣a%b : ∀ {c a b} {b≉0 : b ≉ 0#} → c ∣ a → c ∣ b → c ∣ (a mod b) {b≉0}
    ∣a∣b⇒∣a%b {c} {a} {b} {b≉0} (divides q₁ a≈q₁*c) (divides q₂ b≈q₂*c) = divides ((q₁ mod q₂) {q≉0}) $ begin
      a mod b ≈⟨ mod-cong a≈q₁*c b≈q₂*c {b≉0} {q₂*c≉0} ⟩
      (q₁ * c) mod (q₂ * c) ≈⟨ mod-distribʳ-* c q₁ q₂ ⟩
      (q₁ mod q₂) * c ∎
      where
      q≉0 : q₂ ≉ 0#
      q≉0 q₂≈0 = b≉0 $ begin
        b      ≈⟨ b≈q₂*c ⟩
        q₂ * c ≈⟨ *-congʳ q₂≈0 ⟩
        0# * c ≈⟨ zeroˡ c ⟩
        0#     ∎
      q₂*c≉0 : q₂ * c ≉ 0#
      q₂*c≉0 q₂*c≈0 = b≉0 $ begin
        b ≈⟨ b≈q₂*c ⟩
        q₂ * c ≈⟨ q₂*c≈0 ⟩
        0# ∎

    gcd-greatest : ∀ {c a b} → c ∣ a → c ∣ b → c ∣ gcd a b
    gcd-greatest {c} {a} {b} c∣a c∣b with b ≈? 0#
    ... | yes b≈0 = c∣a
    ... | no  b≉0 = loop c a b <-well-founded c∣a c∣b
      where
      loop : ∀ c a b {b≉0} (rec : Acc _<_ (∣ b ∣ {b≉0})) → c ∣ a → c ∣ b → c ∣ gcdₕ a b rec
      loop c a b {b≉0} (acc downward) c∣a c∣b with modulus a b {b≉0}
      ... | 0≈ r≈0 = c∣b
      ... | 0≉ r≉0 r<m = loop c b (a mod b) (downward _ r<m) c∣b (∣a∣b⇒∣a%b c∣a c∣b)

    gcd-isGCD : IsGCD gcd
    gcd-isGCD = record
      { gcd[a,b]∣a = λ a b → proj₁ (gcd[a,b]∣a×gcd[a,b]∣b a b)
      ; gcd[a,b]∣b = λ a b → proj₂ (gcd[a,b]∣a×gcd[a,b]∣b a b)
      ; gcd-greatest = gcd-greatest
      }

    open GCD gcd-isGCD ∣-antisym public

    data Identity (d : C) (a : C) (b : C) : Set (c ⊔ ℓ) where
      +ʳ : ∀ (x y : C) → d + x * a ≈ y * b → Identity d a b
      +ˡ : ∀ (x y : C) → d + y * b ≈ x * a → Identity d a b

    identity-sym : ∀ {d} → Symmetric (Identity d)
    identity-sym (+ʳ x y pf) = +ˡ y x pf
    identity-sym (+ˡ x y pf) = +ʳ y x pf

    identity-base : ∀ {d a} → Identity d d a
    identity-base {d} {a} = +ˡ 1# 0# $ begin
      d + 0# * a  ≈⟨ +-congˡ (zeroˡ a) ⟩
      d + 0#      ≈⟨ +-identityʳ d ⟩
      d           ≈⟨ sym (*-identityˡ d) ⟩
      1# * d      ∎

    stepʳ
      : ∀ d x y a b {b≉0}
      → d + x * b ≈ y * (a mod b) {b≉0}
      → d + (x + y * (a div b) {b≉0}) * b ≈ y * a
    stepʳ d x y a b {b≉0} d+x*b≈y*[a%b] = begin
      d + (x + y * a div b) * b       ≈⟨ +-congˡ (distribʳ b x (y * (a div b) {b≉0})) ⟩
      d + (x * b + y * a div b * b)   ≈⟨ sym (+-assoc d (x * b) (y * a div b * b)) ⟩
      (d + x * b) + y * a div b * b   ≈⟨ +-cong d+x*b≈y*[a%b] (*-assoc y (a div b) b) ⟩
      y * a mod b + y * (a div b * b) ≈⟨ sym (distribˡ y (a mod b) (a div b * b)) ⟩
      y * (a mod b + a div b * b)     ≈⟨ *-congˡ (+-comm (a mod b) (a div b * b)) ⟩
      y * (a div b * b + a mod b)     ≈⟨ *-congˡ (+-congʳ (*-comm (a div b) b)) ⟩
      y * (b * a div b + a mod b)     ≈⟨ *-congˡ (sym (division a b)) ⟩
      y * a                           ∎

    stepˡ
      : ∀ d x y a b {b≉0}
      → d + y * (a mod b) {b≉0} ≈ x * b
      → d + y * a ≈ (x + y * (a div b) {b≉0}) * b
    stepˡ d x y a b {b≉0} d+x*b≈y*[a%b] = begin
      d + y * a                               ≈⟨ +-congˡ (*-congˡ (division a b {b≉0})) ⟩
      d + y * (b * a div b + a mod b)         ≈⟨ +-congˡ (*-congˡ (+-comm (b * a div b) (a mod b))) ⟩
      d + y * (a mod b + b * a div b)         ≈⟨ +-congˡ (distribˡ y (a mod b) (b * a div b)) ⟩
      d + (y * (a mod b) + y * (b * a div b)) ≈⟨ sym (+-assoc d (y * (a mod b)) (y * (b * a div b))) ⟩
      (d + y * (a mod b)) + y * (b * a div b) ≈⟨ +-cong d+x*b≈y*[a%b] (*-congˡ (*-comm b (a div b))) ⟩
      x * b + y * (a div b * b)               ≈⟨ +-congˡ (sym (*-assoc y (a div b) b)) ⟩
      x * b + (y * a div b) * b               ≈⟨ sym (distribʳ b x (y * a div b)) ⟩
      (x + y * (a div b)) * b                 ∎

    identity-step : ∀ {d a b} {b≉0} → Identity d b ((a mod b) {b≉0}) → Identity d a b
    identity-step {d} {a} {b} {b≉0} (+ʳ x y d+x*b≈y*[a%b]) = +ˡ y (x + y * (a div b)) (stepʳ d x y a b {b≉0} d+x*b≈y*[a%b])
    identity-step {d} {a} {b} {b≉0} (+ˡ x y d+y*[a%b]≈x*b) = +ʳ y (x + y * (a div b)) (stepˡ d x y a b {b≉0} d+y*[a%b]≈x*b)

    data Bézoutₕ (a : C) (b : C) {b≉0 : b ≉ 0#} (rec : Acc _<_ (∣ b ∣ {b≉0})) : Set (c ⊔ ℓ) where
      lemmaₕ : ∀ d → gcdₕ a b rec ≈ d → Identity d a b → Bézoutₕ a b rec

    gcdₕ-base : ∀ {a b} {b≉0} {rec : Acc _<_ (∣ b ∣ {b≉0})} (r≈0 : (a mod b) {b≉0} ≈ 0#) → gcdₕ a b rec ≈ b
    gcdₕ-base {a} {b} {b≉0} {acc downward} [r≈0]₁ with modulus a b {b≉0}
    ... | 0≈ [r≈0]₂ rewrite ≈-irrelevant [r≈0]₁ [r≈0]₂ = refl
    ... | 0≉ r≉0 _  = contradiction [r≈0]₁ r≉0

    gcdₕ-step
      : ∀ {d a b} {b≉0} {r≉0 : (a mod b) {b≉0} ≉ 0#} {r<m : ∣ a mod b ∣ {r≉0} < ∣ b ∣ {b≉0}} {downward}
      → gcdₕ b (a mod b) (downward ∣ a mod b ∣ r<m) ≈ d → gcdₕ a b (acc downward) ≈ d
    gcdₕ-step {d} {a} {b} {b≉0} {[r≉0]₁} {[r<m]₁} gcdₕ[b,a%b]≈d with modulus a b {b≉0}
    ... | 0≈ r≈0 = contradiction r≈0 [r≉0]₁
    ... | 0≉ [r≉0]₂ [r<m]₂ rewrite ≉-irrelevant [r≉0]₁ [r≉0]₂ | <-irrelevant [r<m]₁ [r<m]₂ = gcdₕ[b,a%b]≈d

    bézoutₕ : ∀ a b {b≉0} (rec : Acc _<_ (∣ b ∣ {b≉0})) → Bézoutₕ a b rec
    bézoutₕ a b {b≉0} (acc downward) with modulus a b {b≉0}
    ... | 0≈ r≈0 = lemmaₕ b (gcdₕ-base r≈0) (identity-sym identity-base)
    ... | 0≉ r≉0 r<m with bézoutₕ b (a mod b) {r≉0} (downward _ r<m)
    ...   | lemmaₕ d gcdₕ[b,a%b]≈d ident = lemmaₕ d (gcdₕ-step gcdₕ[b,a%b]≈d) (identity-step ident)

    data Bézout (a : C) (b : C) : Set (c ⊔ ℓ) where
      lemma : ∀ d → gcd a b ≈ d → Identity d a b → Bézout a b

    b≈0⇒gcd[a,b]≈a : ∀ a b → b ≈ 0# → gcd a b ≈ a
    b≈0⇒gcd[a,b]≈a a b b≈0 with b ≈? 0#
    ... | yes _  = refl
    ... | no b≉0 = contradiction b≈0 b≉0

    gcdₕ⇒gcd : ∀ {d a b} {b≉0} → gcdₕ a b {b≉0} <-well-founded ≈ d → gcd a b ≈ d
    gcdₕ⇒gcd {d} {a} {b} {[b≉0]₁} gcdₕ[a,b]≈d with b ≈? 0#
    ... | yes b≈0 = contradiction b≈0 [b≉0]₁
    ... | no [b≉0]₂ rewrite ≉-irrelevant [b≉0]₁ [b≉0]₂ = gcdₕ[a,b]≈d

    bézout : ∀ a b → Bézout a b
    bézout a b with b ≈? 0#
    ... | yes b≈0 = lemma a (b≈0⇒gcd[a,b]≈a a b b≈0) identity-base
    ... | no  b≉0 with bézoutₕ a b {b≉0} <-well-founded
    ...   | lemmaₕ d gcdₕ[a,b]≈d ident = lemma d (gcdₕ⇒gcd gcdₕ[a,b]≈d) ident
