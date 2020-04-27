open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

module AKS.Nat.WellFounded where

open import AKS.Nat.Base using (ℕ; _+_; _∸_; _≤_; _<_; lte)
open ℕ
open import AKS.Nat.Properties using (+-identityʳ; +-suc; ∸-mono-<ˡ; ∸-mono-<ʳ; suc-injective)

data Acc {A : Set} (_≺_ : A → A → Set) (bound : A) : Set where
  acc : (∀ {lower : A} → lower ≺ bound → Acc _≺_ lower)
      → Acc _≺_ bound

subrelation
    : ∀ {A : Set} {B : Set}
        {_≺₁_ : A → A → Set}
        {_≺₂_ : B → B → Set}
        {f : B → A}
        {n : B}
    → (∀ {x y} → x ≺₂ y → f x ≺₁ f y)
    → Acc _≺₁_ (f n)
    → Acc _≺₂_ n
subrelation ≺₂⇒≺₁ (acc down) =
  acc λ x≺₂n → subrelation ≺₂⇒≺₁ (down (≺₂⇒≺₁ x≺₂n))

data _≤ⁱ_ : ℕ → ℕ → Set where
  ≤-same : ∀ {n} → n ≤ⁱ n
  ≤-step : ∀ {n m} → n ≤ⁱ m → n ≤ⁱ suc m

_<ⁱ_ : ℕ → ℕ → Set
n <ⁱ m = suc n ≤ⁱ m

<⇒<ⁱ : ∀ {n m} → n < m → n <ⁱ m
<⇒<ⁱ {n} {m} (lte zero refl) rewrite +-identityʳ n = ≤-same
<⇒<ⁱ {n} {m} (lte (suc k) refl) = ≤-step (<⇒<ⁱ (lte k (sym (+-suc n k))))

<-well-founded : ∀ {n} → Acc _<_ n
<-well-founded {n} = wf₁ n
  where
  wf₁ : ∀ t → Acc _<_ t
  wf₂ : ∀ t b → b <ⁱ t → Acc _<_ b
  wf₁ t = acc λ {b} b<t → wf₂ t b (<⇒<ⁱ b<t)
  wf₂ (suc t) b ≤-same = wf₁ t
  wf₂ (suc t) b (≤-step b<ⁱt) = wf₂ t b b<ⁱt

record [_,_] (low : ℕ) (high : ℕ) : Set where
  inductive
  constructor acc
  field
    downward : ∀ {mid} → low ≤ mid → mid < high → [ low , mid ]
    upward : ∀ {mid} → low < mid → mid ≤ high → [ mid , high ]

binary-search : ∀ {n m} → [ n , m ]
binary-search {n} {m} = loop n m <-well-founded
  where
  loop : ∀ low high → Acc _<_ (high ∸ low) → [ low , high ]
  loop low high (acc next) = acc
    (λ {mid} low≤mid mid<high → loop low mid (next {mid ∸ low} (∸-mono-<ˡ low≤mid mid<high)))
    (λ {mid} low<mid mid≤high → loop mid high (next {high ∸ mid} (∸-mono-<ʳ mid≤high low<mid)))

open import AKS.Unsafe using (trustMe)

record Interval : Set where
  constructor [_,_∣_]
  field
    inf : ℕ
    sup : ℕ
    inf≤sup : inf ≤ sup
open Interval

width : Interval → ℕ
width i = sup i ∸ inf i

data _⊂_ (i₁ : Interval) (i₂ : Interval) : Set where
  downward : inf i₂ ≤ inf i₁ → sup i₁ < sup i₂ → i₁ ⊂ i₂
  upward : inf i₂ < inf i₁ → sup i₁ ≤ sup i₂ → i₁ ⊂ i₂

∸-monoˡ-< : ∀ {l₁ h₁ l₂ h₂} → l₁ ≤ h₁ → l₂ ≤ h₂ → l₂ ≤ l₁ → h₁ < h₂ → h₁ ∸ l₁ < h₂ ∸ l₂
∸-monoˡ-< {l₁} {h₁} {l₂} {h₂} l₁≤h₁ l₂≤h₂ l₂≤l₁ h₁<h₂ = lte ((h₂ ∸ l₂) ∸ suc (h₁ ∸ l₁)) trustMe -- TODO: EVIL

∸-monoʳ-< : ∀ {l₁ h₁ l₂ h₂} → l₁ ≤ h₁ → l₂ ≤ h₂ → l₂ < l₁ → h₁ ≤ h₂ → h₁ ∸ l₁ < h₂ ∸ l₂
∸-monoʳ-< {l₁} {h₁} {l₂} {h₂} l₁≤h₁ l₂≤h₂ l₂<l₁ h₁≤h₂ = lte ((h₂ ∸ l₂) ∸ suc (h₁ ∸ l₁)) trustMe

⊂⇒< : ∀ {i₁ i₂} → i₁ ⊂ i₂ → width i₁ < width i₂
⊂⇒< {[ inf-i₁ , sup-i₁ ∣ inf-i₁≤sup-i₁ ]} {[ inf-i₂ , sup-i₂ ∣ inf-i₂≤sup-i₂ ]} (downward inf-i₂≤inf-i₁ sup-i₁<sup-i₂)
  = ∸-monoˡ-< inf-i₁≤sup-i₁ inf-i₂≤sup-i₂ inf-i₂≤inf-i₁ sup-i₁<sup-i₂
⊂⇒< {[ inf-i₁ , sup-i₁ ∣ inf-i₁≤sup-i₁ ]} {[ inf-i₂ , sup-i₂ ∣ inf-i₂≤sup-i₂ ]} (upward inf-i₂<inf-i₁ sup-i₁≤sup-i₂)
  = ∸-monoʳ-< inf-i₁≤sup-i₁ inf-i₂≤sup-i₂ inf-i₂<inf-i₁ sup-i₁≤sup-i₂

⊂-well-founded : ∀ {i} → Acc _⊂_ i
⊂-well-founded = subrelation ⊂⇒< <-well-founded

