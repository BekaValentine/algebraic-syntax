{-# OPTIONS --universe-polymorphism #-}

open import Data.Product
open import Level
open import Relation.Binary.Core
open import Relation.Nullary

module Syntax.Logic where



infixr 1 _↔_
_↔_ : {l : Level} → Set l → Set l → Set l
X ↔ Y = (X → Y) × (Y → X)

_⇒′_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
      REL A B ℓ₁ → REL A B ℓ₂ → Set _
P ⇒′ Q = ∀ i j → P i j → Q i j

_⇔_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
    → REL A B ℓ₁ → REL A B ℓ₂ → Set _
P ⇔ Q = (P ⇒ Q) × (Q ⇒ P)

_⇔′_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
    → REL A B ℓ₁ → REL A B ℓ₂ → Set _
P ⇔′ Q = (P ⇒′ Q) × (Q ⇒′ P)

_-⟨_⟩-_ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
       → (A → B) → (B → C → D) → (A → C) → (A → D)
f -⟨ _*_ ⟩- g = λ x → f x * g x

∁₂ : {a b : Level} {A : Set a} {B : Set b}
  → REL A B (a ⊔ b)
  → REL A B (a ⊔ b)
∁₂ R = λ x y → ¬ R x y

_º : {a b ℓ : Level} {A : Set a} {B : Set b}
   → REL A B ℓ
   → REL B A ℓ
(R º) x y = R y x

Σ/ : {a b c ℓ : Level} {A : Set a} {B : Set b} {C : Set c}
   → (Set ℓ → Set ℓ → Set ℓ)
   → REL A B ℓ
   → REL A C ℓ
   → REL B C (a ⊔ ℓ)
Σ/ {A = A} _*_ _~_ _~′_ = λ x y → Σ[ z ∶ A ] (z ~ x) * (z ~′ y)