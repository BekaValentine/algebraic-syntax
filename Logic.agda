{-# OPTIONS --universe-polymorphism #-}

open import Naturals
open import Functions

module Logic where



data ⊤ {n} : Set n where
  tt : ⊤

data ⊥ {n} : Set n where

¬ : ∀ {n} → Set n → Set n
¬ {n} A = A → ⊥ {n}

⊥-elim : ∀ {m n} {X : Set m} → ⊥ {n} → X
⊥-elim ()

infixr 11 _∧_
_∧_ : ∀ {n} → Set n → Set n → Set n
_∧_ = _×_

infixr 10 _∨_
_∨_ : ∀ {n} → Set n → Set n → Set n
_∨_ = _+_

infixr 10 _⊕_
_⊕_ : ∀ {n} → Set n → Set n → Set n
X ⊕ Y = (X ∧ ¬ Y) ∨ (¬ X ∧ Y)

data ∃ {m n} (X : Set m) (P : X → Set n) : Set (m ⊔ n) where
  exists : (x : X) → P x → ∃ X P

exists′ : ∀ {n} {X : Set n} {P : X → Set n} → (x : X) → P x → ∃ X P
exists′ = exists

∃-witness : ∀ {m n} {X : Set m} {P : X → Set n} → ∃ X P → X
∃-witness (exists x _) = x

∃-proof : ∀ {m n} {X : Set m} {P : X → Set n} → (ex : ∃ X P) → P (∃-witness ex)
∃-proof (exists _ p) = p

infixr 9 _↔_
_↔_ : ∀ {n} → Set n → Set n → Set n
X ↔ Y = (X → Y) ∧ (Y → X)

data Non-Empty {n} (X : Set n) : Set n where
  non-empty : X → Non-Empty X

ne-witness : ∀ {n} {X : Set n} → Non-Empty X → X
ne-witness (non-empty x) = x

Empty : ∀ {n} (X : Set n) → Set n
Empty X = ¬(Non-Empty X)