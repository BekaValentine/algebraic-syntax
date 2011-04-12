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

data ∃ {n} (X : Set n) (P : X → Set n) : Set n where
  exists : (x : X) → P x → ∃ X P