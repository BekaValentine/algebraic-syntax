{-# OPTIONS --universe-polymorphism #-}

open import Naturals
open import Functions
open import Logic
open import Relations

module Structures where



record Digraph {ℓ} : Set (suc ℓ) where
  constructor digraph
  field
    carrier : Set ℓ
    edges : Rel carrier ℓ



TotalOrder : ∀ {n} → Digraph {n} → Set n
TotalOrder (digraph _ _≤_) = Reflexive _≤_ × Transitive _≤_ ∧ Antisymmetric _≤_ ∧ Total _≤_

LinearOrder : ∀ {n} → Digraph {n} → Set n
LinearOrder (digraph _ _<_) = Transitive _<_ ∧ Trichotomous _<_

Tree : ∀ {n} → Digraph {n} → Set n
Tree (digraph X _<_) = ∃ X (λ x → (y : X) → x == y ∨ x < y)

{-

depth : BinTree → ℕ
depth leaf = zero
depth (branch t t′) = depth t ⊔ depth t′

postulate _==_ : ∀ {n} {X : Set n} → X → X → Set n

FiniteBinTree : BinTree → Set
FiniteBinTree t = ∃ ℕ (λ n → n == depth t)

InfiniteBinTree : BinTree → Set
InfiniteBinTree t = ¬(FiniteBinTree t)

HasBottom : BinTree → Set
HasBottom leaf = ⊥
HasBottom (branch leaf leaf) = ⊤
HasBottom (branch l r) = HasBottom l ∨ HasBottom r
-}