{-# OPTIONS --universe-polymorphism #-}

open import Naturals
open import Functions
open import Logic
open import Relations

module Structures where



record One {n} : Set n where
  constructor *



record Digraph ℓ : Set (suc ℓ) where
  constructor digraph
  field
    carrier : Set ℓ
    edges : Rel carrier ℓ

unit-digraph : ∀ {n} → Digraph n
unit-digraph = digraph One (const2 ⊥)


IsLinearOrder : ∀ {n} → Digraph n → Set n
IsLinearOrder (digraph _ _<_) = Transitive _<_ ∧ Trichotomous _<_

record LinearOrder ℓ : Set (suc ℓ) where
  constructor linear-order
  field
    carrier : Set ℓ
    _<_ : Rel carrier ℓ
    isLinearOrder : IsLinearOrder (digraph carrier _<_)

IsTree : ∀ {n} → Digraph n → Set n
IsTree (digraph X _<_) = Transitive _<_ ∧ Irreflexive _<_ ∧ Asymmetric _<_ ∧ (∃ X (λ x → ∀ (y : X) → x == y ∨ x < y))

record Tree ℓ : Set (suc ℓ) where
  constructor tree
  field
    carrier : Set ℓ
    _<_ : Rel carrier ℓ
    isTree : IsTree (digraph carrier _<_)

root : ∀ {n} → (t : Tree n) → Tree.carrier t
root (tree _ _ (_ , _ , _ , exists r _)) = r

unit-tree : ∀ {n} → Tree n
unit-tree {n} = tree One (const2 ⊥) ((λ {x} {y} {z} → fst) ,
                                     (λ {x} → id) ,
                                     (λ {x} {y} → g {x} {y}) ,
                                     exists′ * (const′ (inl (refl *))))
  where g : ∀ {x y : One} → ⊥ × ⊥ → ⊥
        g (() , ())


imdom : ∀ {n} → (t : Tree n) → Tree.carrier t → Tree.carrier t → Set n
imdom (tree X _<_ _) x y = ¬(x == y) ∧ x < y ∧ (∀ {z : X} → ¬(x < z ∧ z < y))

IsSingleDominanceTree : ∀ {n} → (t : Tree n) → Set n
IsSingleDominanceTree t = ∀ {x y z : Tree.carrier t} → imdom t x z ∧ imdom t y z → x == y

record SingleDominanceTree ℓ : Set (suc ℓ) where
  constructor sdtree
  field
    carrier : Set ℓ
    _<_ : Rel carrier ℓ
    isTree : IsTree (digraph carrier _<_)
    isSingleDominanceTree : IsSingleDominanceTree (tree carrier _<_ isTree)

sdroot : ∀ {n} → (sdt : SingleDominanceTree n) → SingleDominanceTree.carrier sdt
sdroot (sdtree _ _ (_ , _ , _ , exists r _) _) = r

sd-underlying-tree : ∀ {n} → SingleDominanceTree n → Tree n
sd-underlying-tree (sdtree X _<_ t sd) = tree X _<_ t

unit-sdtree : ∀ {n} → SingleDominanceTree n
unit-sdtree = sdtree One (const2 ⊥) (Tree.isTree unit-tree) (const (refl *))

IsCCommandRel : ∀ {ℓ} → (t : SingleDominanceTree ℓ) → Rel (SingleDominanceTree.carrier t) ℓ → Set ℓ
IsCCommandRel (sdtree X _<_ p _) _cc_ = ∀ {x y : X}
                                        → x cc y ↔ ¬ (x < y) ∧
                                          ¬ (y < x) ∧
                                          ∃ X (λ z → imdom (tree X _<_ p) z x ∧ z < y)

record CCommandTree ℓ : Set (suc ℓ) where
  constructor cctree
  field
    carrier : Set ℓ
    _<_ : Rel carrier ℓ
    _cc_ : Rel carrier ℓ
    isTree : IsTree (digraph carrier _<_)
    isSingleDominanceTree : IsSingleDominanceTree (tree carrier _<_ isTree)
    isCCommandRel : IsCCommandRel (sdtree carrier _<_ isTree isSingleDominanceTree) _cc_








{-

record CCTree ℓ : Set (suc ℓ) where
  constructor cctree
  field
    tree : Digraph ℓ
    cc : Rel (Digraph.carrier tree) ℓ
    isTree : IsTree tree
    isSingleDominanceTree : IsSingleDominanceTree tree isTree


-}
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