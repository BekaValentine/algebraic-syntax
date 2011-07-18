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
unit-digraph = digraph One (const (const ⊥))


IsLinearOrder : ∀ {n} → Digraph n → Set n
IsLinearOrder (digraph _ _<_) = Transitive _<_ ∧ Trichotomous _<_

record LinearOrder ℓ : Set (suc ℓ) where
  constructor linear-order
  field
    carrier : Set ℓ
    _<_ : Rel carrier ℓ
    isLinearOrder : IsLinearOrder (digraph carrier _<_)

IsTree : ∀ {n} → (dg : Digraph n) → Digraph.carrier dg → Set n
IsTree (digraph X _<_) r = Transitive _<_ ∧ Irreflexive _<_ ∧ Asymmetric _<_ ∧ Rooted r _<_

record Tree ℓ : Set (suc ℓ) where
  constructor tree
  field
    carrier : Set ℓ
    root : carrier
    _<_ : Rel carrier ℓ
    isTree : IsTree (digraph carrier _<_) root

unit-tree : ∀ {n} → Tree n
unit-tree {n} = tree One * (const2 ⊥) ((λ {x} {y} {z} → f {x} {y} {z}) ,
                                       (λ {x} → g {x}) ,
                                       (λ {x} {y} → h {x} {y}) ,
                                       (λ {x} → k {x}))
  where f : ∀ {x y z : One} → ⊥ ∧ ⊥ → ⊥
        f {*} {*} {*} (() , ())
        
        g : ∀ {x : One} → ⊥ → ⊥
        g {*} ()
        
        h : ∀ {x y : One} → ⊥ ∧ ⊥ → ⊥
        h {*} {*} (() , ())
        
        k : ∀ {y : One} → * == y ∨ ⊥
        k {*} = inl (refl *)


imdom : ∀ {n} → (t : Tree n) → Tree.carrier t → Tree.carrier t → Set n
imdom (tree X _ _<_ _) x y = ¬(x == y) ∧ x < y ∧ (∀ {z : X} → ¬(x < z ∧ z < y))

IsSingleDominanceTree : ∀ {n} → (t : Tree n) → Set n
IsSingleDominanceTree t = ∀ {x y z : Tree.carrier t} → imdom t x z ∧ imdom t y z → x == y

record SingleDominanceTree ℓ : Set (suc ℓ) where
  constructor sdtree
  field
    carrier : Set ℓ
    root : carrier
    _<_ : Rel carrier ℓ
    isTree : IsTree (digraph carrier _<_) root
    isSingleDominanceTree : IsSingleDominanceTree (tree carrier root _<_ isTree)

sd-underlying-tree : ∀ {n} → SingleDominanceTree n → Tree n
sd-underlying-tree (sdtree X r _<_ t sd) = tree X r _<_ t

unit-sdtree : ∀ {n} → SingleDominanceTree n
unit-sdtree = sdtree One * (const2 ⊥) (Tree.isTree unit-tree) (const (refl *))

IsCCommandRel : ∀ {ℓ} → (t : SingleDominanceTree ℓ) → Rel (SingleDominanceTree.carrier t) ℓ → Set ℓ
IsCCommandRel (sdtree X r _<_ p _) _cc_ = ∀ {x y : X}
                                          → x cc y ↔
                                            ¬ (x == y) ∧
                                            ¬ (x < y) ∧
                                            ¬ (y < x) ∧
                                            ∃ X (λ z → imdom (tree X r _<_ p) z x ∧ z < y)

CCommandRel : ∀ {ℓ} → (t : SingleDominanceTree ℓ) → Set (suc ℓ)
CCommandRel {ℓ} (sdtree X r _<_ p _) = ∀ (x y : X)
                                       → ¬ (x == y) ∧
                                         ¬ (x < y) ∧
                                         ¬ (y < x) ∧
                                         ∃ X (λ z → imdom (tree X r _<_ p) z x ∧ z < y)
                                       → Set ℓ

record CCommandTree ℓ : Set (suc ℓ) where
  constructor cctree
  field
    carrier : Set ℓ
    root : carrier
    _<_ : Rel carrier ℓ
    _cc_ : Rel carrier ℓ
    isTree : IsTree (digraph carrier _<_) root
    isSingleDominanceTree : IsSingleDominanceTree (tree carrier root _<_ isTree)
    isCCommandRel : IsCCommandRel (sdtree carrier root _<_ isTree isSingleDominanceTree) _cc_








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