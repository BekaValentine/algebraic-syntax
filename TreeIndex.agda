{-# OPTIONS --universe-polymorphism #-}

open import Data.Bool
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Function
open import Level
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

module TreeIndex where



data Tree : Set where
  leaf : Tree
  branch : Tree → Tree → Tree

data TreeIndex : Tree → Set where
  root : {t : Tree} → TreeIndex t
  left : {l r : Tree} → TreeIndex l → TreeIndex (branch l r)
  right : {l r : Tree} → TreeIndex r → TreeIndex (branch l r)

treeind : {ℓ : Level}
        → (P : Tree → Set ℓ)
        → P leaf
        → ((l r : Tree) → P l → P r → P (branch l r))
        → (t : Tree) → P t
treeind P z f leaf = z
treeind P z f (branch l r) = f l r (treeind P z f l) (treeind P z f r)

infixr 1 _↔_
_↔_ : {l : Level} → Set l → Set l → Set l
X ↔ Y = (X → Y) × (Y → X)

record IsInductionPrinciple {ℓ : Level} (P : Tree → Set ℓ) (F : (t : Tree) → P t) : Set _ where
  field
    baseCase : P leaf
    recursiveCase : (l r : Tree) → P l → P r → P (branch l r)
    proof : (t : Tree) → {!!} ↔ treeind {!!} {!!} {!!} {!!}

{-
IsInductionPrinciple P F = Σ[ z ∶ P leaf ]
                              Σ[ f ∶ ((l r : Tree)
                                   → P l
                                   → P r
                                   → P (branch l r)) ]
                                 ((t : Tree) → F t ↔ treeind P z f t)
-}
{-
data _<_ : {t : Tree} → TreeIndex t → TreeIndex t → Set where
  <-ze-l : {l r : Tree} → _<_ {branch l r} root (left root)
  <-ze-r : {l r : Tree} → _<_ {branch l r }root (right root)
  <-su-l : {l r : Tree} {i j : TreeIndex l} → i < j → _<_ {branch l r} (left i) (left j)
  <-su-r : {l r : Tree} {i j : TreeIndex r} → i < j → _<_ {branch l r} (right i) (right j)

data _#_ : {t : Tree} → TreeIndex t → TreeIndex t → Set where
  #-ze : {l r : Tree} → _#_ {branch l r} (left root) (right root)
  #-su-l : {l r : Tree} {x y : TreeIndex l} → x # y → _#_ {branch l r} (left x) (left y)
  #-su-r : {l r : Tree} {x y : TreeIndex r} → x # y → _#_ {branch l r} (right x) (right y)

data _<₀_ : {t : Tree} → TreeIndex t → TreeIndex t → Set where
  <₀-ze : {t : Tree} {i j : TreeIndex t} → i < j → i <₀ j
  <₀-su : {t : Tree} {i j k : TreeIndex t} → i <₀ j → j <₀ k → i <₀ k

data _<⁺_ : {t : Tree} → TreeIndex t → TreeIndex t → Set where
  <⁺-ze : {t : Tree} {i j : TreeIndex t} → i < j → i <⁺ j
  <⁺-su : {t : Tree} {i j k : TreeIndex t} → i <⁺ j → j < k → i <⁺ k

data _<⁺₀_ : {t : Tree} → TreeIndex t → TreeIndex t → Set where
  <⁺₀-ze : {t : Tree} {i j : TreeIndex t} → i < j → i <⁺₀ j
  <⁺₀-su : {t : Tree} {i j k : TreeIndex t} → i < j → j <⁺₀ k → i <⁺₀ k
-}