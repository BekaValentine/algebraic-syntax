{-# OPTIONS --universe-polymorphism #-}

open import Level

module Syntax.TreeIndex where



data TreeShape : Set where
  leaf : TreeShape
  branch : TreeShape → TreeShape → TreeShape

data TreeIndex : TreeShape → Set where
  root : {t : TreeShape} → TreeIndex t
  left : {l r : TreeShape} → TreeIndex l → TreeIndex (branch l r)
  right : {l r : TreeShape} → TreeIndex r → TreeIndex (branch l r)

data _<_ : {t : TreeShape} → TreeIndex t → TreeIndex t → Set where
  <-ze-l : {l r : TreeShape} {x : TreeIndex l} → _<_ {branch l r} root (left x)
  <-ze-r : {l r : TreeShape} {y : TreeIndex r} → _<_ {branch l r} root (right y)
  <-su-l : {l r : TreeShape} {x y : TreeIndex l} → _<_ {l} x y → _<_ {branch l r} (left x) (left y)
  <-su-r : {l r : TreeShape} {x y : TreeIndex r} → _<_ {r} x y → _<_ {branch l r} (right x) (right y)

treeind : {ℓ : Level}
        → (P : TreeShape → Set ℓ)
        → P leaf
        → ((l r : TreeShape) → P l → P r → P (branch l r))
        → (t : TreeShape) → P t
treeind P z f leaf = z
treeind P z f (branch l r) = f l r (treeind P z f l) (treeind P z f r)