{-# OPTIONS --universe-polymorphism #-}

open import Naturals
open import Logic
open import Relations
open import Functions
open import Structures

module SyntaxTrees where

data BinTree {ℓ} : Set ℓ where
  lf : BinTree
  br : BinTree → BinTree → BinTree

data TIndex {ℓ} : BinTree {ℓ} → Set ℓ where
  root : ∀ {t} → TIndex t
  left : ∀ {l r} → TIndex l → TIndex (br l r)
  right : ∀ {l r} → TIndex r → TIndex (br l r)

proj : ∀ {ℓ} → (t : BinTree {ℓ}) → TIndex t → BinTree {ℓ}
proj t root = t
proj .(br l r) (left {l} {r} i) = proj l i
proj .(br l r) (right {l} {r} i) = proj r i

data _<_ : ∀ {ℓ} {t t′ : BinTree {ℓ}} → TIndex t → TIndex t′ → Set where
  im-left : ∀ {l r} → (x : TIndex (br l r)) → (y : TIndex l) → x < y
  im-right : ∀ {l r} → (x : TIndex (br l r)) → (y : TIndex r) → x < y
  dom-trans : ∀ {t t′ t′′} {x : TIndex t} {y : TIndex t′} {z : TIndex t′′}
              → x < y → y < z → x < z

im-dom : ∀ {ℓ} (t : BinTree {ℓ}) → TIndex t → TIndex t → Set ℓ
im-dom t x y = ¬(x == y) ∧ x < y ∧ (∀ {z : TIndex t} → ¬(x < z ∧ z < y))

IsCCommandRel2 : ∀ {ℓ} → (t : BinTree {ℓ}) → Rel (TIndex t) ℓ → Set ℓ
IsCCommandRel2 t _cc_ = ∀ {x y : TIndex t} → x cc y ↔ ¬ (x == y) ∧ ¬ (x < y) ∧ ¬ (y < x) ∧
                                                      ∃ (TIndex t) (λ z → im-dom t z x ∧ z < y)

cc-comb : ∀ {ℓ} {t t′}
          → (_cc_ : Rel (TIndex t) ℓ)
          → (pcc : IsCCommandRel2 t _cc_)
          → (_cc′_ : Rel (TIndex t′) ℓ)
          → (pcc′ : IsCCommandRel2 t′ _cc′_)
          → ∃ (Rel (TIndex (br t t′)) ℓ) (λ _cc′′_ → IsCCommandRel2 (br t t′) _cc′′_)
cc-comb {ℓ} {t} {t′} _cc_ pcc _cc′_ pcc′ = exists _cc′′_ (λ {x} {y} → pcc′′ {x} {y})
  where _cc′′_ : Rel (TIndex (br t t′)) ℓ
        root cc′′ root = ⊥
        root cc′′ _ = {!!}
        left _ cc′′ _ = {!!}
        right _ cc′′ _ = {!!}
        
        pcc′′ : IsCCommandRel2 (br t t′) _cc′′_
        pcc′′ {root} {root} = {!fwd!} , bwd
          where bwd : ¬ (root == root) ∧
                      ¬ (root < root) ∧
                      ¬ (root < root) ∧
                      ∃ (TIndex (br t t′)) (λ z → im-dom (br t t′) z root ∧ z < root)
                      → root cc′′ root
                bwd a with fst a (refl root)
                bwd _ | ()
        
        pcc′′ {root} {left y} = {!!}
        pcc′′ {root} {right y} = {!!}
        pcc′′ {left x} {y} = {!!}
        pcc′′ {right x} {y} = {!!}