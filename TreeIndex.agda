open import Data.Empty
open import Data.Product
open import Relation.Binary.Core
open import Relation.Nullary

module TreeIndex where




data Tree : Set where
  leaf : Tree
  branch : Tree → Tree → Tree

data TreeIndex : Tree → Set where
  root : {t : Tree} → TreeIndex t
  left : {l r : Tree} → TreeIndex l → TreeIndex (branch l r)
  right : {l r : Tree} → TreeIndex r → TreeIndex (branch l r)

data _<_ : {t : Tree} → TreeIndex t → TreeIndex t → Set where
  rt<l-ze : {l r : Tree} {i : TreeIndex l} → _<_ {branch l r} root (left i)
  rt<r-ze : {l r : Tree} {i : TreeIndex r} → _<_ {branch l r} root (right i)
  rt<l-su : {l r : Tree} {i j : TreeIndex l} → i < j → _<_ {branch l r} (left i) (left j)
  rt<r-su : {l r : Tree} {i j : TreeIndex r} → i < j → _<_ {branch l r} (right i) (right j)

data _<⁺_ : {t : Tree} → TreeIndex t → TreeIndex t → Set where
  <⁺-ze : {t : Tree} {i j : TreeIndex t} → i < j → i <⁺ j
  <⁺-su : {t : Tree} {i j : TreeIndex t} → root < i → i <⁺ j → root <⁺ j

¬i<rt : ∀ {t : Tree} {i : TreeIndex t}
      → ¬ i < root
¬i<rt ()

Rel₀ : Set → Set₁
Rel₀ X = X → X → Set

infixr 3 _↔_
_↔_ : Set → Set → Set
X ↔ Y = (X → Y) × (Y → X)

cc-merge-lemma : {l r : Tree}
               → (_cc₀_ : Rel₀ (TreeIndex l))
               → (_cc₁_ : Rel₀ (TreeIndex r))
               → Σ[ _cc₂_ ∶ Rel₀ (TreeIndex (branch l r)) ]
                  (∀ (x y : TreeIndex (branch l r))
                   → (x cc₂ y ↔ (¬ (x ≡ y) ×
                                 ¬ (x <⁺ y) ×
                                 ¬ (y <⁺ x) ×
                                 (Σ[ z ∶ TreeIndex (branch l r) ] z < x × z <⁺ y))))
cc-merge-lemma {l} {r} _cc₀_ _cc₁_ = _cc₂_ , p
  where _cc₂_ : Rel₀ (TreeIndex (branch l r))
        root cc₂ root = ⊥
        root cc₂ left y = ⊥
        root cc₂ right y = ⊥
        left x cc₂ root = ⊥
        left x cc₂ left y = {!!}
        left x cc₂ right y = {!!}
        right x cc₂ y = {!!}
        
        p : ∀ (x y : _)
            → (x cc₂ y ↔ (¬ (x ≡ y) ×
                         ¬ (x <⁺ y) ×
                         ¬ (y <⁺ x) ×
                         (Σ[ z ∶ (TreeIndex (branch l r)) ] z < x × z <⁺ y)))
        p root root = fwd , bwd
          where fwd : root cc₂ root
                    → (¬ root ≡ root) ×
                      (¬ root <⁺ root) ×
                      (¬ root <⁺ root) ×
                      (Σ[ z ∶ (TreeIndex (branch l r)) ] z < root × z <⁺ root)
                fwd ()
                
                bwd : (¬ root ≡ root) ×
                      (¬ root <⁺ root) ×
                      (¬ root <⁺ root) ×
                      (Σ[ z ∶ (TreeIndex (branch l r)) ] z < root × z <⁺ root)
                    → root cc₂ root
                bwd (a , _) = ⊥-elim (a refl)
                
        p root (left y) = fwd , bwd
          where fwd : root cc₂ left y
                    → (¬ root ≡ left y) ×
                      (¬ root <⁺ left y) ×
                      (¬ left y <⁺ root) ×
                      (Σ[ z ∶ (TreeIndex (branch l r)) ] z < root × z <⁺ left y)
                fwd ()
                
                bwd : (¬ root ≡ left y) ×
                      (¬ root <⁺ left y) ×
                      (¬ left y <⁺ root) ×
                      (Σ[ z ∶ (TreeIndex (branch l r)) ] z < root × z <⁺ left y)
                    → root cc₂ left y
                bwd (_ , b , _) = ⊥-elim (b (<⁺-ze rt<l-ze))
        
        p root (right y) = fwd , bwd
          where fwd : root cc₂ right y
                    → (¬ root ≡ right y) ×
                      (¬ root <⁺ right y) ×
                      (¬ right y <⁺ root) ×
                      (Σ[ z ∶ (TreeIndex (branch l r)) ] z < root × z <⁺ right y)
                fwd ()
                
                bwd : (¬ root ≡ right y) ×
                      (¬ root <⁺ right y) ×
                      (¬ right y <⁺ root) ×
                      (Σ[ z ∶ (TreeIndex (branch l r)) ] z < root × z <⁺ right y)
                    → root cc₂ right y
                bwd (_ , b , _) = ⊥-elim (b (<⁺-ze rt<r-ze))
        
        p (left x) root = fwd , bwd
          where fwd : left x cc₂ root
                    → (¬ left x ≡ root) ×
                      (¬ left x <⁺ root) ×
                      (¬ root <⁺ left x) ×
                      (Σ[ z ∶ (TreeIndex (branch l r)) ] z < left x × z <⁺ root)
                fwd ()
                
                bwd : (¬ left x ≡ root) ×
                      (¬ left x <⁺ root) ×
                      (¬ root <⁺ left x) ×
                      (Σ[ z ∶ (TreeIndex (branch l r)) ] z < left x × z <⁺ root)
                    → left x cc₂ root
                bwd (_ , _ , c , _) = ⊥-elim (c (<⁺-ze rt<l-ze))
        
        p (left x) (left y) = fwd , bwd
          where fwd : left x cc₂ left y
                    → (¬ left x ≡ left y) ×
                      (¬ left x <⁺ left y) ×
                      (¬ left y <⁺ left x) ×
                      (Σ[ z ∶ (TreeIndex (branch l r)) ] z < left x × z <⁺ left y)
                fwd = {!!}
                
                bwd : (¬ left x ≡ left y) ×
                      (¬ left x <⁺ left y) ×
                      (¬ left y <⁺ left x) ×
                      (Σ[ z ∶ (TreeIndex (branch l r)) ] z < left x × z <⁺ left y)
                    → left x cc₂ left y
                bwd (a , b , c , d) with l
                ... | l' = ?
        
        p (left x) (right y) = {!!}
        p (right x) y = {!!}