open import Level
open import Relation.Binary.Core

open import Syntax.Logic
open import Syntax.TreeIndex

module Syntax.Derivationality where



record Deriver : Set₁ where
  constructor deriver
  field
    rt~rt : Set
    rt~l l~rt rt~r r~rt : {t : TreeShape} → TreeIndex t → Set
    l~r r~l : {t t' : TreeShape} → TreeIndex t → TreeIndex t' → Set
  
  private
    baseCase : Rel (TreeIndex leaf) zero
    baseCase root root = rt~rt
    
    recursiveCase : (l r : TreeShape)
                  → Rel (TreeIndex l) zero
                  → Rel (TreeIndex r) zero
                  → Rel (TreeIndex (branch l r)) zero
    recursiveCase l r L R root root = rt~rt
    recursiveCase l r L R root (left y) = rt~l y
    recursiveCase l r L R root (right y) = rt~r y
    recursiveCase l r L R (left x) root = l~rt x
    recursiveCase l r L R (left x) (left y) = L x y
    recursiveCase l r L R (left x) (right y) = l~r x y
    recursiveCase l r L R (right x) root = r~rt x
    recursiveCase l r L R (right x) (left y) = r~l x y
    recursiveCase l r L R (right x) (right y) = R x y
  
  _~~_ : {t : TreeShape} → Rel (TreeIndex t) zero
  _~~_ {t} = treeind (λ t → Rel (TreeIndex t) zero) baseCase recursiveCase t



IsDerivationalRelation : ({t : TreeShape} → Rel (TreeIndex t) zero)
                  → Deriver
                  → Set
IsDerivationalRelation _~_ ind = (t : TreeShape) → _~_ {t} ⇔′ Deriver._~~_ ind {t}



record DerivationalRelation : Set₁ where
  constructor derivedRelation
  field
    _~_ : {t : TreeShape} → Rel (TreeIndex t) zero
    ind : Deriver
    isDerivationalRelation : IsDerivationalRelation _~_ ind
  
  _~~_ : {t : TreeShape} → Rel (TreeIndex t) zero
  _~~_ {t} = Deriver._~~_ ind {t}