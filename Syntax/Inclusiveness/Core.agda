open import Data.Product
open import Function
open import Level
open import Relation.Binary.Core

open import Syntax.Derivationality
open import Syntax.Logic
open import Syntax.TreeIndex

module Syntax.Inclusiveness.Core where



IsInclusiveRelation : ({t : TreeShape} → Rel (TreeIndex t) zero) → Set
IsInclusiveRelation _~_ = ((l r : TreeShape) → _~_ ⇔′ (_~_ on left {l} {r}))
                        × ((l r : TreeShape) → _~_ ⇔′ (_~_ on right {l} {r}))



record InclusiveRelation : Set₁ where
  constructor inclusiveRelation
  field
    _~_ : {t : TreeShape} → Rel (TreeIndex t) zero
    isInclusiveRelation : IsInclusiveRelation _~_



record InclusiveDerivationalRelation : Set₁ where
  constructor inclusiveDerivationalRelation
  field
    indr : DerivationalRelation
    isInclusiveRelation : IsInclusiveRelation (DerivationalRelation._~_ indr)



IsLeftInclusionPreservingOperation : (Set → Set → Set) → Set₁
IsLeftInclusionPreservingOperation _*_ = (l r l' r' : TreeShape)
                                       → (P : InclusiveRelation)
                                       → (Q : InclusiveRelation)
                                       → (x y : TreeIndex l)
                                       → (z w : TreeIndex l')
                                       → ((InclusiveRelation._~_ P x y) * (InclusiveRelation._~_ Q z w)) ↔
                                         ((InclusiveRelation._~_ P (left {l} {r} x) (left {l} {r} y)) *
                                          (InclusiveRelation._~_ Q (left {l'} {r'} z) (left {l'} {r'} w)))



IsRightInclusionPreservingOperation : (Set → Set → Set) → Set₁
IsRightInclusionPreservingOperation _*_ = (l r l' r' : TreeShape)
                                        → (P : InclusiveRelation)
                                        → (Q : InclusiveRelation)
                                        → (x y : TreeIndex r)
                                        → (z w : TreeIndex r')
                                        → ((InclusiveRelation._~_ P x y) * (InclusiveRelation._~_ Q z w)) ↔
                                          ((InclusiveRelation._~_ P (right {l} {r} x) (right {l} {r} y)) *
                                           (InclusiveRelation._~_ Q (right {l'} {r'} z) (right {l'} {r'} w)))



IsInclusionPreservingOperation : (Set → Set → Set) → Set₁
IsInclusionPreservingOperation _*_ = IsLeftInclusionPreservingOperation _*_ ×
                                     IsRightInclusionPreservingOperation _*_



record InclusionPreservingOperation : Set₁ where
  constructor inclusionPreservingOperation
  field
    _*_ : Set → Set → Set
    isInclusionPreservingOperation : IsInclusionPreservingOperation _*_