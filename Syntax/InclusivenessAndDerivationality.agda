{-# OPTIONS --universe-polymorphism #-}

open import Data.Empty
open import Data.Product
open import Data.Sum hiding (map)
open import Data.Unit
open import Function
open import Level
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Unary

open import Derivationality
open import Functor2.Core
open import Functor2.Product
open import Functor2.InclusionPreserving.Core
open import Functor2.InclusionPreserving.Product
open import Inclusiveness.Converse
open import Inclusiveness.Core
open import Inclusiveness.SigmaClosure
open import Inclusiveness.Negation
open import Inclusiveness.Product
open import Logic2
open import TreeIndex

module InclusivenessAndDerivationality where

<-derived : DerivationalRelation
<-derived = derivedRelation _<_ R p
  where R : Deriver
        R = deriver ⊥
                    (λ _ → ⊤)
                    (λ _ → ⊥)
                    (λ _ → ⊤)
                    (λ _ → ⊥)
                    (λ _ _ → ⊥)
                    (λ _ _ → ⊥)
        
        p : (t : TreeShape) → _<_ {t} ⇔′ Deriver._~~_ R {t}
        p leaf = fwd , bwd
          where fwd : _<_ {leaf} ⇒′ Deriver._~~_ R {leaf}
                fwd root root ()
                
                bwd : Deriver._~~_ R {leaf} ⇒′ _<_ {leaf}
                bwd root root ()
        
        p (branch l r) = fwd , bwd
          where fwd : _<_ {branch l r} ⇒′ Deriver._~~_ R {branch l r}
                fwd root root ()
                fwd root (left y) x<y = tt
                fwd root (right y) x<y = tt
                fwd (left x) root ()
                fwd (left x) (left y) (<-su-l x<y) = proj₁ (p l) x y x<y
                fwd (left x) (right y) ()
                fwd (right x) root ()
                fwd (right x) (left y) ()
                fwd (right x) (right y) (<-su-r x<y) = proj₁ (p r) x y x<y
                
                bwd : Deriver._~~_ R {branch l r} ⇒′ _<_ {branch l r}
                bwd root root ()
                bwd root (left y) x~y = <-ze-l
                bwd root (right y) x~y = <-ze-r
                bwd (left x) root ()
                bwd (left x) (left y) x~y = <-su-l (proj₂ (p l) x y x~y)
                bwd (left x) (right y) ()
                bwd (right x) root ()
                bwd (right x) (left y) ()
                bwd (right x) (right y) x~y = <-su-r (proj₂ (p r) x y x~y)

