open import Data.Product
open import Function
open import Relation.Nullary
open import Relation.Unary

open import Syntax.Derivationality
open import Syntax.Inclusiveness.Core
open import Syntax.Logic
open import Syntax.TreeIndex

module Syntax.Inclusiveness.Negation where



¬¬_ : InclusiveDerivationalRelation
    → InclusiveDerivationalRelation
¬¬ (derivationalRelation (derivedRelation p indP proofP) isIncP)
  = derivationalRelation (derivedRelation (λ {t} → ∁₂ (p {t})) R proofR) isIncR
  where R : Deriver
        R = deriver (¬ Deriver.rt~rt indP)
                    (λ {t} → ∁ (Deriver.rt~l indP {t}))
                    (λ {t} → ∁ (Deriver.l~rt indP {t}))
                    (λ {t} → ∁ (Deriver.rt~r indP {t}))
                    (λ {t} → ∁ (Deriver.r~rt indP {t}))
                    (λ {t} {t'} → ∁₂ (Deriver.l~r indP {t} {t'}))
                    (λ {t} {t'} → ∁₂ (Deriver.r~l indP {t} {t'}))
        
        proofR : (t : TreeShape) → ∁₂ (p {t}) ⇔′ Deriver._~~_ R {t}
        proofR leaf = fwd , bwd
          where fwd : ∁₂ (p {leaf}) ⇒′ Deriver._~~_ R {leaf}
                fwd root root ¬p = ¬p ∘ proj₂ (proofP leaf) root root
                
                bwd : Deriver._~~_ R {leaf} ⇒′ ∁₂ (p {leaf})
                bwd root root ¬rt~rt-ind = ¬rt~rt-ind ∘ proj₁ (proofP leaf) root root
                
        proofR (branch l r) = fwd , bwd
          where fwd : ∁₂ (p {branch l r}) ⇒′ Deriver._~~_ R {branch l r}
                fwd root root ¬p = ¬p ∘ proj₂ (proofP (branch l r)) root root
                fwd root (left y) ¬p = ¬p ∘ proj₂ (proofP (branch l r)) root (left y)
                fwd root (right y) ¬p = ¬p ∘ proj₂ (proofP (branch l r)) root (right y)
                fwd (left x) root ¬p = ¬p ∘ proj₂ (proofP (branch l r)) (left x) root
                fwd (left x) (left y) ¬p = proj₁ (proofR l) x y (¬p ∘ proj₁ (proj₁ isIncP l r) x y)
                fwd (left x) (right y) ¬p = ¬p ∘ proj₂ (proofP (branch l r)) (left x) (right y)
                fwd (right x) root ¬p = ¬p ∘ proj₂ (proofP (branch l r)) (right x) root
                fwd (right x) (left y) ¬p = ¬p ∘ proj₂ (proofP (branch l r)) (right x) (left y)
                fwd (right x) (right y) ¬p = proj₁ (proofR r) x y (¬p ∘ proj₁ (proj₂ isIncP l r) x y)
                
                bwd : Deriver._~~_ R {branch l r} ⇒′ ∁₂ (p {branch l r})
                bwd root root ¬x~y-ind = ¬x~y-ind ∘ proj₁ (proofP (branch l r)) root root
                bwd root (left y) ¬x~y-ind = ¬x~y-ind ∘ proj₁ (proofP (branch l r)) root (left y)
                bwd root (right y) ¬x~y-ind = ¬x~y-ind ∘ proj₁ (proofP (branch l r)) root (right y)
                bwd (left x) root ¬x~y-ind = ¬x~y-ind ∘ proj₁ (proofP (branch l r)) (left x) root
                bwd (left x) (left y) ¬x~y-ind = proj₂ (proofR l) x y ¬x~y-ind ∘ proj₂ (proj₁ isIncP l r) x y
                bwd (left x) (right y) ¬x~y-ind = ¬x~y-ind ∘ proj₁ (proofP (branch l r)) (left x) (right y)
                bwd (right x) root ¬x~y-ind = ¬x~y-ind ∘ proj₁ (proofP (branch l r)) (right x) root
                bwd (right x) (left y) ¬x~y-ind = ¬x~y-ind ∘ proj₁ (proofP (branch l r)) (right x) (left y)
                bwd (right x) (right y) ¬x~y-ind = proj₂ (proofR r) x y ¬x~y-ind ∘ proj₂ (proj₂ isIncP l r) x y
                
        isIncR : IsInclusiveRelation (λ {t} → ∁₂ (p {t}))
        isIncR = (λ l r → (λ x y ¬p → ¬p ∘ proj₂ (proj₁ isIncP l r) x y) ,
                          (λ x y ¬x~y-ind → ¬x~y-ind ∘ proj₁ (proj₁ isIncP l r) x y)) ,
                 (λ l r → (λ x y ¬p → ¬p ∘ proj₂ (proj₂ isIncP l r) x y) ,
                          (λ x y ¬x~y-ind → ¬x~y-ind ∘ proj₁ (proj₂ isIncP l r) x y))