open import Data.Product
open import Function

open import Syntax.Derivationality
open import Syntax.Inclusiveness.Core
open import Syntax.Logic
open import Syntax.TreeIndex

module Syntax.Inclusiveness.Converse where



_ºº : InclusiveDerivationalRelation
    → InclusiveDerivationalRelation
_ºº (derivationalRelation (derivedRelation p indP proofP) isIncP)
  = derivationalRelation (derivedRelation (λ {t} → (p {t}) º) R proofR) isIncR
  where R : Deriver
        R = deriver (Deriver.rt~rt indP)
                    (λ {t} → Deriver.l~rt indP {t})
                    (λ {t} → Deriver.rt~l indP {t})
                    (λ {t} → Deriver.r~rt indP {t})
                    (λ {t} → Deriver.rt~r indP {t})
                    (λ {t} {t'} → Deriver.r~l indP {t'} {t} º)
                    (λ {t} {t'} → Deriver.l~r indP {t'} {t} º)
        
        proofR : (t : TreeShape) → (p {t}) º ⇔′ Deriver._~~_ R {t}
        proofR leaf = fwd , bwd
          where fwd : (p {leaf}) º ⇒′ Deriver._~~_ R {leaf}
                fwd root root = proj₁ (proofP leaf) root root
                
                bwd : Deriver._~~_ R {leaf} ⇒′ (p {leaf}) º
                bwd root root = proj₂ (proofP leaf) root root
        
        proofR (branch l r) = fwd , bwd
          where fwd : (p {branch l r}) º ⇒′ Deriver._~~_ R {branch l r}
                fwd root root = proj₁ (proofP (branch l r)) root root
                fwd root (left y) = proj₁ (proofP (branch l r)) (left y) root
                fwd root (right y) = proj₁ (proofP (branch l r)) (right y) root
                fwd (left x) root = proj₁ (proofP (branch l r)) root (left x)
                fwd (left x) (left y) = proj₁ (proofR l) x y ∘ proj₂ (proj₁ isIncP l r) y x
                fwd (left x) (right y) = proj₁ (proofP (branch l r)) (right y) (left x)
                fwd (right x) root = proj₁ (proofP (branch l r)) root (right x)
                fwd (right x) (left y) = proj₁ (proofP (branch l r)) (left y) (right x)
                fwd (right x) (right y) = proj₁ (proofR r) x y ∘ proj₂ (proj₂ isIncP l r) y x
                
                bwd : Deriver._~~_ R {branch l r} ⇒′ (p {branch l r}) º
                bwd root root = proj₂ (proofP (branch l r)) root root
                bwd root (left y) = proj₂ (proofP (branch l r)) (left y) root
                bwd root (right y) = proj₂ (proofP (branch l r)) (right y) root
                bwd (left x) root = proj₂ (proofP (branch l r)) root (left x)
                bwd (left x) (left y) = proj₁ (proj₁ isIncP l r) y x ∘ proj₂ (proofR l) x y
                bwd (left x) (right y) = proj₂ (proofP (branch l r)) (right y) (left x)
                bwd (right x) root = proj₂ (proofP (branch l r)) root (right x)
                bwd (right x) (left y) = proj₂ (proofP (branch l r)) (left y) (right x)
                bwd (right x) (right y) = proj₁ (proj₂ isIncP l r) y x ∘ proj₂ (proofR r) x y
        
        isIncR : IsInclusiveRelation (λ {t} → (p {t}) º)
        isIncR = (λ l r → (λ x y → proj₁ (proj₁ isIncP l r) y x) ,
                          (λ x y → proj₂ (proj₁ isIncP l r) y x)) ,
                 (λ l r → (λ x y → proj₁ (proj₂ isIncP l r) y x) ,
                          (λ x y → proj₂ (proj₂ isIncP l r) y x))