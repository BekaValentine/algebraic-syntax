open import Data.Product
open import Relation.Unary

open import Syntax.Derivationality
open import Syntax.Inclusiveness.Core
open import Syntax.Logic
open import Syntax.TreeIndex

module Syntax.Inclusiveness.Product where



_-××-_ : InclusiveDerivationalRelation
       → InclusiveDerivationalRelation
       → InclusiveDerivationalRelation
(derivationalRelation (derivedRelation p indP proofP) isIncP)
  -××- (derivationalRelation (derivedRelation q indQ proofQ) isIncQ)
  = derivationalRelation (derivedRelation (λ {t} → p {t} -×- q {t}) R proofR) isIncR
  where R : Deriver
        R = deriver (Deriver.rt~rt indP × Deriver.rt~rt indQ)
                    (λ {t} → Deriver.rt~l indP {t} ∩ Deriver.rt~l indQ {t})
                    (λ {t} → Deriver.l~rt indP {t} ∩ Deriver.l~rt indQ {t})
                    (λ {t} → Deriver.rt~r indP {t} ∩ Deriver.rt~r indQ {t})
                    (λ {t} → Deriver.r~rt indP {t} ∩ Deriver.r~rt indQ {t})
                    (λ {t} {t'} → Deriver.l~r indP {t} {t'} -×- Deriver.l~r indQ {t} {t'})
                    (λ {t} {t'} → Deriver.r~l indP {t} {t'} -×- Deriver.r~l indQ {t} {t'})
        
        proofR : (t : TreeShape) → (p {t} -×- q {t}) ⇔′ Deriver._~~_ R {t}
        proofR leaf = fwd , bwd
          where fwd : (p {leaf} -×- q {leaf}) ⇒′ Deriver._~~_ R {leaf}
                fwd root root (a , b) = proj₁ (proofP leaf) root root a ,
                                        proj₁ (proofQ leaf) root root b
        
                bwd : Deriver._~~_ R {leaf} ⇒′ (p {leaf} -×- q {leaf})
                bwd root root (a , b) = proj₂ (proofP leaf) root root a ,
                                        proj₂ (proofQ leaf) root root b
                
        proofR (branch l r) = fwd , bwd
          where fwd : (p {branch l r} -×- q {branch l r}) ⇒′ Deriver._~~_ R {branch l r}
                fwd root root (a , b) = proj₁ (proofP (branch l r)) root root a ,
                                        proj₁ (proofQ (branch l r)) root root b
                fwd root (left y) (a , b) = proj₁ (proofP (branch l r)) root (left y) a ,
                                            proj₁ (proofQ (branch l r)) root (left y) b
                fwd root (right y) (a , b) = proj₁ (proofP (branch l r)) root (right y) a ,
                                             proj₁ (proofQ (branch l r)) root (right y) b
                fwd (left x) root (a , b) = proj₁ (proofP (branch l r)) (left x) root a ,
                                            proj₁ (proofQ (branch l r)) (left x) root b
                fwd (left x) (left y) (a , b) = proj₁ (proofR l) x y
                                                      (proj₂ (proj₁ isIncP l r) x y a ,
                                                       proj₂ (proj₁ isIncQ l r) x y b)
                fwd (left x) (right y) (a , b) = proj₁ (proofP (branch l r)) (left x) (right y) a ,
                                                 proj₁ (proofQ (branch l r)) (left x) (right y) b
                fwd (right x) root (a , b) = proj₁ (proofP (branch l r)) (right x) root a ,
                                             proj₁ (proofQ (branch l r)) (right x) root b
                fwd (right x) (left y) (a , b) = proj₁ (proofP (branch l r)) (right x) (left y) a ,
                                                 proj₁ (proofQ (branch l r)) (right x) (left y) b
                fwd (right x) (right y) (a , b) = proj₁ (proofR r) x y
                                                        (proj₂ (proj₂ isIncP l r) x y a ,
                                                         proj₂ (proj₂ isIncQ l r) x y b)
                
                bwd : Deriver._~~_ R {branch l r} ⇒′ (p {branch l r} -×- q {branch l r})
                bwd root root (a , b) = proj₂ (proofP (branch l r)) root root a ,
                                        proj₂ (proofQ (branch l r)) root root b
                bwd root (left y) (a , b) = proj₂ (proofP (branch l r)) root (left y) a ,
                                            proj₂ (proofQ (branch l r)) root (left y) b
                bwd root (right y) (a , b) = proj₂ (proofP (branch l r)) root (right y) a ,
                                             proj₂ (proofQ (branch l r)) root (right y) b
                bwd (left x) root (a , b) = proj₂ (proofP (branch l r)) (left x) root a ,
                                            proj₂ (proofQ (branch l r)) (left x) root b
                bwd (left x) (left y) rec = proj₁ (proj₁ isIncP l r) x y (proj₁ pq) ,
                                            proj₁ (proj₁ isIncQ l r) x y (proj₂ pq)
                  where pq : p x y × q x y
                        pq = proj₂ (proofR l) x y rec
                bwd (left x) (right y) (a , b) = proj₂ (proofP (branch l r)) (left x) (right y) a ,
                                                 proj₂ (proofQ (branch l r)) (left x) (right y) b
                bwd (right x) root (a , b) = proj₂ (proofP (branch l r)) (right x) root a ,
                                             proj₂ (proofQ (branch l r)) (right x) root b
                bwd (right x) (left y) (a , b) = proj₂ (proofP (branch l r)) (right x) (left y) a ,
                                                 proj₂ (proofQ (branch l r)) (right x) (left y) b
                bwd (right x) (right y) rec = proj₁ (proj₂ isIncP l r) x y (proj₁ pq) ,
                                              proj₁ (proj₂ isIncQ l r) x y (proj₂ pq)
                  where pq : p x y × q x y
                        pq = proj₂ (proofR r) x y rec
                
        isIncR : IsInclusiveRelation (λ {t} → p {t} -×- q {t})
        isIncR = (λ l r → (λ x y ab → proj₁ (proj₁ isIncP l r) x y (proj₁ ab) ,
                                      proj₁ (proj₁ isIncQ l r) x y (proj₂ ab)) ,
                          (λ x y ab → proj₂ (proj₁ isIncP l r) x y (proj₁ ab) ,
                                      proj₂ (proj₁ isIncQ l r) x y (proj₂ ab))) ,
                 (λ l r → (λ x y ab → proj₁ (proj₂ isIncP l r) x y (proj₁ ab) ,
                                      proj₁ (proj₂ isIncQ l r) x y (proj₂ ab)) ,
                           λ x y ab → proj₂ (proj₂ isIncP l r) x y (proj₁ ab) ,
                                      proj₂ (proj₂ isIncQ l r) x y (proj₂ ab))