open import Data.Product
open import Data.Sum
open import Function

open import Syntax.Derivationality
open import Syntax.Functor2.Core
open import Syntax.Functor2.InclusionPreserving.Core
open import Syntax.Inclusiveness.Core
open import Syntax.Logic
open import Syntax.TreeIndex

module Syntax.Inclusiveness.SigmaClosure where



Σ// : InclusionPreservingBifunctor
    → InclusiveDerivationalRelation
    → InclusiveDerivationalRelation
    → InclusiveDerivationalRelation
Σ// (inclusionPreservingBifunctor (bifunctor _*_ fmap isBifunctor) isIncPres)
    (derivationalRelation (derivedRelation p indP proofP) isIncP)
    (derivationalRelation (derivedRelation q indQ proofQ) isIncQ)
  = derivationalRelation (derivedRelation (λ {t} → Σ/ _*_ (p {t}) (q {t})) R proofR) isIncR
  where R : Deriver
        R = deriver ((Deriver.rt~rt indP * Deriver.rt~rt indQ) ⊎
                     (Σ[ t ∶ TreeShape ] Σ[ z ∶ TreeIndex t ]
                       Deriver.l~rt indP {t} z * Deriver.l~rt indQ {t} z) ⊎
                     (Σ[ t ∶ TreeShape ] Σ[ z ∶ TreeIndex t ]
                       Deriver.r~rt indP {t} z * Deriver.r~rt indQ {t} z))
                    (λ {t} → Deriver.rt~l indP {t} -⟨ _*_ ⟩- Deriver.rt~l indQ {t})
                    (λ {t} → Deriver.l~rt indP {t} -⟨ _*_ ⟩- Deriver.l~rt indQ {t})
                    (λ {t} → Deriver.rt~r indP {t} -⟨ _*_ ⟩- Deriver.rt~r indQ {t})
                    (λ {t} → Deriver.r~rt indP {t} -⟨ _*_ ⟩- Deriver.r~rt indQ {t})
                    (λ {t} {t'} → Deriver.l~r indP {t} {t'} -[ _*_ ]- Deriver.l~r indQ {t} {t'})
                    (λ {t} {t'} → Deriver.r~l indP {t} {t'} -[ _*_ ]- Deriver.r~l indQ {t} {t'})
          
        proofR : (t : TreeShape) → Σ/ _*_ (p {t}) (q {t}) ⇔′ Deriver._~~_ R {t}
        proofR leaf = {!!}
          where fwd : Σ/ _*_ (p {leaf}) (q {leaf}) ⇒′ Deriver._~~_ R {leaf}
                fwd root root (root , b) = inj₁ (fmap (proj₁ (proofP leaf) root root)
                                                      (proj₁ (proofQ leaf) root root)
                                                      b)
                
                bwd : Deriver._~~_ R {leaf} ⇒′ Σ/ _*_ (p {leaf}) (q {leaf})
                bwd root root (inj₁ x) = root , fmap (proj₂ (proofP leaf) root root)
                                                     (proj₂ (proofQ leaf) root root)
                                                     x
                bwd root root (inj₂ (inj₁ (leaf , b))) = root , {!!}
                bwd root root (inj₂ (inj₁ (branch l r , x₁ , y))) = root , {!!}
                bwd root root (inj₂ (inj₂ x)) = {!!}
        
        proofR (branch l r) = {!!}
        
        isIncR : IsInclusiveRelation (λ {t} → Σ/ _*_ (p {t}) (q {t}))
               {-
                 ((l r : TreeShape) → _~_ ⇒′ (_~_ on left {l} {r})
                                    × (_~_ on left {l} {r}) ⇒′ _~_)
               × ((l r : TreeShape) → _~_ ⇒′ (_~_ on right {l} {r})
                                    × (_~_ on right {l} {r}) ⇒′ _~_)
               -}
        
        isIncR = isIncRLeft , {!!}
          where isIncRLeft : (l r : TreeShape)
                           → Σ/ _*_ (p {l}) (q {l}) ⇔′ (Σ/ _*_ (p {branch l r}) (q {branch l r}) on left {l} {r})
                isIncRLeft l r = fwd , {!!}
                  where fwd : Σ/ _*_ (p {l}) (q {l}) ⇒′ (Σ/ _*_ (p {branch l r}) (q {branch l r}) on left {l} {r})
                        fwd x y (a , b) = left a ,
                                             proj₁ (proj₁ isIncPres l r l r
                                                          (inclusiveRelation p isIncP)
                                                          (inclusiveRelation q isIncQ)
                                                          a x a y)
                                                   b
                        bwd : (Σ/ _*_ (p {branch l r}) (q {branch l r}) on left {l} {r}) ⇒′ Σ/ _*_ (p {l}) (q {l})
                        bwd x y (root , b) = {!!}
                        bwd x y (left a , b) = a , proj₂ (proj₁ isIncPres l r l r
                                                               (inclusiveRelation p isIncP)
                                                               (inclusiveRelation q isIncQ)
                                                               a x a y) b
                        bwd x y (right a , b) with proj₂ isIncPres l r l r
                                                         (inclusiveRelation p isIncP)
                                                         (inclusiveRelation q isIncQ)
                        ... | ff = {!!}