open import Data.Product
open import Data.Sum
open import Data.Unit
open import Function

open import Syntax.Derivationality
open import Functor2.Core
open import Functor2.InclusionPreserving.Core
open import Syntax.Inclusiveness.Core
open import Syntax.Logic
open import Syntax.TreeIndex

module Syntax.Inclusiveness.SigmaClosure where



Σ// : Bifunctor
    → InclusiveDerivationalRelation
    → InclusiveDerivationalRelation
    → InclusiveDerivationalRelation
Σ// (bifunctor _*_ fmap isBifunctor)
    (inclusiveDerivationalRelation (derivationalRelation p indP isDerP) isIncP)
    (inclusiveDerivationalRelation (derivationalRelation q indQ isDerQ) isIncQ)
  = inclusiveDerivationalRelation (derivationalRelation (λ {t} → Σ/ _*_ (p {t}) (q {t})) R isDerR) isIncR
  where R : Deriver
        R = deriver -- new rt~rt
                    ((Deriver.rt~rt indP * Deriver.rt~rt indQ) ⊎
                      (Σ[ t ∶ TreeShape ] Σ[ z ∶ TreeIndex t ] Deriver.l~rt indP z * Deriver.l~rt indQ z) ⊎
                      (Σ[ t ∶ TreeShape ] Σ[ z ∶ TreeIndex t ] Deriver.r~rt indP z * Deriver.r~rt indQ z))
                    -- new rt~l
                    (λ {t} x → (Deriver.rt~rt indP * Deriver.rt~l indQ x) ⊎
                               (Σ[ z ∶ TreeIndex t ] Deriver.l~rt indP z * Deriver._~~_ indQ z x) ⊎
                               (Σ[ t' ∶ TreeShape ] Σ[ z ∶ TreeIndex t' ] Deriver.r~rt indP z * Deriver.r~l indQ z x))
                    -- new l~rt
                    (λ {t} x → (Deriver.rt~l indP x * Deriver.rt~rt indQ) ⊎ -- rt0~l * rt0~rt
                               (Σ[ z ∶ TreeIndex t ] Deriver._~~_ indP z x * Deriver.l~rt indQ z) ⊎ -- l0~l * l0~rt
                               (Σ[ t' ∶ TreeShape ] Σ[ z ∶ TreeIndex t' ] Deriver.r~l indP z x * Deriver.r~rt indQ z )) -- r0~l * r0~rt
                    -- new rt~r
                    (λ {t} x → (Deriver.rt~rt indP * Deriver.rt~r indQ x) ⊎ -- rt0~rt * rt0~r
                               (Σ[ t' ∶ TreeShape ] Σ[ z ∶ TreeIndex t' ] Deriver.l~rt indP z * Deriver.l~r indQ z x) ⊎ -- l0~rt * l0~r
                               (Σ[ z ∶ TreeIndex t ] Deriver.r~rt indP z * Deriver._~~_ indQ z x)) -- r0~rt * r0~r
                    -- new r~rt
                    (λ {t} x → (Deriver.rt~r indP x * Deriver.rt~rt indQ) ⊎ -- rt0~r * rt0~rt
                               (Σ[ t' ∶ TreeShape ] Σ[ z ∶ TreeIndex t' ] Deriver.l~r indP z x * Deriver.l~rt indQ z) ⊎ -- l0~r * l0~rt
                               (Σ[ z ∶ TreeIndex t ] Deriver._~~_ indP z x * Deriver.r~rt indQ z)) -- r0~r * r0~rt
                    -- new l~r
                    (λ {t} {t'} x y
                      → (Deriver.rt~l indP x * Deriver.rt~r indQ y) ⊎ -- rt0~l * rt0~r
                        (Σ[ z ∶ TreeIndex t ] Deriver._~~_ indP z x * Deriver.l~r indQ z y) ⊎ -- l0~l * l0~r
                        (Σ[ z ∶ TreeIndex t' ] Deriver.r~l indP z x * Deriver._~~_ indQ z y)) -- r0~l * r0~r
                    -- new r~l
                    (λ {t} {t'} x y
                      → (Deriver.rt~r indP x * Deriver.rt~l indQ y) ⊎ -- rt0~r * rt0~l
                        (Σ[ z ∶ TreeIndex t' ] Deriver.l~r indP z x * Deriver._~~_ indQ z y) ⊎ -- l0~r * l0~l
                        (Σ[ z ∶ TreeIndex t ] Deriver._~~_ indP z x * Deriver.r~l indQ z y)) -- r0~r * r0~l)
          
        isDerR : (t : TreeShape) → Σ/ _*_ (p {t}) (q {t}) ⇔′ Deriver._~~_ R {t}
        isDerR t = {!!}
          where fwd : Σ/ _*_ (p {t}) (q {t}) ⇒′ Deriver._~~_ R {t}
                fwd x y (a , b) with t
                fwd root root (root , b) | leaf = inj₁ (fmap (proj₁ (isDerP leaf) root root)
                                                             (proj₁ (isDerQ leaf) root root)
                                                             b)
                fwd root root (root , b) | branch l r = inj₁ (fmap (proj₁ (isDerP (branch l r)) root root)
                                                                   (proj₁ (isDerQ (branch l r)) root root)
                                                                   b)
                fwd root root (left z , b) | branch l r = inj₂ (inj₁ (l , z ,
                                                               fmap (proj₁ (isDerP (branch l r)) (left z) root)
                                                                    (proj₁ (isDerQ (branch l r)) (left z) root)
                                                                    b))
                fwd root root (right z , b) | branch l r = inj₂ (inj₂ (r , z ,
                                                                fmap (proj₁ (isDerP (branch l r)) (right z) root)
                                                                     (proj₁ (isDerQ (branch l r)) (right z) root)
                                                                     b))
                fwd root (left y) (root , b) | branch l r = inj₁ (fmap (proj₁ (isDerP (branch l r)) root root)
                                                                       (proj₁ (isDerQ (branch l r)) root (left y))
                                                                       b)
                fwd root (left y) (left z , b) | branch l r
                  = inj₂ (inj₁ (z , fmap (proj₁ (isDerP (branch l r)) (left z) root)
                                        (proj₁ (isDerQ (branch l r)) (left z) (left y))
                                        b))
                fwd root (left y) (right z , b) | branch l r
                  = inj₂ (inj₂ (r , z , fmap (proj₁ (isDerP (branch l r)) (right z) root)
                                            (proj₁ (isDerQ (branch l r)) (right z) (left y))
                                            b))
                fwd root (right y) (root , b) | branch l r = inj₁ (fmap (proj₁ (isDerP (branch l r)) root root)
                                                                        (proj₁ (isDerQ (branch l r)) root (right y))
                                                                        b)
                fwd root (right y) (left z , b) | branch l r
                  = inj₂ (inj₁ (l , z ,
                               fmap (proj₁ (isDerP (branch l r)) (left z) root)
                                    (proj₁ (isDerQ (branch l r)) (left z) (right y))
                                    b))
                fwd root (right y) (right z , b) | branch l r
                  = inj₂ (inj₂ (z , fmap (proj₁ (isDerP (branch l r)) (right z) root)
                                        (proj₁ (isDerQ (branch l r)) (right z) (right y))
                                        b))
                fwd (left x) root (root , b) | branch l r = inj₁ (fmap (proj₁ (isDerP (branch l r)) root (left x))
                                                                       (proj₁ (isDerQ (branch l r)) root root)
                                                                       b)
                fwd (left x) root (left z , b) | branch l r
                  = inj₂ (inj₁ (z , fmap (proj₁ (isDerP (branch l r)) (left z) (left x))
                                        (proj₁ (isDerQ (branch l r)) (left z) root)
                                        b))
                fwd (left x) root (right z , b) | branch l r
                  = inj₂ (inj₂ (r , z , fmap (proj₁ (isDerP (branch l r)) (right z) (left x))
                                            (proj₁ (isDerQ (branch l r)) (right z) root)
                                            b))
                fwd (left x) (left y) (root , b) | branch l r = proj₁ (isDerR l) x y {!!}
                fwd (left x) (left y) (left z , b) | branch l r
                  = proj₁ (isDerR l) x y (z , fmap (proj₂ (proj₁ isIncP l r) z x)
                                                   (proj₂ (proj₁ isIncQ l r) z y)
                                                   b)
                fwd (left x) (left y) (right z , b) | branch l r = proj₁ (isDerR l) x y {!!}
                fwd (left x) (right y) (root , b) | branch l r
                  = inj₁ (fmap (proj₁ (isDerP (branch l r)) root (left x))
                               (proj₁ (isDerQ (branch l r)) root (right y))
                               b)
                fwd (left x) (right y) (left z , b) | branch l r
                  = inj₂ (inj₁ (z , fmap (proj₁ (isDerP (branch l r)) (left z) (left x))
                                        (proj₁ (isDerQ (branch l r)) (left z) (right y))
                                        b))
                fwd (left x) (right y) (right z , b) | branch l r
                  = inj₂ (inj₂ (z , fmap (proj₁ (isDerP (branch l r)) (right z) (left x))
                                        (proj₁ (isDerQ (branch l r)) (right z) (right y))
                                        b))
                fwd (right x) root (root , b) | branch l r = inj₁ (fmap (proj₁ (isDerP (branch l r)) root (right x))
                                                                        (proj₁ (isDerQ (branch l r)) root root)
                                                                        b)
                fwd (right x) root (left z , b) | branch l r
                  = inj₂ (inj₁ (l , z , fmap (proj₁ (isDerP (branch l r)) (left z) (right x))
                                            (proj₁ (isDerQ (branch l r)) (left z) root)
                                            b))
                fwd (right x) root (right z , b) | branch l r
                  = inj₂ (inj₂ (z , fmap (proj₁ (isDerP (branch l r)) (right z) (right x))
                                        (proj₁ (isDerQ (branch l r)) (right z) root)
                                        b))
                fwd (right x) (left y) (root , b) | branch l r = inj₁ (fmap (proj₁ (isDerP (branch l r)) root (right x))
                                                                            (proj₁ (isDerQ (branch l r)) root (left y))
                                                                            b)
                fwd (right x) (left y) (left z , b) | branch l r
                  = inj₂ (inj₁ (z , fmap (proj₁ (isDerP (branch l r)) (left z) (right x))
                                        (proj₁ (isDerQ (branch l r)) (left z) (left y))
                                        b))
                fwd (right x) (left y) (right z , b) | branch l r
                  = inj₂ (inj₂ (z , fmap (proj₁ (isDerP (branch l r)) (right z) (right x))
                                        (proj₁ (isDerQ (branch l r)) (right z) (left y))
                                        b))
                fwd (right x) (right y) (root , b) | branch l r = {!!}
                fwd (right x) (right y) (left z , b) | branch l r = {!!}
                fwd (right x) (right y) (right z , b) | branch l r
                  = proj₁ (isDerR r) x y (z , fmap (proj₂ (proj₂ isIncP l r) z x)
                                                   (proj₂ (proj₂ isIncQ l r) z y)
                                                   b)
        
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
                        fwd x y (a , b) = left a , fmap (proj₁ (proj₁ isIncP l r) a x)
                                                        (proj₁ (proj₁ isIncQ l r) a y)
                                                        b
                        bwd : (Σ/ _*_ (p {branch l r}) (q {branch l r}) on left {l} {r}) ⇒′ Σ/ _*_ (p {l}) (q {l})
                        bwd x y (root , b) = {!!}
                        bwd x y (left a , b) = a , proj₂ (proj₁ {!!} l r l r
                                                               (inclusiveRelation p isIncP)
                                                               (inclusiveRelation q isIncQ)
                                                               a x a y) b
                        bwd x y (right a , b) with proj₂ {!!} l r l r
                                                         (inclusiveRelation p isIncP)
                                                         (inclusiveRelation q isIncQ)
                        ... | ff = {!!}