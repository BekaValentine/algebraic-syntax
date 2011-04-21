{-# OPTIONS --universe-polymorphism #-}

open import Naturals
open import Functions
open import Logic
open import Relations
open import Structures
open import InclusivenessAndDerivationality
open import CCommandLemmas
open import TreeProjection

module CCommand where



cc-comb : ∀ {ℓ}
          → (sdt0 : SingleDominanceTree ℓ)
          → (_cc_ : Rel (SingleDominanceTree.carrier sdt0) ℓ)
          → (p0 : IsCCommandRel sdt0 _cc_)
          → (sdt1 : SingleDominanceTree ℓ)
          → (_cc′_ : Rel (SingleDominanceTree.carrier sdt1) ℓ)
          → (p1 : IsCCommandRel sdt1 _cc′_)
          → Rel (SingleDominanceTree.carrier (sdt0 ↑ sdt1)) ℓ
cc-comb {ℓ} (sdtree X r0 _<_ t0 sd0) _cc_ p0 (sdtree Y r1 _<′_ t1 sd1) _cc′_ p1 = _cc′′_
  where sdt2 = sdtree X r0 _<_ t0 sd0 ↑ sdtree Y r1 _<′_ t1 sd1
        open SingleDominanceTree sdt2 using () renaming (_<_ to _<′′_ ; isTree to t2)
        
        rt0 : Rooted r0 _<_
        rt0 = snd (snd (snd t0))
        
        rootedness : (∀ {x : X}
                      → x == r0 ↔
                        imdom (sd-underlying-tree sdt2) (inl *) (inr (inl x))) ∧
                     (∀ {y : Y}
                      → y == r1 ↔
                        imdom (sd-underlying-tree sdt2) (inl *) (inr (inr y)))
        rootedness = lem-↑-root (sdtree X r0 _<_ t0 sd0) (sdtree Y r1 _<′_ t1 sd1)
        
        _cc′′_ : Rel (One + X + Y) ℓ
        inl * cc′′ inl * = ⊥
        inl * cc′′ inr (inl y) = ⊥
        inl * cc′′ inr (inr y) = ⊥
        inr (inl x) cc′′ inl * = ⊥
        inr (inl x) cc′′ inr (inl y) = x cc y
        inr (inl x) cc′′ inr (inr y) = {!!}
        inr (inr x) cc′′ inl * = {!!}
        inr (inr x) cc′′ inr (inl y) = {!!}
        inr (inr x) cc′′ inr (inr y) = {!!}
        
        p2 : IsCCommandRel sdt2 _cc′′_
        p2 {inl *} {inl *} = (f , g)
          where g : ¬ (inl * == inl *) ∧
                    ¬ (inl * <′′ inl *) ∧
                    ¬ (inl * <′′ inl *) ∧
                    ∃ (One + X + Y) (λ z → imdom (tree (One + X + Y) (inl *) _<′′_ t2) z (inl *) ∧ (z <′′ inl *))
                    → inl * cc′′ inl *
                g (_ , _ , _ , exists (inl *) (_ , ()))
                g (_ , _ , _ , exists (inr _) (_ , ()))
                
                f : inl * cc′′ inl *
                    → ¬ (inl * == inl *) ∧ 
                      ¬ (inl * <′′ inl *) ∧
                      ¬ (inl * <′′ inl *) ∧
                      ∃ (One + X + Y) (λ z → imdom (tree (One + X + Y) (inl *) _<′′_ t2) z (inl *) ∧ (z <′′ inl *))
                f ()
        
        p2 {inl *} {inr (inl y)} = (f , g)
          where g : ¬ (inl * == inr (inl y)) ∧
                    ¬ (inl * <′′ inr (inl y)) ∧
                    ¬ (inr (inl y) <′′ inl *) ∧
                    ∃ (One + X + Y) (λ z → imdom (tree (One + X + Y) (inl *) _<′′_ t2) z (inl *) ∧ (z <′′ inr (inl y)))
                    → inl * cc′′ inr (inl y)
                g (_ , _ , _ , exists (inl *) ((_ , () , _) , _))
                g (_ , _ , _ , exists (inr (inl _)) ((_ , () , _) , _))
                g (_ , _ , _ , exists (inr (inr _)) (_ , ()))
                
                f : inl * cc′′ inr (inl y)
                    → ¬ (inl * == inr (inl y)) ∧ 
                      ¬ (inl * <′′ inr (inl y)) ∧
                      ¬ (inr (inl y) <′′ inl *) ∧
                      ∃ (One + X + Y) (λ z → imdom (tree (One + X + Y) (inl *) _<′′_ t2) z (inl *) ∧ (z <′′ inr (inl y)))
                f ()
                
        p2 {inl *} {inr (inr y)} = (f , g)
          where g : ¬ (inl * == inr (inr y)) ∧
                    ¬ (inl * <′′ inr (inr y)) ∧
                    ¬ (inr (inr y) <′′ inl *) ∧
                    ∃ (One + X + Y) (λ z → imdom (tree (One + X + Y) (inl *) _<′′_ t2) z (inl *) ∧ (z <′′ inr (inr y)))
                    → inl * cc′′ inr (inr y)
                g (_ , _ , _ , exists (inl *) ((_ , () , _) , _))
                g (_ , _ , _ , exists (inr _) ((_ , () , _) , _))
                
                f : inl * cc′′ inr (inr y)
                    → ¬ (inl * == inr (inr y)) ∧ 
                      ¬ (inl * <′′ inr (inr y)) ∧
                      ¬ (inr (inr y) <′′ inl *) ∧
                      ∃ (One + X + Y) (λ z → imdom (tree (One + X + Y) (inl *) _<′′_ t2) z (inl *) ∧ (z <′′ inr (inr y)))
                f ()

        p2 {inr (inl x)} {inl *} = (f , g)
          where g : ¬ (inr (inl x) == inl *) ∧
                    ¬ (inr (inl x) <′′ inl *) ∧
                    ¬ (inl * <′′ inr (inl x)) ∧
                    ∃ (One + X + Y) (λ z → imdom (tree (One + X + Y) (inl *) _<′′_ t2) z (inr (inl x)) ∧ (z <′′ inl *))
                    → inr (inl x) cc′′ inl *
                g (_ , _ , _ , exists (inl *) (_ , ()))
                g (_ , _ , _ , exists (inr _) (_ , ()))
                
                f : inr (inl x) cc′′ inl *
                    → ¬ (inr (inl x) == inl *) ∧
                      ¬ (inr (inl x) <′′ inl *) ∧
                      ¬ (inl * <′′ inr (inl x)) ∧
                      ∃ (One + X + Y) (λ z → imdom (tree (One + X + Y) (inl *) _<′′_ t2) z (inr (inl x)) ∧ (z <′′ inl *))
                f ()
        
        p2 {inr (inl x)} {inr (inl y)} = ({!!} , g)
          where g : ¬ (inr (inl x) == inr (inl y)) ∧
                    ¬ (inr (inl x) <′′ inr (inl y)) ∧
                    ¬ (inr (inl y) <′′ inr (inl x)) ∧
                    ∃ (One + X + Y) (λ z → imdom (tree (One + X + Y) (inl *) _<′′_ t2) z (inr (inl x)) ∧ (z <′′ inr (inl y)))
                    → inr (inl x) cc′′ inr (inl y)
                g (neq , a , b , exists (inl *) ((c , d , e) , f)) with snd (fst rootedness {x})
                                                                            (uneq-+-inl-inr , tt , λ {z} → e {z})
                ... | x==r0 with rt0 {y}
                g (neq , a , b , exists (inl *) ((c , d , e) , f)) | x==r0 | inl r0==y with neq (cong (inr ∘ inl) (trans-== x==r0 r0==y))
                ... | ()
                g (neq , a , b , exists (inl *) ((c , d , e) , f)) | x==r0 | inr r0<y with a (subst-== {F = λ r0 → r0 < y} r0 x (comm-== x==r0) r0<y)
                ... | ()
                g (neq , a , b , exists (inr (inl z)) ((c , d , e) , f)) = snd (p0 {x} {y}) (neq ∘′ cong inr ∘′ cong inl ,
                                                                                             a , b ,
                                                                                             exists z ((c ∘′ cong inr ∘′ cong inl ,
                                                                                                        d ,
                                                                                                        λ {z'} → e {inr (inl z')}) ,
                                                                                                       f))
                g (_ , _ , _ , exists (inr (inr _)) ((_ , () , _) , _))

        
        p2 {inr (inl x)} {inr (inr y)} = {!!}
        p2 {inr (inr x)} {inl *} = {!!}
        p2 {inr (inr x)} {inr (inl y)} = {!!}
        p2 {inr (inr x)} {inr (inr y)} = {!!}


{-

_cc′′_ : (x y : car) → ∃ (Set ℓ) (λ xccy → xccy ↔
                       ¬(x <′′ y) ∧
                       ¬(y <′′ x) ∧
                       ∃ car (λ z → imdom (tree car _<′′_ t2) z x ∧ z <′′ y))



(inr (inl x)) cc′′ (inr (inr y)) = exists w ({!!} , g)
  where w : Set ℓ
        w = {!!}
        
        g : ¬(inr (inl x) <′′ inr (inr y)) ∧
            ¬(inr (inr y) <′′ inr (inl x)) ∧
            ∃ car (λ z → imdom (tree car _<′′_ t2) z (inr (inl x)) ∧ (z <′′ inr (inr y)))
            → w
        g (a , b , exists (inl *) d) = {!!}
        g (_ , _ , exists (inr (inl _)) (_ , ()))
        g (_ , _ , exists (inr (inr _)) ((_ , () , _) , _))

(inr (inr x)) cc′′ (inl *) = exists ⊥ (f , g)
  where g : ¬(inr (inr x) <′′ inl *) ∧
            ¬(inl * <′′ inr (inr x)) ∧
            ∃ car (λ z → imdom (tree car _<′′_ t2) z (inr (inr x)) ∧ (z <′′ inl *))
            → ⊥
        g (_ , _ , exists (inl *) (_ , ()))
        g (_ , _ , exists (inr _) (_ , ()))
        
        f : ⊥ → ¬(inr (inr x) <′′ inl *) ∧
                 ¬(inl * <′′ inr (inr x)) ∧
                 ∃ car (λ z → imdom (tree car _<′′_ t2) z (inr (inr x)) ∧ (z <′′ inl *))
        f ()

(inr (inr x)) cc′′ (inr (inl y)) = exists w ({!!} , g)
  where w : Set ℓ
        w = {!!}
        
        g : ¬(inr (inr x) <′′ inr (inl y)) ∧
            ¬(inr (inl y) <′′ inr (inr x)) ∧
            ∃ car (λ z → imdom (tree car _<′′_ t2) z (inr (inr x)) ∧ z <′′ (inr (inl y)))
            → w
        g (a , b , exists (inl *) d) = {!!}
        g (_ , _ , exists (inr (inl _)) ((_ , () , _) , _))
        g (_ , _ , exists (inr (inr _)) (_ , ()))

(inr (inr x)) cc′′ (inr (inr y)) = exists w ({!!} , g)
  where w : Set ℓ
        w = {!!}
        
        g : ¬(inr (inr x) <′′ inr (inr y)) ∧
                  ¬(inr (inr y) <′′ inr (inr x)) ∧
            ∃ car (λ z → imdom (tree car _<′′_ t2) z (inr (inr x)) ∧ z <′′ (inr (inr y)))
            → w
        g (a , b , exists (inl *) d) = {!!}
        g (a , b , exists (inr (inl z)) (_ , ()))
        g (a , b , exists (inr (inr z)) d) = {!!}
-}