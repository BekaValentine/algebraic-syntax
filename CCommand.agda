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
          → ∃ (Rel (SingleDominanceTree.carrier (sdt0 ↑ sdt1)) ℓ) (λ _cc′′_ → IsCCommandRel (sdt0 ↑ sdt1) _cc′′_)
cc-comb {ℓ} (sdtree X r0 _<_ t0 sd0) _cc_ p0 (sdtree Y r1 _<′_ t1 sd1) _cc′_ p1 = exists _cc′′_ (λ {x} {y} → p2 {x} {y})
  where sdt0 = sdtree X r0 _<_ t0 sd0
        sdt1 = sdtree Y r1 _<′_ t1 sd1
        sdt2 = sdt0 ↑ sdt1
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
        inl * cc′′ inl * = {!!} --⊥
        inl * cc′′ inr (inl y) = ⊥
        inl * cc′′ inr (inr y) = ⊥
        inr (inl x) cc′′ inl * = ⊥
        inr (inl x) cc′′ inr (inl y) = x cc y
        inr (inl x) cc′′ inr (inr y) = x == r0
        inr (inr x) cc′′ inl * = ⊥
        inr (inr x) cc′′ inr (inl y) = x == r1
        inr (inr x) cc′′ inr (inr y) = x cc′ y
        
        p2 : IsCCommandRel sdt2 _cc′′_
        p2 {inl *} {inl *} = (f , g)
          where g : ¬ (inl * == inl *) ∧
                    ¬ (inl * <′′ inl *) ∧
                    ¬ (inl * <′′ inl *) ∧
                    ∃ (One + X + Y) (λ z → imdom (tree (One + X + Y) (inl *) _<′′_ t2) z (inl *) ∧ (z <′′ inl *))
                    → inl * cc′′ inl *
                g = {!!} -- (_ , _ , _ , exists (inl *) (_ , ()))
                --g (_ , _ , _ , exists (inr _) (_ , ()))
                
                f : inl * cc′′ inl *
                    → ¬ (inl * == inl *) ∧ 
                      ¬ (inl * <′′ inl *) ∧
                      ¬ (inl * <′′ inl *) ∧
                      ∃ (One + X + Y) (λ z → imdom (tree (One + X + Y) (inl *) _<′′_ t2) z (inl *) ∧ (z <′′ inl *))
                f = {!!} --()
        
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
        
        p2 {inr (inl x)} {inr (inl y)} = (f , g)
          where f : inr (inl x) cc′′ inr (inl y)
                    → ¬ (inr (inl x) == inr (inl y)) ∧
                      ¬ (inr (inl x) <′′ inr (inl y)) ∧
                      ¬ (inr (inl y) <′′ inr (inl x)) ∧
                      ∃ (One + X + Y) (λ z → imdom (tree (One + X + Y) (inl *) _<′′_ t2) z (inr (inl x)) ∧ (z <′′ inr (inl y)))
                f rlxccrly with fst (p0 {x} {y}) rlxccrly
                f rlxccrly | (a , b , c , exists d ((e , f , g) , h)) = a ∘′ uncong-+-inr ∘′ uncong-+-inl ,
                                                                        b ,
                                                                        c ,
                                                                        exists (inr (inl d))
                                                                               ((e ∘′ uncong-+-inl ∘′ uncong-+-inr ,
                                                                                 f ,
                                                                                 λ {z} → f0 {z}) ,
                                                                                h)
                  where f0 : ∀ {z : One + X + Y}
                             → comb _<_ _<′_ (inr (inl d)) z × comb _<_ _<′_ z (inr (inl x))
                             → ⊥
                        f0 {inl *} (() , _)
                        f0 {inr (inl z)} a,b with g {z} a,b
                        f0 {inr (inl z)} a,b | ()
                        f0 {inr (inr z)} (() , ())
                
                g : ¬ (inr (inl x) == inr (inl y)) ∧
                    ¬ (inr (inl x) <′′ inr (inl y)) ∧
                    ¬ (inr (inl y) <′′ inr (inl x)) ∧
                    ∃ (One + X + Y) (λ z → imdom (tree (One + X + Y) (inl *) _<′′_ t2) z (inr (inl x)) ∧ (z <′′ inr (inl y)))
                    → inr (inl x) cc′′ inr (inl y)
                g (a , b , c , exists (inl *) ((d , e , f) , g')) with snd (fst (lem-↑-root sdt0 sdt1) {x}) (d , tt , λ {z} → f {z}) | snd (snd (snd t0)) {y}
                g (a , b , c , exists (inl *) ((d , e , f) , g')) | x==r0 | inl r0==y with a (cong inr (cong inl (trans-== x==r0 r0==y)))
                g (a , b , c , exists (inl *) ((d , e , f) , g')) | x==r0 | inl r0==y | ()
                g (a , b , c , exists (inl *) ((d , e , f) , g')) | x==r0 | inr r0<y with b (subst-== {F = λ x' → x' < y} r0 x (comm-== x==r0) r0<y)
                g (a , b , c , exists (inl *) ((d , e , f) , g')) | x==r0 | inr r0<y | ()
                g (a , b , c , exists (inr (inl z)) ((d , e , f) , g)) = snd (p0 {x} {y}) (a ∘′ cong inr ∘′ cong inl ,
                                                                                           b ,
                                                                                           c ,
                                                                                           exists z ((d ∘′ cong inr ∘′ cong inl ,
                                                                                                      e ,
                                                                                                      λ {z'} → f {inr (inl z')}) ,
                                                                                                     g))
                g (_ , _ , _ , exists (inr (inr _)) ((_ , () , _) , _))
        
        p2 {inr (inl x)} {inr (inr y)} = {!!}
        p2 {inr (inr x)} {inl *} = {!!}
{-        
        p2 {inr (inl x)} {inr (inr y)} = ({!f!} , g)
          where g : ¬ (inr (inl x) == inr (inr y)) ∧
                    ¬ (inr (inl x) <′′ inr (inr y)) ∧
                    ¬ (inr (inr y) <′′ inr (inl x)) ∧
                    ∃ (One + X + Y) (λ z → imdom (tree (One + X + Y) (inl *) _<′′_ t2) z (inr (inl x)) ∧ (z <′′ inr (inr y)))
                    → inr (inl x) cc′′ inr (inr y)
                g (a , b , c , exists (inl *) ((e , f , g') , h)) = snd (fst (lem-↑-root sdt0 sdt1) {x}) (e , tt , (λ {z} → g' {z}))
                g (a , b , c , exists (inr (inl _)) (_ , ()))
                g (a , b , c , exists (inr (inr _)) ((_ , () , _) , _))
                
                f : inr (inl x) cc′′ inr (inr y)
                    →  ¬ (inr {_} {X + Y} (inl x) == inr (inr y)) ∧
                       ¬ (inr (inl x) <′′ inr (inr y)) ∧
                       ¬ (inr (inr y) <′′ inr (inl x)) ∧
                       ∃ (One + X + Y) (λ z → imdom (tree (One + X + Y) (inl *) _<′′_ t2) z (inr (inl x)) ∧ (z <′′ inr (inr y)))
                f rlx==rry = (uneq-+-inl-inr ∘′ uncong-+-inr ,
                              id ,
                              id ,
                              exists (inl *) ((uneq-+-inl-inr ,
                                               tt ,
                                               (λ {z} → f0 {z})) ,
                                              tt))
                  where f0 : ∀ {z : One + X + Y}
                             → comb _<_ _<′_ (inl *) z ∧
                               comb _<_ _<′_ z (inr (inl x))
                             → ⊥
                        f0 {inl *} (() , _)
                        f0 {inr (inl r)} (_ , b) with snd (snd (fst (fst (lem-↑-root sdt0 sdt1) {x}) rlx==rry)) {inr (inl r)} (tt , b)
                        f0 {inr (inl _)} (_ , _) | ()
                        f0 {inr (inr _)} (_ , ())
          
        p2 {inr (inr x)} {inl *} = (f , g)
          where g : ¬ (inr (inr x) == inl *) ∧
                    ¬ (inr (inr x) <′′ inl *) ∧
                    ¬ (inl * <′′ inr (inr x)) ∧
                    ∃ (One + X + Y) (λ z → imdom (tree (One + X + Y) (inl *) _<′′_ t2) z (inr (inr x)) ∧ (z <′′ inl *))
                    → inr (inr x) cc′′ inl *
                g (a , b , c , exists (inl *) (_ , ()))
                g (a , b , c , exists (inr _) (_ , ()))
                
                f : inr (inr x) cc′′ inl *
                    → ¬ (inr (inr x) == inl *) ∧
                      ¬ (inr (inr x) <′′ inl *) ∧
                      ¬ (inl * <′′ inr (inr x)) ∧
                      ∃ (One + X + Y) (λ z → imdom (tree (One + X + Y) (inl *) _<′′_ t2) z (inr (inr x)) ∧ (z <′′ inl *))
                f ()
                
-}
        p2 {inr (inr x)} {inr (inl y)} = {!!}
        p2 {inr (inr x)} {inr (inr y)} = {!!}