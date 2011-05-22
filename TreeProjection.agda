{-# OPTIONS --universe-polymorphism #-}

open import Naturals
open import Functions
open import Logic
open import Relations
open import Structures
open import InclusivenessAndDerivationality
open import CCommandLemmas

module TreeProjection where



_↑_ : ∀ {n}
      → SingleDominanceTree n
      → SingleDominanceTree n
      → SingleDominanceTree n
sdt0 ↑ sdt1 = sdtree (One + X + Y)
                     (inl *)
                     (comb _<_ _<′_)
                     (lem-tree-comb (tree X r0 _<_ t0) (tree Y r1 _<′_ t1))
                     (lem-sd-comb (sdtree X r0 _<_ t0 sd0) (sdtree Y r1 _<′_ t1 sd1))
  where open SingleDominanceTree sdt0 using (_<_) renaming (carrier to X ; root to r0 ; isTree to t0 ; isSingleDominanceTree to sd0)
        open SingleDominanceTree sdt1 using () renaming (carrier to Y ; root to r1 ; _<_ to _<′_ ; isTree to t1 ; isSingleDominanceTree to sd1)



lem-↑-root : ∀ {n}
             → (sdt0 : SingleDominanceTree n)
             → (sdt1 : SingleDominanceTree n)
             → (∀ {x : SingleDominanceTree.carrier sdt0}
                  → x == SingleDominanceTree.root sdt0 ↔
                    imdom (sd-underlying-tree (sdt0 ↑ sdt1)) (SingleDominanceTree.root (sdt0 ↑ sdt1)) (inr (inl x))) ∧
               (∀ {y : SingleDominanceTree.carrier sdt1}
                  → y == SingleDominanceTree.root sdt1 ↔
                    imdom (sd-underlying-tree (sdt0 ↑ sdt1)) (SingleDominanceTree.root (sdt0 ↑ sdt1)) (inr (inr y)))
lem-↑-root sdt0 sdt1 = ((λ {x} → (ff {x} , fb {x})) ,
                        (λ {x} → (gf {x} , gb {x})))
  where open SingleDominanceTree sdt0 using (_<_) renaming (carrier to X ;
                                                            root to r0 ;
                                                            isTree to t0 ;
                                                            isSingleDominanceTree to sd0)
        
        open SingleDominanceTree sdt1 using () renaming (carrier to Y ;
                                                         root to r1 ;
                                                         _<_ to _<′_ ;
                                                         isTree to t1 ;
                                                         isSingleDominanceTree to sd1)
        
        a0 : Asymmetric _<_
        a0 = fst (snd (snd t0))
        
        rt0 : Rooted r0 _<_
        rt0 = snd (snd (snd t0))
        
        ff : ∀ {x : X}
             → x == r0
             → imdom (sd-underlying-tree (sdt0 ↑ sdt1)) (SingleDominanceTree.root (sdt0 ↑ sdt1)) (inr (inl x))
        ff {x} isroot0 = (uneq-+-inl-inr , tt , λ {x} → h {x})
          where h : ∀ {z : One + X + Y}
                    → comb _<_ _<′_ (inl *) z ∧ comb _<_ _<′_ z (inr (inl x))
                    → ⊥
                h {inl *} (() , _)
                h {inr (inl z)} (_ , q) = ((λ rt0' → a0 {z} {x} (q , subst-==-2 {F = _<_} x z (trans-== isroot0 rt0') q))
                                           ▿
                                           (λ rt0' → a0 {z} {x} (q , subst-== {F = λ x0 → x0 < z} r0 x (comm-== isroot0) rt0')))
                                          (rt0 {z})
                h {inr (inr _)} (_ , ())
        
        fb : ∀ {x : X}
             → imdom (sd-underlying-tree (sdt0 ↑ sdt1)) (SingleDominanceTree.root (sdt0 ↑ sdt1)) (inr (inl x))
             → x == r0
        fb {x} (_ , _ , c) with rt0 {x}
        ... | inl r0==x = comm-== r0==x
        ... | inr r0<x with c {inr (inl r0)} (tt , r0<x)
        ... | ()
        
        a1 : Asymmetric _<′_
        a1 = fst (snd (snd t1))
        
        rt1 : Rooted r1 _<′_
        rt1 = snd (snd (snd t1))
        
        gf : ∀ {x : Y}
             → x == r1
             → imdom (sd-underlying-tree (sdt0 ↑ sdt1)) (SingleDominanceTree.root (sdt0 ↑ sdt1)) (inr (inr x))
        gf {x} isroot1 = (uneq-+-inl-inr , tt , λ {x} → h {x})
          where h : ∀ {z : One + X + Y}
                    → comb _<_ _<′_ (inl *) z ∧ comb _<_ _<′_ z (inr (inr x))
                    → ⊥
                h {inl *} (() , _)
                h {inr (inl _)} (_ , ())
                h {inr (inr z)} (_ , q) = ((λ rt1' → a1 {z} {x} (q , subst-==-2 {F = _<′_} x z (trans-== isroot1 rt1') q))
                                           ▿
                                           (λ rt1' → a1 {z} {x} (q , subst-== {F = λ x1 → x1 <′ z} r1 x (comm-== isroot1) rt1')))
                                          (rt1 {z})
        
        gb : ∀ {x : Y}
             → imdom (sd-underlying-tree (sdt0 ↑ sdt1)) (SingleDominanceTree.root (sdt0 ↑ sdt1)) (inr (inr x))
             → x == r1
        gb {x} (_ , _ , c) with rt1 {x}
        ... | inl r1==x = comm-== r1==x
        ... | inr r1<x with c {inr (inr r1)} (tt , r1<x)
        ... | ()

lem-↑-cc-pres : ∀ {ℓ}
                → (sdt0 : SingleDominanceTree ℓ)
                → (_cc_ : Rel (SingleDominanceTree.carrier sdt0) ℓ)
                → IsCCommandRel sdt0 _cc_
                → (sdt1 : SingleDominanceTree ℓ)
                → (_cc′_ : Rel (SingleDominanceTree.carrier sdt1) ℓ)
                → IsCCommandRel sdt1 _cc′_
                → (_cc′′_ : Rel (SingleDominanceTree.carrier (sdt0 ↑ sdt1)) ℓ)
                → IsCCommandRel (sdt0 ↑ sdt1) _cc′′_
                → (∀ {x y : SingleDominanceTree.carrier sdt0} → x cc y ↔ inr (inl x) cc′′ inr (inl y)) ∧
                  (∀ {x y : SingleDominanceTree.carrier sdt1} → x cc′ y ↔ inr (inr x) cc′′ inr (inr y))
lem-↑-cc-pres {ℓ} sdt0 _cc_ p0 sdt1 _cc′_ p1 _cc′′_ p2 = ((λ {x} {y} → (ff , fb)) ,
                                                     (λ {x} {y} → (gf , gb)))
  where open SingleDominanceTree sdt0 using (_<_) renaming (carrier to X ;
                                                            root to r0 ;
                                                            isTree to t0 ;
                                                            isSingleDominanceTree to sd0)
        
        open SingleDominanceTree sdt1 using () renaming (carrier to Y ;
                                                         root to r1 ;
                                                         _<_ to _<′_ ;
                                                         isTree to t1 ;
                                                         isSingleDominanceTree to sd1)
        
        open SingleDominanceTree (sdt0 ↑ sdt1) using () renaming (root to r2 ;
                                                                  _<_ to _<′′_ ;
                                                                  isTree to t2 ;
                                                                  isSingleDominanceTree to sd2)
        
        ff : ∀ {x y : X} → x cc y → inr (inl x) cc′′ inr (inl y)
        ff {x} {y} xccy with fst (p0 {x} {y}) xccy
        ... | (a , b , c , exists d e ) = snd (p2 {inr (inl x)} {inr (inl y)}) (a ∘′ uncong-+-inl ∘′ uncong-+-inr ,
                                                                                b ,
                                                                                c ,
                                                                                exists (inr (inl d))
                                                                                       ((fst (fst e) ∘′ uncong-+-inl ∘′ uncong-+-inr ,
                                                                                         fst (snd (fst e)) ,
                                                                                         (λ {z} → ffsub {z})) ,
                                                                                        snd e))
          where ffsub : ∀ {z : One + X + Y}
                        → ¬ (comb _<_ _<′_ (inr (inl d)) z ∧
                             comb _<_ _<′_ z (inr (inl x)))
                ffsub {inl *} (() , _)
                ffsub {inr (inl z)} (p , q) = snd (snd (fst e)) (p , q)
                ffsub {inr (inr z)} (() , ())
        
        gf : ∀ {x y : Y} → x cc′ y → inr (inr x) cc′′ inr (inr y)
        gf {x} {y} xcc′y with fst (p1 {x} {y}) xcc′y
        ... | (a , b , c , exists d e ) = snd (p2 {inr (inr x)} {inr (inr y)}) (a ∘′ uncong-+-inr ∘′ uncong-+-inr ,
                                                                                b ,
                                                                                c ,
                                                                                exists (inr (inr d))
                                                                                       ((fst (fst e) ∘′ uncong-+-inr ∘′ uncong-+-inr ,
                                                                                         fst (snd (fst e)) ,
                                                                                         (λ {z} → gfsub {z})) ,
                                                                                        snd e))
          where gfsub : ∀ {z : One + X + Y}
                        → ¬ (comb _<_ _<′_ (inr (inr d)) z ∧
                             comb _<_ _<′_ z (inr (inr x)))
                gfsub {inl *} (() , _)
                gfsub {inr (inl z)} (() , ())
                gfsub {inr (inr z)} (p , q) = snd (snd (fst e)) (p , q)
        
        fb : ∀ {x y : X} → inr (inl x) cc′′ inr (inl y) → x cc y
        fb {x} {y} rlxccrly with fst (p2 {inr (inl x)} {inr (inl y)}) rlxccrly
        fb {x} {y} rlxccrly | (a , b , c , exists (inl *) ((d , e , f) , g)) with snd (snd (snd t0)) {y}
        fb {x} {y} rlxccrly | (a , b , c , exists (inl *) ((d , e , f) , g)) | inl rt0 with a (cong inr (cong inl (trans-== (snd (fst (lem-↑-root sdt0 sdt1) {x}) (uneq-+-inl-inr , tt , (λ {z} → f {z}))) rt0)))
        fb {x} {y} rlxccrly | (a , b , c , exists (inl *) ((d , e , f) , g)) | inl rt0 | ()
        fb {x} {y} rlxccrly | (a , b , c , exists (inl *) ((d , e , f) , g)) | inr rt0 with b (subst-== {F = λ r → r < y} r0 x (comm-== (snd (fst (lem-↑-root sdt0 sdt1) {x}) (uneq-+-inl-inr , tt , (λ {z} → f {z})))) rt0)
        fb {x} {y} rlxccrly | (a , b , c , exists (inl *) ((d , e , f) , g)) | inr rt0 | ()
        fb {x} {y} rlxccrly | (a , b , c , exists (inr (inl z)) ((d , e , f) , g)) = snd (p0 {x} {y}) (a ∘′ cong inr ∘′ cong inl ,
                                                                       b ,
                                                                       c ,
                                                                       exists z (((λ z==x → d (cong inr (cong inl z==x))) , 
                                                                                  e ,
                                                                                  (λ {z'} h → f {inr (inl z')} h)),
                                                                                 g))
        fb {x} {y} rlxccrly | (a , b , c , exists (inr (inr z)) (_ , ()))

        gb : ∀ {x y : Y} → inr (inr x) cc′′ inr (inr y) → x cc′ y
        gb {x} {y} rlxcc′rly with fst (p2 {inr (inr x)} {inr (inr y)}) rlxcc′rly
        gb {x} {y} rlxcc′rly | (a , b , c , exists (inl *) ((d , e , f) , g)) with snd (snd (snd t1)) {y}
        gb {x} {y} rlxcc′rly | (a , b , c , exists (inl *) ((d , e , f) , g)) | inl rt1 with a (cong inr (cong inr (trans-== (snd (snd (lem-↑-root sdt0 sdt1) {x}) (uneq-+-inl-inr , tt , (λ {z} → f {z}))) rt1)))
        gb {x} {y} rlxcc′rly | (a , b , c , exists (inl *) ((d , e , f) , g)) | inl rt1 |  ()
        gb {x} {y} rlxcc′rly | (a , b , c , exists (inl *) ((d , e , f) , g)) | inr rt1 with b (subst-== {F = λ r → r <′ y} r1 x (comm-== (snd (snd (lem-↑-root sdt0 sdt1) {x}) (uneq-+-inl-inr , tt , (λ {z} → f {z})))) rt1)
        gb {x} {y} rlxcc′rly | (a , b , c , exists (inl *) ((d , e , f) , g)) | inr rt1 | ()
        gb {x} {y} rlxcc′rly | (a , b , c , exists (inr (inl z)) (_ , ()))
        gb {x} {y} rlxcc′rly | (a , b , c , exists (inr (inr z)) ((d , e , f) , g)) = snd (p1 {x} {y}) (a ∘′ cong inr ∘′ cong inr ,
                                                                       b ,
                                                                       c ,
                                                                       exists z (((λ z==x → d (cong inr (cong inr z==x))) , 
                                                                                  e ,
                                                                                  (λ {z'} h → f {inr (inr z')} h)),
                                                                                 g))