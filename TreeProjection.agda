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
        a0 = fst (snd (snd t0)) -- t0 = (t0 , i0 , a0 , rt0)
        
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