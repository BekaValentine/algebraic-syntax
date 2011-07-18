{-# OPTIONS --universe-polymorphism #-}

open import Naturals
open import Functions
open import Logic
open import Relations
open import Structures
open import InclusivenessAndDerivationality

module CCommandLemmas where



lem-cc-uniqueness : ∀ {ℓ} {t : SingleDominanceTree ℓ}
                    → (_cc_ : Rel (SingleDominanceTree.carrier t) ℓ)
                    → IsCCommandRel t _cc_
                    → (_cc′_ : Rel (SingleDominanceTree.carrier t) ℓ)
                    → IsCCommandRel t _cc′_
                    → ObsEquivalent _cc_ _cc′_
lem-cc-uniqueness _cc_ p0 _cc′_ p1 {x} {y} = (snd (p1 {x} {y}) ∘′ fst (p0 {x} {y}) ,
                                              snd (p0 {x} {y}) ∘′ fst (p1 {x} {y}))



comb : ∀ {ℓ} {X Y : Set ℓ}
       → Rel X ℓ
       → Rel Y ℓ
       → Rel (One + X + Y) ℓ
comb _<_ _<′_ (inl *) (inl *) = ⊥
comb _<_ _<′_ (inl *) (inr _) = ⊤
comb _<_ _<′_ (inr _) (inl *) = ⊥
comb _<_ _<′_ (inr (inl x)) (inr (inl y)) = x < y
comb _<_ _<′_ (inr (inl _)) (inr (inr _)) = ⊥
comb _<_ _<′_ (inr (inr _)) (inr (inl _)) = ⊥
comb _<_ _<′_ (inr (inr x)) (inr (inr y)) = x <′ y


lem-trans-comb : ∀ {ℓ} {X Y : Set ℓ}
                 → (_<_ : Rel X ℓ)
                 → Transitive _<_
                 → (_<′_ : Rel Y ℓ)
                 → Transitive _<′_
                 → Transitive (comb _<_ _<′_)
lem-trans-comb _<_ p0 _<′_ p1 {inl _} {inl _} {_} (() , _)
lem-trans-comb _<_ p0 _<′_ p1 {inl _} {inr _} {inl _} (_ , ())
lem-trans-comb _<_ p0 _<′_ p1 {inl _} {inr _} {inr _} (_ , _) = tt
lem-trans-comb _<_ p0 _<′_ p1 {inr _} {inl _} {inl _} (_ , ())
lem-trans-comb _<_ p0 _<′_ p1 {inr _} {inl _} {inr _} (() , _)
lem-trans-comb _<_ p0 _<′_ p1 {inr _} {inr _} {inl _} (_ , ())
lem-trans-comb _<_ p0 _<′_ p1 {inr (inl _)} {inr (inl _)} {inr (inl _)} p2 = p0 p2
lem-trans-comb _<_ p0 _<′_ p1 {inr (inl _)} {inr (inl _)} {inr (inr _)} (_ , ())
lem-trans-comb _<_ p0 _<′_ p1 {inr (inl _)} {inr (inr _)} {inr _} (() , _)
lem-trans-comb _<_ p0 _<′_ p1 {inr (inr _)} {inr (inl _)} {inr _} (() , _)
lem-trans-comb _<_ p0 _<′_ p1 {inr (inr _)} {inr (inr _)} {inr (inl _)} (_ , ())
lem-trans-comb _<_ p0 _<′_ p1 {inr (inr _)} {inr (inr _)} {inr (inr _)} p2 = p1 p2

lem-irref-comb : ∀ {ℓ} {X Y : Set ℓ}
                 → (_<_ : Rel X ℓ)
                 → Irreflexive _<_
                 → (_<′_ : Rel Y ℓ)
                 → Irreflexive _<′_
                 → Irreflexive (comb _<_ _<′_)
lem-irref-comb _<_ p0 _<′_ p1 {inl *} ()
lem-irref-comb _<_ p0 _<′_ p1 {inr (inl x)} p = p0 {x} p
lem-irref-comb _<_ p0 _<′_ p1 {inr (inr x)} p = p1 {x} p

lem-asym-comb : ∀ {ℓ} {X Y : Set ℓ}
                → (_<_ : Rel X ℓ)
                → Asymmetric _<_
                → (_<′_ : Rel Y ℓ)
                → Asymmetric _<′_
                → Asymmetric (comb _<_ _<′_)
lem-asym-comb _<_ p0 _<′_ p1 {inl *} {inl *} (() , ())
lem-asym-comb _<_ p0 _<′_ p1 {inl *} {inr (inl y)} (_ , ())
lem-asym-comb _<_ p0 _<′_ p1 {inl *} {inr (inr y)} (_ , ())
lem-asym-comb _<_ p0 _<′_ p1 {inr (inl x)} {inl *} (() , _)
lem-asym-comb _<_ p0 _<′_ p1 {inr (inl x)} {inr (inl y)} p = p0 {x} {y} p
lem-asym-comb _<_ p0 _<′_ p1 {inr (inl x)} {inr (inr y)} (() , ())
lem-asym-comb _<_ p0 _<′_ p1 {inr (inr x)} {inl *} (() , _)
lem-asym-comb _<_ p0 _<′_ p1 {inr (inr x)} {inr (inl y)} (() , ())
lem-asym-comb _<_ p0 _<′_ p1 {inr (inr x)} {inr (inr y)} p = p1 {x} {y} p

lem-rooted-comb : ∀ {ℓ} {X Y : Set ℓ}
                  → (_<_ : Rel X ℓ)
                  → (_<′_ : Rel Y ℓ)
                  → (y : One + X + Y)
                  → inl * == y ∨ comb _<_ _<′_ (inl *) y
lem-rooted-comb _<_ _<′_ (inl *) = inl (refl (inl *))
lem-rooted-comb _<_ _<′_ (inr x) = inr tt

lem-tree-comb : ∀ {n}
                → (t0 : Tree n)
                → (t1 : Tree n)
                → IsTree (digraph (One + Tree.carrier t0 + Tree.carrier t1) (comb (Tree._<_ t0) (Tree._<_ t1))) (inl *)
lem-tree-comb (tree X r0 _<_ (t0 , i0 , a0 , rt0)) (tree Y r1 _<′_ (t1 , i1 , a1 , rt1)) = (t2 , i2 , a2 , λ {x} → r2 {x})
  where t2 = λ {x} {y} {z} → lem-trans-comb _<_ t0 _<′_ t1 {x} {y} {z}
        i2 = λ {x} → lem-irref-comb _<_ i0 _<′_ i1 {x}
        a2 = λ {x} {y} → lem-asym-comb _<_ a0 _<′_ a1 {x} {y}
        
        r2 : Rooted (inl *) (comb _<_ _<′_)
        r2 {inl *} = inl (refl (inl *))
        r2 {inr (inl x)} = inr tt
        r2 {inr (inr x)} = inr tt
        

lem-sd-comb : ∀ {n}
              → (sdt0 : SingleDominanceTree n)
              → (sdt1 : SingleDominanceTree n)
              → IsSingleDominanceTree (tree (One + SingleDominanceTree.carrier sdt0 + SingleDominanceTree.carrier sdt1)
                                            (inl *)
                                            (comb (SingleDominanceTree._<_ sdt0) (SingleDominanceTree._<_ sdt1))
                                            (lem-tree-comb (sd-underlying-tree sdt0) (sd-underlying-tree sdt1)))
lem-sd-comb sdt0 sdt1 {inl *} {inl *} {inl *} ((_ , () , _) , (_ , () , _))
lem-sd-comb sdt0 sdt1 {inl *} {inl *} {inr _} _ = refl (inl *)
lem-sd-comb sdt0 sdt1 {inl *} {inr (inl _)} {inl *} (_ , (_ , () , _))
lem-sd-comb sdt0 sdt1 {inl *} {inr (inl y)} {inr (inl _)} ((_ , _ , p02) , (_ , p11 , _)) with p02 {inr (inl y)} (tt , p11)
... | ()
lem-sd-comb sdt0 sdt1 {inl *} {inr (inl _)} {inr (inr _)} (_ , (_ , () , _))
lem-sd-comb sdt0 sdt1 {inl *} {inr (inr _)} {inl *} (_ , (_ , () , _))
lem-sd-comb sdt0 sdt1 {inl *} {inr (inr _)} {inr (inl _)} (_ , (_ , () , _))
lem-sd-comb sdt0 sdt1 {inl *} {inr (inr y)} {inr (inr _)} ((_ , _ , p02) , (_ , p11 , _)) with p02 {inr (inr y)} (tt , p11)
... | ()
lem-sd-comb sdt0 sdt1 {inr (inl _)} {inl *} {inl *} (_ , (_ , () , _))
lem-sd-comb sdt0 sdt1 {inr (inl x)} {inl *} {inr (inl _)} ((_ , p01 , _) , (_ , _ , p12)) with p12 {inr (inl x)} (tt , p01)
... | ()
lem-sd-comb sdt0 sdt1 {inr (inl _)} {inl *} {inr (inr _)} ((_ , () , _) , _)
lem-sd-comb sdt0 sdt1 {inr (inl _)} {inr (inl _)} {inl *} (_ , (_ , () , _))
lem-sd-comb sdt0 sdt1 {inr (inl x)} {inr (inl y)} {inr (inl z)} ((p00 , p01 , p02) , (p10 , p11 , p12)) = cong (inr ∘′ inl) ((SingleDominanceTree.isSingleDominanceTree sdt0) {x} {y} {z} (((λ x==z → p00 (cong (inr ∘′ inl) x==z)) , p01 , (λ {z′} p → p02 {inr (inl z′)} p)) , ((λ y==z → p10 (cong (inr ∘′ inl) y==z)) , p11 , (λ {z′} p → p12 {inr (inl z′)} p))))
lem-sd-comb sdt0 sdt1 {inr (inl _)} {inr (inl _)} {inr (inr _)} (_ , (_ , () , _))
lem-sd-comb sdt0 sdt1 {inr (inl _)} {inr (inr _)} {inl *} (_ , (_ , () , _))
lem-sd-comb sdt0 sdt1 {inr (inl _)} {inr (inr _)} {inr (inl _)} (_ , (_ , () , _))
lem-sd-comb sdt0 sdt1 {inr (inl _)} {inr (inr _)} {inr (inr _)} ((_ , () , _) , _)
lem-sd-comb sdt0 sdt1 {inr (inr _)} {inl *} {inl *} (_ , (_ , () , _))
lem-sd-comb sdt0 sdt1 {inr (inr _)} {inl *} {inr (inl _)} ((_ , () , _) , _)
lem-sd-comb sdt0 sdt1 {inr (inr x)} {inl *} {inr (inr _)} ((_ , p01 , _) , (_ , _ , p12)) with p12 {inr (inr x)} (tt , p01)
... | ()
lem-sd-comb sdt0 sdt1 {inr (inr x)} {inr (inl y)} {inl *} (_ , (_ , () , _))
lem-sd-comb sdt0 sdt1 {inr (inr x)} {inr (inl y)} {inr (inl z)} ((_ , () , _) , _)
lem-sd-comb sdt0 sdt1 {inr (inr x)} {inr (inl y)} {inr (inr z)} (_ , (_ , () , _))
lem-sd-comb sdt0 sdt1 {inr (inr x)} {inr (inr y)} {inl *} (_ , (_ , () , _))
lem-sd-comb sdt0 sdt1 {inr (inr x)} {inr (inr y)} {inr (inl z)} (_ , (_ , () , _))
lem-sd-comb sdt0 sdt1 {inr (inr x)} {inr (inr y)} {inr (inr z)} ((p00 , p01 , p02) , (p10 , p11 , p12)) = cong (inr ∘′ inr) ((SingleDominanceTree.isSingleDominanceTree sdt1) {x} {y} {z} (((λ x==z → p00 (cong (inr ∘′ inr) x==z)) , p01 , (λ {z′} p → p02 {inr (inr z′)} p)) , ((λ y==z → p10 (cong (inr ∘′ inr) y==z)) , p11 , (λ {z′} p → p12 {inr (inr z′)} p))))