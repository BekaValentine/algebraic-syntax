{-# OPTIONS --universe-polymorphism #-}

open import Naturals
open import Functions
open import Logic
open import Relations
open import Structures
open import InclusivenessAndDerivationality

module CCommand where



iso2 : ∀ {n} {X Y : Set n}
       → (One + X + Y) × (One + X + Y)
       → (One × One + One × X + One × Y) +
         (X × One + X × X + X × Y) +
         (Y × One + Y × X + Y × Y)
iso2 {n} = ((id +′ distl) +′ ((id {n} +′ distl) ∘′ distl) +′ ((id {n} +′ distl) ∘′ distl)) ∘′ (distl +′ distr) ∘′ distr

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


lem-rooted-comb : ∀ {ℓ} {X Y : Set ℓ}
                  → (_<_ : Rel X ℓ)
                  → (_<′_ : Rel Y ℓ)
                  → (y : One + X + Y)
                  → inl * == y + comb _<_ _<′_ (inl *) y
lem-rooted-comb _<_ _<′_ (inl *) = inl (refl (inl *))
lem-rooted-comb _<_ _<′_ (inr x) = inr tt

lem-sd-comb : ∀ {ℓ} {X Y : Set ℓ}
              → (_<_ : Rel X ℓ)
              → (isTree0 : IsTree (digraph X _<_))
              → IsSingleDominanceTree (tree X _<_ isTree0)
              → (_<′_ : Rel Y ℓ)
              → (isTree1 : IsTree (digraph Y _<′_))
              → IsSingleDominanceTree (tree Y _<′_ isTree1)
              → (isTree2 : IsTree (digraph (One + X + Y) (comb _<_ _<′_)))
              → IsSingleDominanceTree (tree (One + X + Y) (comb _<_ _<′_) isTree2)
lem-sd-comb _<_ t0 sd0 _<′_ t1 sd1 t2 {inl *} {inl *} {inl *} (_ , (_ , () , _))
lem-sd-comb _<_ t0 sd0 _<′_ t1 sd1 t2 {inl *} {inl *} {inr _} _ = refl (inl *)
lem-sd-comb _<_ t0 sd0 _<′_ t1 sd1 t2 {inl *} {inr (inl y)} {inl *} (_ , (_ , () , _))
lem-sd-comb _<_ t0 sd0 _<′_ t1 sd1 t2 {inl *} {inr (inl y)} {inr (inl z)} ((p00 , p01 , p02) , (p10 , p11 , p12)) with p02 {inr (inl y)} (tt , p11)
... | ()
lem-sd-comb _<_ t0 sd0 _<′_ t1 sd1 t2 {inl *} {inr (inl y)} {inr (inr z)} (_ , (_ , () , _))
lem-sd-comb _<_ t0 sd0 _<′_ t1 sd1 t2 {inl *} {inr (inr y)} {inl *} (_ , (_ , () , _))
lem-sd-comb _<_ t0 sd0 _<′_ t1 sd1 t2 {inl *} {inr (inr y)} {inr (inl z)} (_ , (_ , () , _))
lem-sd-comb _<_ t0 sd0 _<′_ t1 sd1 t2 {inl *} {inr (inr y)} {inr (inr z)} ((p00 , p01 , p02) , (p10 , p11 , p12)) with p02 {inr (inr y)} (tt , p11)
... | ()
lem-sd-comb _<_ t0 sd0 _<′_ t1 sd1 t2 {inr (inl x)} {inl *} {inl *} (_ , (_ , () , _))
lem-sd-comb _<_ t0 sd0 _<′_ t1 sd1 t2 {inr (inl x)} {inl *} {inr (inl z)} ((p00 , p01 , p02) , (p10 , p11 , p12)) with p12 {inr (inl x)} (tt , p01)
... | ()
lem-sd-comb _<_ t0 sd0 _<′_ t1 sd1 t2 {inr (inl x)} {inl *} {inr (inr z)} ((_ , () , _) , _)
lem-sd-comb _<_ t0 sd0 _<′_ t1 sd1 t2 {inr (inl x)} {inr (inl y)} {inl *} (_ , (_ , () , _))
lem-sd-comb _<_ t0 sd0 _<′_ t1 sd1 t2 {inr (inl x)} {inr (inl y)} {inr (inl z)} ((p00 , p01 , p02) , (p10 , p11 , p12)) = cong (inr ∘′ inl) (sd0 {x} {y} {z} (((λ x==z → p00 (cong (inr ∘′ inl) x==z)) , p01 , (λ {z′} p → p02 {inr (inl z′)} p)) , ((λ y==z → p10 (cong (inr ∘′ inl) y==z)) , p11 , (λ {z′} p → p12 {inr (inl z′)} p))))
lem-sd-comb _<_ t0 sd0 _<′_ t1 sd1 t2 {inr (inl x)} {inr (inl y)} {inr (inr z)} (_ , (_ , () , _))
lem-sd-comb _<_ t0 sd0 _<′_ t1 sd1 t2 {inr (inl x)} {inr (inr y)} {inl *} (_ , (_ , () , _))
lem-sd-comb _<_ t0 sd0 _<′_ t1 sd1 t2 {inr (inl x)} {inr (inr y)} {inr (inl z)} (_ , (_ , () , _))
lem-sd-comb _<_ t0 sd0 _<′_ t1 sd1 t2 {inr (inl x)} {inr (inr y)} {inr (inr z)} ((_ , () , _) , _)
lem-sd-comb _<_ t0 sd0 _<′_ t1 sd1 t2 {inr (inr x)} {inl *} {inl *} (_ , (_ , () , _))
lem-sd-comb _<_ t0 sd0 _<′_ t1 sd1 t2 {inr (inr x)} {inl *} {inr (inl z)} ((_ , () , _) , _)
lem-sd-comb _<_ t0 sd0 _<′_ t1 sd1 t2 {inr (inr x)} {inl *} {inr (inr z)} ((p00 , p01 , p02) , (p10 , p11 , p12)) with p12 {inr (inr x)} (tt , p01)
... | ()
lem-sd-comb _<_ t0 sd0 _<′_ t1 sd1 t2 {inr (inr x)} {inr (inl y)} {inl *} (_ , (_ , () , _))
lem-sd-comb _<_ t0 sd0 _<′_ t1 sd1 t2 {inr (inr x)} {inr (inl y)} {inr (inl z)} ((_ , () , _) , _)
lem-sd-comb _<_ t0 sd0 _<′_ t1 sd1 t2 {inr (inr x)} {inr (inl y)} {inr (inr z)} (_ , (_ , () , _))
lem-sd-comb _<_ t0 sd0 _<′_ t1 sd1 t2 {inr (inr x)} {inr (inr y)} {inl *} (_ , (_ , () , _))
lem-sd-comb _<_ t0 sd0 _<′_ t1 sd1 t2 {inr (inr x)} {inr (inr y)} {inr (inl z)} (_ , (_ , () , _))
lem-sd-comb _<_ t0 sd0 _<′_ t1 sd1 t2 {inr (inr x)} {inr (inr y)} {inr (inr z)} ((p00 , p01 , p02) , (p10 , p11 , p12)) = cong (inr ∘′ inr) (sd1 {x} {y} {z} (((λ x==z → p00 (cong (inr ∘′ inr) x==z)) , p01 , (λ {z′} p → p02 {inr (inr z′)} p)) , ((λ y==z → p10 (cong (inr ∘′ inr) y==z)) , p11 , (λ {z′} p → p12 {inr (inr z′)} p))))
              

_↑_ : ∀ {n}
      → SingleDominanceTree n
      → SingleDominanceTree n
      → SingleDominanceTree n
sdtree X _<_ (t0 , i0 , a0 , p0) sd0 ↑ sdtree Y _<′_ (t1 , i1 , a1 , p1) sd1 = sdtree (One + X + Y)
                                                                                  (comb _<_ _<′_)
                                                                                  t2
                                                                                  (lem-sd-comb _<_ ((λ {x} {y} {z} → t0 {x} {y} {z}) ,
                                                                                                    (λ {x} → i0 {x}) ,
                                                                                                    (λ {x} {y} p → a0 {x} {y} p) ,
                                                                                                    p0) sd0
                                                                                               _<′_ ((λ {x} {y} {z} → t1 {x} {y} {z}) ,
                                                                                                     (λ {x} → i1 {x}) ,
                                                                                                     (λ {x} {y} p → a1 {x} {y} p) ,
                                                                                                     p1) sd1
                                                                                               t2)
  where t2 : IsTree (digraph (One + X + Y) (comb  _<_ _<′_))
        t2 = ((λ {x} {y} {z} p → lem-trans-comb _<_ t0 _<′_ t1 {x} {y} {z} p) ,
              (λ {x} → lem-irref-comb _<_ i0 _<′_ i1 {x}) ,
              (λ {x} {y} → h {x} {y}) ,
              exists (inl *) (lem-rooted-comb _<_ _<′_))
          where h : ∀ {x y : One + X + Y}
                    → comb _<_ _<′_ x y ∧ comb _<_ _<′_ y x
                    → ⊥
                h {inl *} {inl *} (() , ())
                h {inl *} {inr _} (_ , ())
                h {inr (inl _)} {inl *} (() , _)
                h {inr (inl x)} {inr (inl y)} p = a0 {x} {y} p
                h {inr (inl _)} {inr (inr _)} (() , ())
                h {inr (inr _)} {inl *} (() , _)
                h {inr (inr _)} {inr (inl _)} (() , _)
                h {inr (inr x)} {inr (inr y)} p = a1 {x} {y} p

lem-sd-root : ∀ {n}
              → (sdt0 : SingleDominanceTree n)
              → (sdt1 : SingleDominanceTree n)
              → (∀ {x : SingleDominanceTree.carrier sdt0}
                   → x == sdroot sdt0 ↔ imdom (sd-underlying-tree (sdt0 ↑ sdt1)) (sdroot (sdt0 ↑ sdt1)) (inr (inl x))) ∧
                (∀ {y : SingleDominanceTree.carrier sdt1}
                   → y == sdroot sdt1 ↔ imdom (sd-underlying-tree (sdt0 ↑ sdt1)) (sdroot (sdt0 ↑ sdt1)) (inr (inr y)))
lem-sd-root sdt0 sdt1 = ((λ {x : SingleDominanceTree.carrier sdt0} → (fl {x} , fr {x})) ,
                         (λ {x : SingleDominanceTree.carrier sdt1} → (gl {x} , gr {x})))
  where fl : ∀ {x : SingleDominanceTree.carrier sdt0}
             → x == sdroot sdt0
             → imdom (sd-underlying-tree (sdt0 ↑ sdt1)) (sdroot (sdt0 ↑ sdt1)) (inr (inl x))
        fl {x} isroot0 with sdt0 | sdt1
        ... | sdtree X _<_ (t0 , i0 , a0 , exists r0 p0) sd0 | sdtree Y _<′_ t1 sd1 = (uneq-+-inl-inr , tt , λ {z} → h {z})
          where h : ∀ {z : One + X + Y}
                    → comb _<_ _<′_ (inl *) z × comb _<_ _<′_ z (inr (inl x))
                    → ⊥
                h {inl *} (() , _)
                h {inr (inl z)} (p , q) = ((λ z0 → a0 {z} {x} (q , subst-==-2 {F = _<_} x z (trans-== isroot0 z0) q))
                                           ▿
                                           (λ z0 → a0 {z} {x} (q , subst-== {F = λ x0 → x0 < z} r0 x (comm-== isroot0) z0)))
                                            (p0 z)
                h {inr (inr _)} (_ , ())
        
        fr : ∀ {x : SingleDominanceTree.carrier sdt0}
             → imdom (sd-underlying-tree (sdt0 ↑ sdt1)) (sdroot (sdt0 ↑ sdt1)) (inr (inl x))
             → x == sdroot sdt0
        fr {x} (a , b , c) with sdt0 | sdt1
        ... | sdtree X _<_ (t0 , i0 , a0 , exists r0 p0) sd0 | sdtree Y _<′_ t1 sd1 with p0 x
        ... | inl r0==x = comm-== r0==x
        ... | inr r0<x with c {inr (inl r0)} (tt , r0<x)
        ... | ()

        gl : ∀ {x : SingleDominanceTree.carrier sdt1}
             → x == sdroot sdt1
             → imdom (sd-underlying-tree (sdt0 ↑ sdt1)) (sdroot (sdt0 ↑ sdt1)) (inr (inr x))
        gl {x} isroot1 with sdt0 | sdt1
        ... | sdtree X _<_ t0 sd0 | sdtree Y _<′_ (t1 , i1 , a1 , exists r1 p1) sd1 = (uneq-+-inl-inr , tt , λ {z} → h {z})
          where h : ∀ {z : One + X + Y}
                    → comb _<_ _<′_ (inl *) z × comb _<_ _<′_ z (inr (inr x))
                    → ⊥
                h {inl *} (() , _)
                h {inr (inl _)} (_ , ())
                h {inr (inr z)} (p , q) = ((λ z1 → a1 {z} {x} (q , subst-==-2 {F = _<′_} x z (trans-== isroot1 z1) q))
                                           ▿
                                           (λ z1 → a1 {z} {x} (q , subst-== {F = λ x1 → x1 <′ z} r1 x (comm-== isroot1) z1)))
                                            (p1 z)
        
        gr : ∀ {x : SingleDominanceTree.carrier sdt1}
             → imdom (sd-underlying-tree (sdt0 ↑ sdt1)) (sdroot (sdt0 ↑ sdt1)) (inr (inr x))
             → x == sdroot sdt1
        gr {x} (a , b , c) with sdt0 | sdt1
        ... | sdtree X _<_ t0 sd0 | sdtree Y _<′_ (t1 , i1 , a1 , exists r1 p1) sd1 with p1 x
        ... | inl r1==x = comm-== r1==x
        ... | inr r1<′x with c {inr (inr r1)} (tt , r1<′x)
        ... | ()
        


cc-comb-lem : ∀ {ℓ}
              → (sdt0 : SingleDominanceTree ℓ)
              → (_cc_ : Rel (SingleDominanceTree.carrier sdt0) ℓ)
              → (p0 : IsCCommandRel sdt0 _cc_)
              → (sdt1 : SingleDominanceTree ℓ)
              → (_cc′_ : Rel (SingleDominanceTree.carrier sdt1) ℓ)
              → (p1 : IsCCommandRel sdt1 _cc′_)
              → ∃ (Rel (SingleDominanceTree.carrier (sdt0 ↑ sdt1)) ℓ)
                  (IsCCommandRel (sdt0 ↑ sdt1))
cc-comb-lem {ℓ} sdt0 _cc_ p0 sdt1 _cc′_ p1 = exists _cc′′_ (λ {x} {y} → ccp {x} {y})
  where _cc′′_ : Rel (SingleDominanceTree.carrier (sdt0 ↑ sdt1)) ℓ
        x cc′′ y with sdt0 | sdt1
        ... | sdtree X _<_ t0 sd0 | sdtree Y _<′_ t1 sd1 with x | y
        ... | inl * | inl * = {!!}
        ... | inl * | inr (inl y0) = {!!}
        ... | inl * | inr (inr y0) = {!!}
        ... | inr _ | _ = {!!}
        
        ccp : IsCCommandRel (sdt0 ↑ sdt1) _cc′′_
        ccp {x} {y} with sdt0 ↑ sdt1 | sdt0 | sdt1
        ... | sdtree X _<_ t0 sd0 | sdtree Y _<′_ t1 sd1 | sdtree _ _<′′_ t2 sd2 with x | y
        ... | inl * | inl * = ({!!} , {!g!})
          where w : Set ℓ
                w = ?
                
                g : ¬ ⊥ × ¬ ⊥ ×
                    ∃ (One + X + Y) (λ z → imdom (tree (One + X + Y) _<′′_ t2) z (inl *) ∧ (z <′′ inl *))
                    → w
                g = {!!}
        ... | inl * | inr (inl y0) = {!!}
        ... | inl * | inr (inr y0) = {!!}
        ... | inr _ | _ = {!!}

{-

_cc′′_ : (x y : car) → ∃ (Set ℓ) (λ xccy → xccy ↔
                       ¬(x <′′ y) ∧
                       ¬(y <′′ x) ∧
                       ∃ car (λ z → imdom (tree car _<′′_ t2) z x ∧ z <′′ y))

(inl *) cc′′ (inl *) = exists ⊥ (f , g)
  where g : ¬(inl * <′′ inl *) ∧
            ¬(inl * <′′ inl *) ∧
            ∃ car (λ z → imdom (tree car _<′′_ t2) z (inl *) ∧ (z <′′ inl *))
            → ⊥
        g (_ , _ , exists (inl *) (_ , ()))
        g (_ , _ , exists (inr _) (_ , ()))

        f : ⊥ → ¬(inl * <′′ inl *) ∧
                 ¬(inl * <′′ inl *) ∧
                 ∃ car (λ z → imdom (tree car _<′′_ t2) z (inl *) ∧ (z <′′ inl *))
        f ()

(inl *) cc′′ (inr (inl y)) = exists ⊥ (f , g)
  where g : ¬(inl * <′′ inr (inl y)) ∧
            ¬(inr (inl y) <′′ inl *) ∧
            ∃ car (λ z → imdom (tree car _<′′_ t2) z (inl *) ∧ (z <′′ inr (inl y)))
            → ⊥
        g (_ , _ , exists (inl *) ((_ , () , _) , _))
        g (_ , _ , exists (inr (inl _)) ((_ , () , _) , _))
        g (_ , _ , exists (inr (inr _)) (_ , ()))
        
        f : ⊥ → ¬(inl * <′′ inr (inl y)) ∧
                ¬(inr (inl y) <′′ inl *) ∧
                ∃ car (λ z → imdom (tree car _<′′_ t2) z (inl *) ∧ (z <′′ inr (inl y)))
        f ()

(inl *) cc′′ (inr (inr y)) = exists ⊥ (f , g)
  where g : ¬(inl * <′′ inr (inr y)) ∧
            ¬(inr (inr y) <′′ inl *) ∧
            ∃ car (λ z → imdom (tree car _<′′_ t2) z (inl *) ∧ (z <′′ inr (inr y)))
            → ⊥
        g (_ , _ , exists (inl *) ((_ , () , _) , _))
        g (_ , _ , exists (inr _) ((_ , () , _) , _))
        
        f : ⊥ → ¬(inl * <′′ inr (inr y)) ∧
                ¬(inr (inr y) <′′ inl *) ∧
                ∃ car (λ z → imdom (tree car _<′′_ t2) z (inl *) ∧ (z <′′ inr (inr y)))
        f ()

(inr (inl x)) cc′′ (inl *) = exists ⊥ (f , g)
  where g : ¬(inr (inl x) <′′ inl *) ∧
            ¬(inl * <′′ inr (inl x)) ∧
            ∃ car (λ z → imdom (tree car _<′′_ t2) z (inr (inl x)) ∧ (z <′′ inl *))
            → ⊥
        g (_ , _ , exists (inl *) (_ , ()))
        g (_ , _ , exists (inr _) (_ , ()))
        
        f : ⊥ → ¬(inr (inl x) <′′ inl *) ∧
                 ¬(inl * <′′ inr (inl x)) ∧
                 ∃ car (λ z → imdom (tree car _<′′_ t2) z (inr (inl x)) ∧ (z <′′ inl *))
        f ()

(inr (inl x)) cc′′ (inr (inl y)) = exists w ({!!} , g)
  where w : Set ℓ
        w = {!!}
        
        g : ¬(inr (inl x) <′′ inr (inl y)) ∧
            ¬(inr (inl y) <′′ inr (inl x)) ∧
            ∃ car (λ z → imdom (tree car _<′′_ t2) z (inr (inl x)) ∧ (z <′′ inr (inl y)))
            → w
        g (a , b , exists (inl *) (c , d)) = {!!}
        g (a , b , exists (inr (inl z)) ((c , d , e) , f)) = {!!}
        g (_ , _ , exists (inr (inr _)) ((_ , () , _) , _))

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