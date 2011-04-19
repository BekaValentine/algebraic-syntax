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
lem-irref-comb _<_ p0 _<′_ p1 p2 = p0 (λ {x} → p2 {inr (inl x)})


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
              

_↑_ : ∀ {n} → SingleDominanceTree n → SingleDominanceTree n → SingleDominanceTree n
_↑_ (sdtree X _<_ (t0 , i0 , p0) sd0) (sdtree Y _<′_ (t1 , i1 , p1) sd1) = let t2 = ((λ {x} {y} {z} p → lem-trans-comb _<_ t0 _<′_ t1 {x} {y} {z} p) ,
                                                                                    lem-irref-comb _<_ i0 _<′_ i1 ,
                                                                                    exists (inl *) (lem-rooted-comb _<_ _<′_)) in
                                                                               sdtree (One + X + Y)
                                                                                  (comb _<_ _<′_)
                                                                                  t2
                                                                                  (lem-sd-comb _<_ ((λ {x} {y} {z} → t0 {x} {y} {z}) , i0 , p0) sd0
                                                                                               _<′_ ((λ {x} {y} {z} → t1 {x} {y} {z}) , i1 , p1) sd1
                                                                                               t2)

postulate ℓ : ℕ
postulate X Y : Set ℓ
postulate _<_ : Rel X ℓ
postulate t0 : IsTree (digraph X _<_)
postulate sd0 : IsSingleDominanceTree (tree X _<_ t0)
postulate _<′_ : Rel Y ℓ
postulate t1 : IsTree (digraph Y _<′_)
postulate sd1 : IsSingleDominanceTree (tree Y _<′_ t1)

sdt0 : SingleDominanceTree ℓ
sdt0 = sdtree X _<_ t0 sd0

postulate _cc_ : Rel X ℓ
postulate p0 : IsCCommandRel sdt0 _cc_

sdt1 : SingleDominanceTree ℓ
sdt1 = sdtree Y _<′_ t1 sd1

postulate _cc′_ : Rel Y ℓ
postulate p1 : IsCCommandRel sdt1 _cc′_

sdt2 : SingleDominanceTree ℓ
sdt2 = sdt0 ↑ sdt1

car : Set ℓ
car = SingleDominanceTree.carrier sdt2

_<′′_ : Rel car ℓ
_<′′_ = SingleDominanceTree._<_ sdt2

t2 : IsTree (digraph car _<′′_)
t2 = SingleDominanceTree.isTree sdt2

sd2 : IsSingleDominanceTree (tree car _<′′_ t2)
sd2 = SingleDominanceTree.isSingleDominanceTree sdt2

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

(inr (inl x)) cc′′ (inr (inl y)) = exists w ({!!} , {!!})
  where w : Set ℓ
        w = {!!}
        
        g : ¬(inr (inl x) <′′ inr (inl y)) ∧
            ¬(inr (inl y) <′′ inr (inl x)) ∧
            ∃ car (λ z → imdom (tree car _<′′_ t2) z (inr (inl x)) ∧ (z <′′ inr (inl y)))
            → w
        g (a , b , exists (inl *) ((c , d , e) , f)) = {!!}
        g (a , b , exists (inr (inl z)) ((c , d , e) , f)) = {!!}
        g (_ , _ , exists (inr (inr _)) ((_ , () , _) , _))

(inr (inl x)) cc′′ (inr (inr y)) = {!!}

(inr (inr x)) cc′′ y = {!!}