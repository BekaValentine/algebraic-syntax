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
comb _<_ _<′_ (inr (inl x)) (inr (inr y)) = ⊥
comb _<_ _<′_ (inr (inr x)) (inr (inl y)) = ⊥
comb _<_ _<′_ (inr (inr x)) (inr (inr y)) = x <′ y


lem-trans-comb : ∀ {ℓ} {X Y : Set ℓ}
                 → (_<_ : Rel X ℓ)
                 → Transitive _<_
                 → (_<′_ : Rel Y ℓ)
                 → Transitive _<′_
                 → Transitive (comb _<_ _<′_)
lem-trans-comb _<_ p0 _<′_ p1 {inl x} {inl y} {inl z} (() , ())
lem-trans-comb _<_ p0 _<′_ p1 {inl x} {inl y} {inr z} (() , _)
lem-trans-comb _<_ p0 _<′_ p1 {inl x} {inr (inl y)} {inl z} (_ , ())
lem-trans-comb _<_ p0 _<′_ p1 {inl x} {inr (inr y)} {inl z} (_ , ())
lem-trans-comb _<_ p0 _<′_ p1 {inl x} {inr (inl y)} {inr (inl z)} (p2 , p3) = tt
lem-trans-comb _<_ p0 _<′_ p1 {inl x} {inr (inl y)} {inr (inr z)} (p2 , p3) = tt
lem-trans-comb _<_ p0 _<′_ p1 {inl x} {inr (inr y)} {inr (inl z)} (p2 , p3) = tt
lem-trans-comb _<_ p0 _<′_ p1 {inl x} {inr (inr y)} {inr (inr z)} (p2 , p3) = tt
lem-trans-comb _<_ p0 _<′_ p1 {inr x} {inl y} {inl z} (_ , ())
lem-trans-comb _<_ p0 _<′_ p1 {inr (inl x)} {inl y} {inr (inl z)} (() , _)
lem-trans-comb _<_ p0 _<′_ p1 {inr (inl x)} {inl y} {inr (inr z)} (() , _)
lem-trans-comb _<_ p0 _<′_ p1 {inr (inr x)} {inl y} {inr (inl z)} (() , _)
lem-trans-comb _<_ p0 _<′_ p1 {inr (inr x)} {inl y} {inr (inr z)} (() , _)
lem-trans-comb _<_ p0 _<′_ p1 {inr (inl x)} {inr (inl y)} {inl z} (_ , ())
lem-trans-comb _<_ p0 _<′_ p1 {inr (inl x)} {inr (inr y)} {inl z} (() , ())
lem-trans-comb _<_ p0 _<′_ p1 {inr (inr x)} {inr (inl y)} {inl z} (() , ())
lem-trans-comb _<_ p0 _<′_ p1 {inr (inr x)} {inr (inr y)} {inl z} (_ , ())
lem-trans-comb _<_ p0 _<′_ p1 {inr (inl x)} {inr (inl y)} {inr (inl z)} p2 = p0 p2
lem-trans-comb _<_ p0 _<′_ p1 {inr (inl x)} {inr (inl y)} {inr (inr z)} (_ , ())
lem-trans-comb _<_ p0 _<′_ p1 {inr (inl x)} {inr (inr y)} {inr (inl z)} (() , ())
lem-trans-comb _<_ p0 _<′_ p1 {inr (inl x)} {inr (inr y)} {inr (inr z)} (() , _)
lem-trans-comb _<_ p0 _<′_ p1 {inr (inr x)} {inr (inl y)} {inr (inl z)} (() , _)
lem-trans-comb _<_ p0 _<′_ p1 {inr (inr x)} {inr (inl y)} {inr (inr z)} (() , ())
lem-trans-comb _<_ p0 _<′_ p1 {inr (inr x)} {inr (inr y)} {inr (inl z)} (_ , ())
lem-trans-comb _<_ p0 _<′_ p1 {inr (inr x)} {inr (inr y)} {inr (inr z)} p2 = p1 p2

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
{-
lem-cc : ∀ {ℓ} {X Y : Set ℓ}
         → (_cc_ : Rel X ℓ)
         → IsCCommandRel _cc_
         → (_cc′_ : Rel Y ℓ)
         → IsCCommandRel _cc′_
         → ∃ (Rel X ℓ → Rel Y ℓ → Rel (One + X + Y) ℓ) (λ f → IsCCommandRel (f _cc_ _cc′_))
lem-cc _cc_ p0 _cc′_ p1 = ?
-}