{-# OPTIONS --universe-polymorphism #-}

open import Naturals
open import Functions
open import Logic
open import Relations
open import Structures
open import InclusivenessAndDerivationality

module LinearOrderingsAndConcatenation where



iso : ∀ {n} {X X′ Y Y′ : Set n}
      → (X + Y) × (X′ + Y′)
      → ((X × X′) + (X × Y′)) + ((Y × X′) + (Y × Y′))
iso {n} = (distl +′ distl) ⟨ _∘_ {n} {n} {n} ⟩ distr

_++_ : ∀ {n} → Digraph n → Digraph n → Digraph n
digraph X _~_ ++ digraph Y _~′_ = digraph (X + Y) (curry (((uncurry _~_ ▿ const ⊤) ▿ (const ⊥ ▿ uncurry _~′_)) ∘ iso))


trans-unit : ∀ {n} → Transitive {X = One {n}} (const2 ⊥)
trans-unit {n} {x} {y} {z} (() , ())

trich-unit : ∀ {n} → Trichotomous {X = One {n}} (const2 ⊥)
trich-unit {n} {x} {y} = inr (id , (inr (id , (refl *))))

linear-unit : ∀ {n} → IsLinearOrder (digraph (One {n}) (const2 ⊥))
linear-unit {n} = ((λ {x} {y} {z} → trans-unit {n} {x} {y} {z}) , (λ {x} {y} → trich-unit {n} {x} {y}))


trans-++ : ∀ {n} → (dgx : Digraph n) → Transitive (Digraph.edges dgx)
                 → (dgy : Digraph n) → Transitive (Digraph.edges dgy)
                 → Transitive (Digraph.edges (dgx ++ dgy))
trans-++ (digraph _ _~_) p1 (digraph _ _~′_) p2 {inl x} {inl y} {inl z} p3 = p1 {x} {y} {z} p3
trans-++ (digraph _ _~_) p1 (digraph _ _~′_) p2 {inl x} {inl y} {inr z} p3 = tt
trans-++ (digraph _ _~_) p1 (digraph _ _~′_) p2 {inl x} {inr y} {inl z} (_ , ())
trans-++ (digraph _ _~_) p1 (digraph _ _~′_) p2 {inl x} {inr y} {inr z} p3 = tt
trans-++ (digraph _ _~_) p1 (digraph _ _~′_) p2 {inr x} {inl y} {inl z} (() , _)
trans-++ (digraph _ _~_) p1 (digraph _ _~′_) p2 {inr x} {inl y} {inr z} (() , _)
trans-++ (digraph _ _~_) p1 (digraph _ _~′_) p2 {inr x} {inr y} {inl z} (_ , ())
trans-++ (digraph _ _~_) p1 (digraph _ _~′_) p2 {inr x} {inr y} {inr z} p3 = p2 {x} {y} {z} p3

trich-++ : ∀ {n} → (dgx : Digraph n) → Trichotomous (Digraph.edges dgx)
                 → (dgy : Digraph n) → Trichotomous (Digraph.edges dgy)
                 → Trichotomous (Digraph.edges (dgx ++ dgy))
trich-++ (digraph _ _~_) p1 (digraph _ _~′_) p2 {inl x} {inl y} with p1 {x} {y}
... | inl (x~y , p3) = inl (x~y , (λ p4 → p3 (inl (fst p4 , snd p4 ∘ cong inl))) ▿
                                  (p3 ∘ inr ∘ (fst ▵ uncong-+-inl ∘′ snd)))
... | inr (x~y→⊥ , inl (y~x , x==y→⊥)) = inr (x~y→⊥ , inl (y~x , λ inlx==inly → x==y→⊥ (uncong-+-inl inlx==inly)))
... | inr (x~y→⊥ , inr (y~x→⊥ , x==y)) = inr (x~y→⊥ , inr (y~x→⊥ , cong inl x==y))
trich-++ (digraph _ _~_) p1 (digraph _ _~′_) p2 {inl x} {inr y} = inl (tt , fst ▿ uneq-+-inl-inr ∘′ snd)
trich-++ (digraph _ _~_) p1 (digraph _ _~′_) p2 {inr x} {inl y} = inr (id , inl (tt , uneq-+-inr-inl))
trich-++ (digraph _ _~_) p1 (digraph _ _~′_) p2 {inr x} {inr y} with p2 {x} {y}
... | inl (x~′y , p3) = inl (x~′y , (λ p4 → p3 (inl (fst p4 , snd p4 ∘ cong inr))) ▿
                                   (p3 ∘ inr ∘ (fst ▵ (uncong-+-inr ∘′ snd))))
... | inr (x~′y→⊥ , inl (y~′x , x==y→⊥)) = inr (x~′y→⊥ , inl (y~′x , λ inrx==inry → x==y→⊥ (uncong-+-inr inrx==inry)))
... | inr (x~′y→⊥ , inr (y~′x→⊥ , x==y)) = inr (x~′y→⊥ , inr (y~′x→⊥ , cong inr x==y))

linear-++ : ∀ {n} → (dgx : Digraph n) → IsLinearOrder dgx
                  → (dgy : Digraph n) → IsLinearOrder dgy
                  → IsLinearOrder (dgx ++ dgy)
linear-++ dgx (p1 , p2) dgy (p3 , p4) = ((λ {x} {y} {z} → trans-++ dgx p1 dgy p3 {x} {y} {z}) ,
                                         (λ {x} {y} → trich-++ dgx p2 dgy p4 {x} {y}))

_l++_ : ∀ {n} → LinearOrder n → LinearOrder n → LinearOrder n
(linear-order X _<_ p) l++ (linear-order Y _<′_ q) = linear-order (X + Y)
                                                                  (curry (((uncurry _<_ ▿ const ⊤) ▿ (const ⊥ ▿ uncurry _<′_)) ∘ iso))
                                                                  (linear-++ (digraph X _<_) p (digraph Y _<′_) q)

l++-inclusiveness : ∀ {n} {X Y : LinearOrder n}
                    → Preserves₁ {n} {LinearOrder n} {X} {Y} _l++_ LinearOrder.carrier id LinearOrder._<_
l++-inclusiveness = ((λ {x} {y} → (id , id)) ,
                     (λ {x} {y} → (id , id)))

-- Prove that a definition of _<_ under _++_ as something quantificationally (e.g. ∀ {x y : X + Y} → x < y ↔ ...) is a linear ordering