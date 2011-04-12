{-# OPTIONS --universe-polymorphism #-}

open import Naturals
open import Functions
open import Logic
open import Relations
open import Structures

module LinearOrderingsAndConcatenation where



record One : Set where
  constructor *

iso : ∀ {n} {X X′ Y Y′ : Set n} → (X + Y) × (X′ + Y′) → ((X × X′) + (X × Y′)) + ((Y × X′) + (Y × Y′))
iso {n} = (distl +′ distl) ⟨ _∘_ {n} {n} {n} ⟩ distr

_++_ : Digraph → Digraph → Digraph
digraph X _~_ ++ digraph Y _~′_ = digraph (X + Y) (curry (((uncurry _~_ ▿ const ⊤) ▿ (const ⊥ ▿ uncurry _~′_)) ∘ iso))



trans-unit : Transitive {X = One} (const2 ⊥)
trans-unit {x} {y} {z} (() , ())

trich-unit : Trichotomous {X = One} (const2 ⊥)
trich-unit {x} {y} = inr (id , (inr (id , (refl *))))

linear-unit : LinearOrder (digraph One (const2 ⊥))
linear-unit = ((λ {x} {y} {z} → trans-unit {x} {y} {z}) , (λ {x} {y} → trich-unit {x} {y}))



trans-++ : (dgx : Digraph) → Transitive (Digraph.edges dgx) → (dgy : Digraph) → Transitive (Digraph.edges dgy) → Transitive (Digraph.edges (dgx ++ dgy))
trans-++ (digraph _ _~_) p1 (digraph _ _~′_) p2 {inl x} {inl y} {inl z} p3 = p1 {x} {y} {z} p3
trans-++ (digraph _ _~_) p1 (digraph _ _~′_) p2 {inl x} {inl y} {inr z} p3 = tt
trans-++ (digraph _ _~_) p1 (digraph _ _~′_) p2 {inl x} {inr y} {inl z} (_ , ())
trans-++ (digraph _ _~_) p1 (digraph _ _~′_) p2 {inl x} {inr y} {inr z} p3 = tt
trans-++ (digraph _ _~_) p1 (digraph _ _~′_) p2 {inr x} {inl y} {inl z} (() , _)
trans-++ (digraph _ _~_) p1 (digraph _ _~′_) p2 {inr x} {inl y} {inr z} (() , _)
trans-++ (digraph _ _~_) p1 (digraph _ _~′_) p2 {inr x} {inr y} {inl z} (_ , ())
trans-++ (digraph _ _~_) p1 (digraph _ _~′_) p2 {inr x} {inr y} {inr z} p3 = p2 {x} {y} {z} p3

trich-++ : ∀ {n} → (dgx : Digraph {n}) → Trichotomous (Digraph.edges dgx) → (dgy : Digraph {n}) → Trichotomous (Digraph.edges dgy) → Trichotomous (Digraph.edges (dgx ++ dgy))
trich-++ (digraph _ _~_) p1 (digraph _ _~′_) p2 {inl x} {inl y} with p1 {x} {y}
... | inl (x~y , p3) = inl (x~y , (λ p4 → p3 (inl (fst p4 , snd p4 ∘ cong inl))) ▿
                                  (p3 ∘ inr ∘ (fst ▵ uncong-+-inl ∘′ snd)))
... | inr p3 = {!!}
trich-++ (digraph _ _~_) p1 (digraph _ _~′_) p2 {inl x} {inr y} = inl (tt , fst ▿ uneq-+-inl-inr ∘′ snd)
trich-++ (digraph _ _~_) p1 (digraph _ _~′_) p2 {inr x} {inl y} = inr (id , inl (tt , uneq-+-inr-inl))
trich-++ (digraph _ _~_) p1 (digraph _ _~′_) p2 {inr x} {inr y} with p2 {x} {y}
... | inl (x~′y , p3) = inl (x~′y , (λ p4 → p3 (inl (fst p4 , snd p4 ∘ cong inr))) ▿
                                   (p3 ∘ inr ∘ (fst ▵ (uncong-+-inr ∘′ snd))))
... | inr p3 = {!!}

{-
linear-++ : (dgx : Digraph) → LinearOrder dgx → (dgy : Digraph) → LinearOrder dgy → LinearOrder (dgx ++ dgy)
linear-++ dgx p1 dgy p2 = {!!}
-}