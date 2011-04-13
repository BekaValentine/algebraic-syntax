{-# OPTIONS --universe-polymorphism #-}

open import Naturals
open import Functions
open import Logic
open import Relations
open import Structures

module CCommand where



iso2 : ∀ {n} {X Y : Set n} → (One + X + Y) × (One + X + Y) → (One × One + One × X + One × Y) + (X × One + X × X + X × Y) + (Y × One + Y × X + Y × Y)
iso2 {n} = ((id +′ distl) +′ ((id {n} +′ distl) ∘′ distl) +′ ((id {n} +′ distl) ∘′ distl)) ∘′ (distl +′ distr) ∘′ distr

_↑_ : ∀ {n} → SingleDominanceTree n → SingleDominanceTree n → SingleDominanceTree n
sdtree (tree (digraph X _<_) p1 ) p2 ↑ sdtree (tree (digraph Y _<′_) p3) p4 = sdtree (tree (digraph (One + X + Y) (curry (((const ⊥ ▿ const ⊤ ▿ const ⊤) ▿ (const ⊥ ▿ uncurry _<_ ▿ const ⊥) ▿ (const ⊥ ▿ const ⊥ ▿ uncurry _<′_)) ∘ iso2))) (exists (inl *) ({!!} +′ {!!}))) {!!}



--cc-unit : IsCCommandRel unit-sdtree (const2 ⊥)