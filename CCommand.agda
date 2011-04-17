{-# OPTIONS --universe-polymorphism #-}

open import Naturals
open import Functions
open import Logic
open import Relations
open import Structures
open import InclusivenessAndDerivationality

module CCommand where







iso2 : ∀ {n} {X Y : Set n} → (One + X + Y) × (One + X + Y) → (One × One + One × X + One × Y) + (X × One + X × X + X × Y) + (Y × One + Y × X + Y × Y)
iso2 {n} = ((id +′ distl) +′ ((id {n} +′ distl) ∘′ distl) +′ ((id {n} +′ distl) ∘′ distl)) ∘′ (distl +′ distr) ∘′ distr

_↑_ : ∀ {n} → Tree n → Tree n → Tree n
_↑_ (tree X _<_ p0) (tree Y _<′_ p1) = tree (One + X + Y)
                                            (curry
                                               (((const ⊥ ▿ const ⊤ ▿ const ⊤) ▿
                                                 (const ⊥ ▿ uncurry _<_ ▿ const ⊥) ▿
                                                 (const ⊥ ▿ const ⊥ ▿ uncurry _<′_))
                                                ∘ iso2))
                                            ((λ {x} {y} {z} p → {!!}) ,
                                             ({!!} , {!!}))