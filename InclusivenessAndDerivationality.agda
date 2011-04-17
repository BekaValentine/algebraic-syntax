{-# OPTIONS --universe-polymorphism #-}

open import Naturals
open import Functions
open import Logic
open import Relations
open import Structures

module InclusivenessAndDerivationality where



-- inclusiveness of relations over structured sets
Preserves₁ : ∀ {ℓ} {T : Set (suc ℓ)} {X Y : T}
             → (_~_ : T → T → T)
             → (carrier : T → Set ℓ)
             → (inj : carrier X + carrier Y → carrier (X ~ Y))
             → (rel : (Z : T) → Rel (carrier Z) ℓ)
             → Set ℓ
Preserves₁ {_} {_} {X} {Y} _~_ carrier inj rel = (∀ {x y : carrier X}
                                                  → rel (X ~ Y) (inj (inl x)) (inj (inl y)) ↔ rel X x y) ∧
                                                 (∀ {x y : carrier Y}
                                                  → rel (X ~ Y) (inj (inr x)) (inj (inr y)) ↔ rel Y x y)

-- derivationality of relations over structured sets
DerivesFrom₁ : ∀ {ℓ} {T : Set (suc ℓ)} {X Y : T}
               → (_~_ : T → T → T)
               → (carrier : T → Set ℓ)
               → (inj : carrier X + carrier Y → carrier (X ~ Y))
               → (postrel : (Z : T) → Rel (carrier Z) ℓ)
               → (prerel : (Z : T) → Rel (carrier Z) ℓ)
               → Set ℓ
DerivesFrom₁ {_} {_} {X} {Y} _~_ carrier inj postrel prerel = (∀ {x y : carrier X}
                                                               → postrel (X ~ Y) (inj (inl x)) (inj (inl y))
                                                               → prerel X x y) ∧
                                                              (∀ {x y : carrier Y}
                                                               → postrel (X ~ Y) (inj (inr x)) (inj (inr y))
                                                               → prerel Y x y)

lemma-Preserves₁→DerivesFrom₁ : ∀ {ℓ} {T : Set (suc ℓ)} {X Y : T}
                                → (_~_ : T → T → T)
                                → (carrier : T → Set ℓ)
                                → (inj : carrier X + carrier Y → carrier (X ~ Y))
                                → (rel : (Z : T) → Rel (carrier Z) ℓ)
                                → Preserves₁ {ℓ} {T} {X} {Y} _~_ carrier inj rel
                                → DerivesFrom₁ {ℓ} {T} {X} {Y} _~_ carrier inj rel rel
lemma-Preserves₁→DerivesFrom₁ _~_ carrier inj rel (p0 , p1) = ((λ {x} {y} → fst (p0 {x} {y})) ,
                                                               (λ {x} {y} → fst (p1 {x} {y})))



-- inclusiveness of properties of pointed sets
Preserves₂ : ∀ {n} {T : Set (suc n)} {X Y : T} {R : Set n}
             → (_~_ : T → T → T)
             → (carrier : T → Set n)
             → (fun : (Z : T) → carrier Z → R)
             → (comb : R × R → R)
             → (acc : R → R × R)
             → (point : (Z : T) → carrier Z)
             → Set n
Preserves₂ {_} {_} {X} {Y} _~_ carrier fun comb acc point = (comb (fun X (point X) , fun Y (point Y)) == fun (X ~ Y) (point (X ~ Y))) ∧
                                                            ((fun X (point X) , fun Y (point Y)) == acc (fun (X ~ Y) (point (X ~ Y))))

-- derivationality of properties of pointed sets
DerivesFrom₂ : ∀ {n} {T : Set (suc n)} {X Y : T} {R : Set n}
               → (_~_ : T → T → T)
               → (carrier : T → Set n)
               → (fun : (Z : T) → carrier Z → R)
               → (comb : R × R → R)
               → (point : (Z : T) → carrier Z)
               → Set n
DerivesFrom₂ {_} {_} {X} {Y} _~_ carrier fun comb point = comb ((fun X (point X)) , (fun Y (point Y))) == fun (X ~ Y) (point (X ~ Y))

lemma-Preserves₂→DerivesFrom₂ : ∀ {n} {T : Set (suc n)} {X Y : T} {R : Set n}
                                → (_~_ : T → T → T)
                                → (carrier : T → Set n)
                                → (fun : (Z : T) → carrier Z → R)
                                → (comb : R × R → R)
                                → (acc : R → R × R)
                                → (point : (Z : T) → carrier Z)
                                → Preserves₂ {n} {T} {X} {Y} _~_ carrier fun comb acc point
                                → DerivesFrom₂ {n} {T} {X} {Y} _~_ carrier fun comb point
--lemma-Preserves₂→DerivesFrom₂ _~_ carrier fun comb acc point (p0 , p1) = p0
lemma-Preserves₂→DerivesFrom₂ _~_ carrier fun comb acc point = fst