{-# OPTIONS --universe-polymorphism #-}

open import Data.Product
open import Function
open import Level
open import Relation.Binary.PropositionalEquality

module Functor2.Core where



IdentityFunctorLaw : {ℓ : Level}
                   → (F : Set ℓ → Set ℓ) 
                   → ({A B : Set ℓ} → (A → B) → F A → F B)
                   → Set (suc ℓ)
IdentityFunctorLaw {ℓ} F fmap = ∀ {A : Set ℓ} {x : F A} → fmap id x ≡ x

CompositionFunctorLaw : {ℓ : Level}
                      → (F : Set ℓ → Set ℓ) 
                      → ({A B : Set ℓ} → (A → B) → F A → F B)
                      → Set (suc ℓ)
CompositionFunctorLaw {ℓ} F fmap = ∀ {A B C : Set ℓ} {x : F A} {f : B → C} {g : A → B}
                                   → fmap f (fmap g x) ≡ fmap (f ∘ g) x

IsFunctor : {ℓ : Level}
          → (F : Set ℓ → Set ℓ) 
          → ({A B : Set ℓ} → (A → B) → F A → F B)
          → Set (suc ℓ)
IsFunctor F fmap = IdentityFunctorLaw F fmap × CompositionFunctorLaw F fmap

record Functor {ℓ : Level} : Set (suc ℓ) where
  constructor functor
  field
    F : Set ℓ → Set ℓ
    fmap : {A B : Set ℓ} → (A → B) → F A → F B
    isFunctor : IsFunctor F fmap

IdentityBifunctorLaw : {ℓ : Level}
                     → (_*_ : Set ℓ → Set ℓ → Set ℓ)
                     → ({A B C D : Set ℓ} → (A → B) → (C → D) → (A * C → B * D))
                     → Set (suc ℓ)
IdentityBifunctorLaw {ℓ} _*_ fmap = ∀ {A B : Set ℓ} {x : A * B} → fmap id id x ≡ x

CompositionBifunctorLaw : {ℓ : Level}
                        → (_*_ : Set ℓ → Set ℓ → Set ℓ)
                        → ({A B C D : Set ℓ} → (A → B) → (C → D) → (A * C → B * D))
                        → Set (suc ℓ)
CompositionBifunctorLaw {ℓ} _*_ fmap = {A B C D E F : Set ℓ} {x : A * D} {f : B → C} {g : A → B} {h : E → F} {k : D → E}
                                     → fmap f h (fmap g k x) ≡ fmap (f ∘ g) (h ∘ k) x

IsBifunctor : {ℓ : Level}
            → (_*_ : Set ℓ → Set ℓ → Set ℓ)
            → ({A B C D : Set ℓ} → (A → B) → (C → D) → (A * C → B * D))
            → Set (suc ℓ)
IsBifunctor _*_ fmap = IdentityBifunctorLaw _*_ fmap × CompositionBifunctorLaw _*_ fmap

record Bifunctor {ℓ : Level} : Set (suc ℓ) where
  constructor bifunctor
  field
    _*_ : Set ℓ → Set ℓ → Set ℓ
    fmap : {A B C D : Set ℓ} → (A → B) → (C → D) → A * C → B * D
    isBifunctor : IsBifunctor _*_ fmap