open import Data.Product
open import Level
open import Relation.Binary.PropositionalEquality

open import Syntax.Functor2.Core

module Syntax.Functor2.Product where

×-Bifunctor : Bifunctor {zero}
×-Bifunctor = record { _*_ = _×_
                     ; fmap = λ f g xy → (f (proj₁ xy) , g (proj₂ xy))
                     ; isBifunctor = (λ {_} {_} {_} → refl) , (λ {_} {_} {_} → refl)
                     }