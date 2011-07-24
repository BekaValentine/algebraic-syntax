open import Data.Product

open import Functor2.Product
open import Functor2.InclusionPreserving.Core
open import Syntax.Inclusiveness.Core

module Functor2.InclusionPreserving.Product where

×-InclusionPreservingBifunctor : InclusionPreservingBifunctor
×-InclusionPreservingBifunctor = record { underlying = ×-Bifunctor
                                        ; isInclusionPreservingOperation = leftInc , rightInc
                                        }
  where leftInc : IsLeftInclusionPreservingOperation _×_
        leftInc l r l' r'
                (inclusiveRelation p isIncP)
                (inclusiveRelation q isIncQ)
                x y z w = map (proj₁ (proj₁ isIncP l r) x y)
                              (proj₁ (proj₁ isIncQ l' r') z w) ,
                          map (proj₂ (proj₁ isIncP l r) x y)
                              (proj₂ (proj₁ isIncQ l' r') z w)
        
        rightInc : IsRightInclusionPreservingOperation _×_
        rightInc l r l' r'
                 (inclusiveRelation p isIncP)
                 (inclusiveRelation q isIncQ)
                 x y z w = map (proj₁ (proj₂ isIncP l r) x y)
                               (proj₁ (proj₂ isIncQ l' r') z w) ,
                           map (proj₂ (proj₂ isIncP l r) x y)
                               (proj₂ (proj₂ isIncQ l' r') z w)