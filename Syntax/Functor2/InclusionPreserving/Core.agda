open import Level

open import Syntax.Functor2.Core
open import Syntax.Inclusiveness.Core

module Syntax.Functor2.InclusionPreserving.Core where



record InclusionPreservingBifunctor : Set₁ where
  constructor inclusionPreservingBifunctor
  field
    underlying : Bifunctor {zero}
    isInclusionPreservingOperation : IsInclusionPreservingOperation (Bifunctor._*_ underlying)