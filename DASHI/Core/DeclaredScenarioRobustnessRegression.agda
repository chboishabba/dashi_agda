module DASHI.Core.DeclaredScenarioRobustnessRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)

import DASHI.Core.DeclaredScenarioRobustnessExact as Declared

------------------------------------------------------------------------
-- Universal obligations may always be weakened to the declared ensemble.
------------------------------------------------------------------------

data Plan : Set where plan : Plan

data Future : Set where declaredFuture outsideFuture : Future

data Acceptable : Plan → Future → Set where
  declaredAccepted : Acceptable plan declaredFuture
  outsideAccepted : Acceptable plan outsideFuture

universalAcceptable : (future : Future) → Acceptable plan future
universalAcceptable declaredFuture = declaredAccepted
universalAcceptable outsideFuture = outsideAccepted

declaredEnsemble : List Future
declaredEnsemble = declaredFuture ∷ []

universalWeakensToDeclared :
  Declared.RobustOnDeclared Acceptable plan declaredEnsemble
universalWeakensToDeclared =
  Declared.fromUniversalObligation universalAcceptable

------------------------------------------------------------------------
-- The declared interface deliberately does not produce obligations for an
-- out-of-ensemble future merely from its local membership-indexed receipt.
------------------------------------------------------------------------

data DeclaredOnlyAcceptable : Plan → Future → Set where
  onlyDeclaredAccepted : DeclaredOnlyAcceptable plan declaredFuture

declaredOnly :
  Declared.RobustOnDeclared DeclaredOnlyAcceptable plan declaredEnsemble
declaredOnly =
  Declared.robustOnDeclared
    (λ { declaredFuture _ → onlyDeclaredAccepted ; outsideFuture () })

outsideNotRecovered :
  ((future : Future) → DeclaredOnlyAcceptable plan future) → ⊥
outsideNotRecovered universal with universal outsideFuture
... | ()
