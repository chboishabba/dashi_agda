module DASHI.Physics.QuantumVacuum.CasimirCutoffRouteSeparationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CROSS-POLLINATION / NEGATIVE RESULT
--
-- The Yang--Mills local-core lane contains a strong cutoff-removal pattern:
-- once a cutoff encloses the support of a local observable, all larger cutoffs
-- give exactly the same value.  That is an EVENTUAL-STABILITY theorem.
--
-- The Casimir spectral lane requires a different pattern: plate and reference
-- quantities may each remain cutoff-dependent while a regulated DIFFERENCE has
-- a controlled limit / finite part.  Exact stabilization and renormalised
-- cancellation must therefore remain distinct theorem classes.
------------------------------------------------------------------------

record ExactTailStabilisation
    {Cutoff Scalar : Set}
    (_≤_ : Cutoff → Cutoff → Set)
    (value : Cutoff → Scalar) : Set₁ where
  field
    threshold : Cutoff
    stableBeyondThreshold :
      (left right : Cutoff) →
      threshold ≤ left →
      threshold ≤ right →
      value left ≡ value right

open ExactTailStabilisation public

record RenormalisedDifferenceLimit
    {Cutoff Scalar Limit : Set}
    (plate reference : Cutoff → Scalar) : Set₁ where
  field
    combine : Scalar → Scalar → Scalar
    regulatedDifference : Cutoff → Scalar
    regulatedDifferenceLaw :
      (Λ : Cutoff) →
      regulatedDifference Λ ≡ combine (plate Λ) (reference Λ)

    limit : Limit
    convergenceSemantics : Set
    convergesAfterCombination : convergenceSemantics

    regulatorIndependenceSemantics : Set
    regulatorIndependentFinitePart : regulatorIndependenceSemantics

    reading : String

open RenormalisedDifferenceLimit public

------------------------------------------------------------------------
-- No generic implication is admitted in either direction.
--
-- In particular, an eventual-stability receipt for some unrelated local-core
-- observable cannot be used as a Casimir renormalisation receipt merely because
-- both are informally described as "cutoff removal".
------------------------------------------------------------------------

data ExactStabilisationAutomaticallyImpliesRenormalisedDifference : Set where

data RenormalisedDifferenceAutomaticallyImpliesExactStabilisation : Set where

exactStabilisationCannotAutoPromoteToRenormalisation :
  ExactStabilisationAutomaticallyImpliesRenormalisedDifference → ⊥
exactStabilisationCannotAutoPromoteToRenormalisation ()

renormalisationCannotAutoPromoteToExactStabilisation :
  RenormalisedDifferenceAutomaticallyImpliesExactStabilisation → ⊥
renormalisationCannotAutoPromoteToExactStabilisation ()

record CutoffRouteStatus : Set where
  field
    exactLocalCoreRouteExistsInRepo : Bool
    exactLocalCoreRouteClosesCasimirByDefinition : Bool
    casimirNeedsDifferenceLimitRoute : Bool

    exactLocalCoreRouteExistsInRepoIsTrue :
      exactLocalCoreRouteExistsInRepo ≡ true
    exactLocalCoreRouteClosesCasimirByDefinitionIsFalse :
      exactLocalCoreRouteClosesCasimirByDefinition ≡ false
    casimirNeedsDifferenceLimitRouteIsTrue :
      casimirNeedsDifferenceLimitRoute ≡ true

open CutoffRouteStatus public

canonicalCutoffRouteStatus : CutoffRouteStatus
canonicalCutoffRouteStatus =
  record
    { exactLocalCoreRouteExistsInRepo = true
    ; exactLocalCoreRouteClosesCasimirByDefinition = false
    ; casimirNeedsDifferenceLimitRoute = true
    ; exactLocalCoreRouteExistsInRepoIsTrue = refl
    ; exactLocalCoreRouteClosesCasimirByDefinitionIsFalse = refl
    ; casimirNeedsDifferenceLimitRouteIsTrue = refl
    }
