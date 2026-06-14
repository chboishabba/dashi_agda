module DASHI.Physics.Closure.GRProofArchitectureAggregationTest where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.GRConcreteLeviCivita as LeviCivita
import DASHI.Physics.Closure.GRDiscreteBianchiFiniteR as Bianchi
import DASHI.Physics.Closure.GRDiscreteRicciCandidateFromCurvature as Ricci
import DASHI.Physics.Closure.SchwarzschildLimitCandidate as Schwarzschild

------------------------------------------------------------------------
-- GR proof-architecture aggregation test.
--
-- This module checks that the current Levi-Civita, Ricci, finite-r Bianchi,
-- and Schwarzschild surfaces can be imported and threaded together without
-- adding unproved axioms or promoting any GR claim.

data GRProofArchitectureAggregationStatus : Set where
  checkedAggregationOnlyNoPromotion :
    GRProofArchitectureAggregationStatus

record GRProofArchitectureAggregationTest : Setω where
  field
    status :
      GRProofArchitectureAggregationStatus

    flatLeviCivitaSurface :
      LeviCivita.GRConcreteLeviCivitaSurface

    flatLeviCivitaResidual :
      LeviCivita.GRConcreteLeviCivitaSurface.residual flatLeviCivitaSurface
      ≡
      LeviCivita.nonFlatSelectedGRStillOpen

    flatLeviCivitaFirstMissing :
      LeviCivita.GRConcreteLeviCivitaSurface.remainingSelectedGRFirstMissing
        flatLeviCivitaSurface
      ≡
      Bianchi.missingFiniteRScalarAlgebra

    ricciCandidate :
      Ricci.GRDiscreteRicciCandidateFromCurvature

    ricciCandidateFirstMissing :
      Ricci.GRDiscreteRicciCandidateFromCurvature.firstMissing ricciCandidate
      ≡
      Ricci.missingBianchiIdentityProof

    ricciCandidateLocalContractionBoundaryOnly :
      Ricci.GRDiscreteRicciCandidateFromCurvature.localRicciContractionBoundaryOnly
        ricciCandidate
      ≡
      true

    ricciCandidateNoGlobalEagerSweep :
      Ricci.GRDiscreteRicciCandidateFromCurvature.globalEagerRicciSweepRequired
        ricciCandidate
      ≡
      false

    finiteRBianchiMissingIngredients :
      List Bianchi.GRDiscreteBianchiFiniteRMissingIngredient

    finiteRBianchiMissingIngredientsAreCanonical :
      finiteRBianchiMissingIngredients
      ≡
      Bianchi.canonicalGRDiscreteBianchiFiniteRMissingIngredients

    schwarzschildLimitCandidate :
      Schwarzschild.SchwarzschildLimitCandidateDiagnostic

    schwarzschildLimitStatusIsRequestOnly :
      Schwarzschild.SchwarzschildLimitCandidateDiagnostic.status
        schwarzschildLimitCandidate
      ≡
      Schwarzschild.requestSurfaceOnlyNoPromotion

    schwarzschildLimitFirstMissing :
      Schwarzschild.SchwarzschildLimitCandidateDiagnostic.firstMissing
        schwarzschildLimitCandidate
      ≡
      Schwarzschild.missingRadialValuation

    aggregationBoundary :
      List String

canonicalGRProofArchitectureAggregationTest :
  GRProofArchitectureAggregationTest
canonicalGRProofArchitectureAggregationTest =
  record
    { status =
        checkedAggregationOnlyNoPromotion
    ; flatLeviCivitaSurface =
        LeviCivita.canonicalGRConcreteLeviCivitaSurface
    ; flatLeviCivitaResidual =
        LeviCivita.grConcreteLeviCivitaResidualIsNonFlat
    ; flatLeviCivitaFirstMissing =
        LeviCivita.grConcreteLeviCivitaFirstMissingIsFiniteRScalarAlgebra
    ; ricciCandidate =
        Ricci.canonicalGRDiscreteRicciCandidateFromCurvature
    ; ricciCandidateFirstMissing =
        Ricci.grDiscreteRicciCandidateFirstMissing
    ; ricciCandidateLocalContractionBoundaryOnly =
        Ricci.grDiscreteRicciCandidateContractionBoundaryOnly
    ; ricciCandidateNoGlobalEagerSweep =
        Ricci.grDiscreteRicciCandidateNoGlobalEagerRicciSweep
    ; finiteRBianchiMissingIngredients =
        Bianchi.canonicalGRDiscreteBianchiFiniteRMissingIngredients
    ; finiteRBianchiMissingIngredientsAreCanonical =
        refl
    ; schwarzschildLimitCandidate =
        Schwarzschild.canonicalSchwarzschildLimitCandidateDiagnostic
    ; schwarzschildLimitStatusIsRequestOnly =
        Schwarzschild.schwarzschildLimitStatusIsRequestOnly
    ; schwarzschildLimitFirstMissing =
        Schwarzschild.schwarzschildLimitExactFirstMissing
    ; aggregationBoundary =
        "Imports and checks the flat Levi-Civita prerequisite surface"
        ∷ "Imports and checks the Ricci candidate boundary-only local contraction surface"
        ∷ "Imports and checks the finite-r Bianchi missing-ingredient index"
        ∷ "Imports and checks the Schwarzschild request surface first missing primitive"
        ∷ "No GR, Schwarzschild, Bianchi, or Einstein-equation promotion is introduced here"
        ∷ []
    }

grProofArchitectureAggregationStatus :
  GRProofArchitectureAggregationTest.status
    canonicalGRProofArchitectureAggregationTest
  ≡
  checkedAggregationOnlyNoPromotion
grProofArchitectureAggregationStatus = refl

grProofArchitectureAggregationRicciFirstMissing :
  GRProofArchitectureAggregationTest.ricciCandidateFirstMissing
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.grDiscreteRicciCandidateFirstMissing
grProofArchitectureAggregationRicciFirstMissing = refl

grProofArchitectureAggregationSchwarzschildFirstMissing :
  GRProofArchitectureAggregationTest.schwarzschildLimitFirstMissing
    canonicalGRProofArchitectureAggregationTest
  ≡
  Schwarzschild.schwarzschildLimitExactFirstMissing
grProofArchitectureAggregationSchwarzschildFirstMissing = refl
