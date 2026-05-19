module DASHI.Physics.Closure.DiscreteEinsteinVacuumLimitSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.DiscreteConnectionCandidateFromCRT as DCRT
import DASHI.Physics.Closure.DiscreteEinsteinTensorCandidate as DET
import DASHI.Physics.Closure.DiscreteEinsteinTensorNextThreadIndex as DETIndex
import DASHI.Physics.Closure.EinsteinEquationCandidate as EEC
import DASHI.Physics.Closure.GRDiscreteBianchiFiniteR as GRBianchi
import DASHI.Physics.Closure.GRNonFlatScalarAlgebraSurface as NFScalar
import DASHI.Physics.Closure.GRSelectedNonFlatMetricInstance as SelectedGR

------------------------------------------------------------------------
-- Vacuum-limit / Christoffel off-resonance lane.
--
-- This surface records the exact result of the current repository search.
-- The repo contains flat-vacuum and flat-Minkowski prerequisite surfaces, a
-- selected finite-r scalar/metric dependency, and several diagnostic-only
-- Einstein-tensor/connection indices.  It does not currently contain a law
-- of the form christoffelVanishesOffResonance, nor the downstream zero
-- propagation needed to promote a vacuum Einstein tensor theorem.

data DiscreteEinsteinVacuumLimitStatus : Set where
  blockedBeforeOffResonanceChristoffelZero :
    DiscreteEinsteinVacuumLimitStatus

data DiscreteEinsteinVacuumLimitMissingPrimitive : Set where
  missingChristoffelVanishesOffResonance :
    DiscreteEinsteinVacuumLimitMissingPrimitive

  missingRiemannFromChristoffelZero :
    DiscreteEinsteinVacuumLimitMissingPrimitive

  missingRicciContractionFromRiemannZero :
    DiscreteEinsteinVacuumLimitMissingPrimitive

  missingEinsteinTensorZeroFromRicciZero :
    DiscreteEinsteinVacuumLimitMissingPrimitive

canonicalDiscreteEinsteinVacuumLimitMissingPrimitives :
  List DiscreteEinsteinVacuumLimitMissingPrimitive
canonicalDiscreteEinsteinVacuumLimitMissingPrimitives =
  missingChristoffelVanishesOffResonance
  ∷ missingRiemannFromChristoffelZero
  ∷ missingRicciContractionFromRiemannZero
  ∷ missingEinsteinTensorZeroFromRicciZero
  ∷ []

data DiscreteEinsteinVacuumLimitUnsupportedClaim : Set where
  unsupportedVacuumAutomaticClaim :
    DiscreteEinsteinVacuumLimitUnsupportedClaim

  unsupportedOffResonanceChristoffelZeroClaim :
    DiscreteEinsteinVacuumLimitUnsupportedClaim

  unsupportedRiemannZeroClaim :
    DiscreteEinsteinVacuumLimitUnsupportedClaim

  unsupportedRicciZeroClaim :
    DiscreteEinsteinVacuumLimitUnsupportedClaim

  unsupportedEinsteinTensorZeroClaim :
    DiscreteEinsteinVacuumLimitUnsupportedClaim

canonicalDiscreteEinsteinVacuumLimitUnsupportedClaims :
  List DiscreteEinsteinVacuumLimitUnsupportedClaim
canonicalDiscreteEinsteinVacuumLimitUnsupportedClaims =
  unsupportedVacuumAutomaticClaim
  ∷ unsupportedOffResonanceChristoffelZeroClaim
  ∷ unsupportedRiemannZeroClaim
  ∷ unsupportedRicciZeroClaim
  ∷ unsupportedEinsteinTensorZeroClaim
  ∷ []

record DiscreteEinsteinVacuumLimitSurface : Setω where
  field
    status :
      DiscreteEinsteinVacuumLimitStatus

    discreteEinsteinTensorDiagnostic :
      DET.DiscreteEinsteinTensorCandidateDiagnostic

    crtConnectionDiagnostic :
      DCRT.DiscreteConnectionCandidateFromCRTDiagnostic

    nextThreadIndex :
      DETIndex.DiscreteEinsteinTensorNextThreadIndex

    finiteRScalarOperations :
      NFScalar.GRCarrierScalarOperations

    selectedNonFlatMetricSurface :
      SelectedGR.GRSelectedNonFlatMetricInstanceSurface

    finiteRBianchiMissingIngredients :
      List GRBianchi.GRDiscreteBianchiFiniteRMissingIngredient

    flatVacuumEinsteinEquationObligation :
      EEC.EinsteinEquationCandidateObligationSurface

    suppliedSurface :
      List String

    firstMissingPrimitive :
      DiscreteEinsteinVacuumLimitMissingPrimitive

    firstMissingPrimitiveIsChristoffelOffResonance :
      firstMissingPrimitive
      ≡
      missingChristoffelVanishesOffResonance

    orderedMissingPrimitives :
      List DiscreteEinsteinVacuumLimitMissingPrimitive

    orderedMissingPrimitivesAreCanonical :
      orderedMissingPrimitives
      ≡
      canonicalDiscreteEinsteinVacuumLimitMissingPrimitives

    inheritedDiscreteEinsteinFirstMissing :
      DET.DiscreteEinsteinTensorFirstMissingCondition

    inheritedDiscreteEinsteinFirstMissingIsCRTConnection :
      inheritedDiscreteEinsteinFirstMissing
      ≡
      DET.missingCarrierInternalNonFlatConnectionFromCRT

    inheritedSelectedGRFirstMissing :
      SelectedGR.GRSelectedNonFlatMetricFirstMissingLaw

    inheritedSelectedGRFirstMissingIsChristoffelFromMetric :
      inheritedSelectedGRFirstMissing
      ≡
      SelectedGR.missingSelectedChristoffelFromMetricLaw

    unsupportedClaims :
      List DiscreteEinsteinVacuumLimitUnsupportedClaim

    unsupportedClaimsAreCanonical :
      unsupportedClaims
      ≡
      canonicalDiscreteEinsteinVacuumLimitUnsupportedClaims

    exactBlockerReport :
      List String

    nonPromotionBoundary :
      List String

canonicalDiscreteEinsteinVacuumLimitSurface :
  DiscreteEinsteinVacuumLimitSurface
canonicalDiscreteEinsteinVacuumLimitSurface =
  record
    { status =
        blockedBeforeOffResonanceChristoffelZero
    ; discreteEinsteinTensorDiagnostic =
        DET.canonicalDiscreteEinsteinTensorCandidateDiagnostic
    ; crtConnectionDiagnostic =
        DCRT.canonicalDiscreteConnectionCandidateFromCRTDiagnostic
    ; nextThreadIndex =
        DETIndex.canonicalDiscreteEinsteinTensorNextThreadIndex
    ; finiteRScalarOperations =
        NFScalar.canonicalGRFiniteRCarrierScalarOperations
    ; selectedNonFlatMetricSurface =
        SelectedGR.canonicalGRSelectedNonFlatMetricInstanceSurface
    ; finiteRBianchiMissingIngredients =
        GRBianchi.canonicalGRDiscreteBianchiFiniteRMissingIngredients
    ; flatVacuumEinsteinEquationObligation =
        EEC.canonicalEinsteinEquationCandidateObligationSurface
    ; suppliedSurface =
        "Flat-vacuum surface in EinsteinEquationCandidate"
        ∷ "Flat Minkowski discrete Einstein tensor diagnostic"
        ∷ "CRT/J connection diagnostic with no carrier-internal connection"
        ∷ "Finite-r scalar operation table"
        ∷ "Selected non-flat metric dependency with placeholder Christoffel slot"
        ∷ "Finite-r Bianchi missing-ingredient index"
        ∷ []
    ; firstMissingPrimitive =
        missingChristoffelVanishesOffResonance
    ; firstMissingPrimitiveIsChristoffelOffResonance =
        refl
    ; orderedMissingPrimitives =
        canonicalDiscreteEinsteinVacuumLimitMissingPrimitives
    ; orderedMissingPrimitivesAreCanonical =
        refl
    ; inheritedDiscreteEinsteinFirstMissing =
        DET.DiscreteEinsteinTensorCandidateDiagnostic.firstMissing
          DET.canonicalDiscreteEinsteinTensorCandidateDiagnostic
    ; inheritedDiscreteEinsteinFirstMissingIsCRTConnection =
        refl
    ; inheritedSelectedGRFirstMissing =
        SelectedGR.GRSelectedNonFlatMetricInstanceSurface.firstMissingNonFlatLaw
          SelectedGR.canonicalGRSelectedNonFlatMetricInstanceSurface
    ; inheritedSelectedGRFirstMissingIsChristoffelFromMetric =
        refl
    ; unsupportedClaims =
        canonicalDiscreteEinsteinVacuumLimitUnsupportedClaims
    ; unsupportedClaimsAreCanonical =
        refl
    ; exactBlockerReport =
        "No christoffelVanishesOffResonance or equivalent off-resonance Christoffel-zero law is present"
        ∷ "No Riemann-from-Christoffel-zero propagation law is present"
        ∷ "No Ricci contraction from Riemann-zero law is present"
        ∷ "No Einstein tensor zero from Ricci-zero vacuum reduction is present"
        ∷ []
    ; nonPromotionBoundary =
        "This surface is a bounded vacuum-limit obstruction report, not a GR promotion"
        ∷ "Flat-vacuum and flat-Minkowski prerequisite surfaces are not promoted to a non-flat off-resonance theorem"
        ∷ "The selected non-flat metric Christoffel slot is typed, but not proved to be Levi-Civita or off-resonance zero"
        ∷ "No vacuum G=0 theorem is constructed until the four ordered missing primitives are supplied"
        ∷ []
    }

discreteEinsteinVacuumLimitExactStatus :
  DiscreteEinsteinVacuumLimitSurface.status
    canonicalDiscreteEinsteinVacuumLimitSurface
  ≡
  blockedBeforeOffResonanceChristoffelZero
discreteEinsteinVacuumLimitExactStatus = refl

discreteEinsteinVacuumLimitExactFirstMissing :
  DiscreteEinsteinVacuumLimitSurface.firstMissingPrimitive
    canonicalDiscreteEinsteinVacuumLimitSurface
  ≡
  missingChristoffelVanishesOffResonance
discreteEinsteinVacuumLimitExactFirstMissing = refl

discreteEinsteinVacuumLimitInheritedDETFirstMissing :
  DiscreteEinsteinVacuumLimitSurface.inheritedDiscreteEinsteinFirstMissing
    canonicalDiscreteEinsteinVacuumLimitSurface
  ≡
  DET.missingCarrierInternalNonFlatConnectionFromCRT
discreteEinsteinVacuumLimitInheritedDETFirstMissing = refl

discreteEinsteinVacuumLimitInheritedSelectedGRFirstMissing :
  DiscreteEinsteinVacuumLimitSurface.inheritedSelectedGRFirstMissing
    canonicalDiscreteEinsteinVacuumLimitSurface
  ≡
  SelectedGR.missingSelectedChristoffelFromMetricLaw
discreteEinsteinVacuumLimitInheritedSelectedGRFirstMissing = refl
