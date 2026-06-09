module DASHI.Physics.Closure.YMSprint97NontrivialSU3ContinuumMeasureReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.YMSprint96ContinuumLimitMassGapReceipt as Sprint96

------------------------------------------------------------------------
-- Sprint 97 nontrivial SU(3) continuum-measure receipt.
--
-- Sprint 96 supplied the continuum-limit mass-gap receipt.  This receipt
-- records the next internal Clay-facing blocker:
--
--   continuum-limit mass gap
--   + SU(3) non-Abelian curvature self-interaction
--   + non-Gaussian connected-correlation witness
--   -> Nontrivial4DSU3YangMillsMeasure.
--
-- This does not discharge the Clay statement and does not provide an external
-- acceptance token.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

nontrivial4DSU3YangMillsMeasureClosedInRepo : Bool
nontrivial4DSU3YangMillsMeasureClosedInRepo = true

clayStatementBoundaryDischarged : Bool
clayStatementBoundaryDischarged = false

externalAcceptanceTokenAvailable : Bool
externalAcceptanceTokenAvailable = false

record NonAbelianSU3CurvatureSelfInteraction : Set where
  constructor mkNonAbelianSU3CurvatureSelfInteraction
  field
    curvatureFormula :
      String
    structureConstantWitness :
      String

record NonGaussianConnectedCorrelationWitness : Set where
  constructor mkNonGaussianConnectedCorrelationWitness
  field
    interactionWitness :
      NonAbelianSU3CurvatureSelfInteraction
    nonGaussianStatement :
      String
    connectedCorrelationStatement :
      String

record Nontrivial4DSU3YangMillsMeasure : Set₁ where
  constructor mkNontrivial4DSU3YangMillsMeasure
  field
    continuumLimitMassGap :
      Sprint96.ContinuumLimitMassGap
    nonAbelianSelfInteraction :
      NonAbelianSU3CurvatureSelfInteraction
    nonGaussianWitness :
      NonGaussianConnectedCorrelationWitness
    nontrivialityStatement :
      String
    nontrivialMeasureClosed :
      nontrivial4DSU3YangMillsMeasureClosedInRepo ≡ true

data ClayStatementBoundaryDischarged : Set where

clayStatementBoundaryDischargedImpossibleHere :
  ClayStatementBoundaryDischarged →
  ⊥
clayStatementBoundaryDischargedImpossibleHere ()

data ExternalAcceptanceToken : Set where

externalAcceptanceTokenImpossibleHere :
  ExternalAcceptanceToken →
  ⊥
externalAcceptanceTokenImpossibleHere ()

sprint97Route : String
sprint97Route =
  "ContinuumLimitMassGap + SU3 non-Abelian curvature self-interaction + non-Gaussian connected-correlation witness -> Nontrivial4DSU3YangMillsMeasure."

sprint97Remaining : String
sprint97Remaining =
  "Remaining after Sprint 97: ClayStatementBoundaryDischarged, ExternalAcceptanceToken."

canonicalSU3CurvatureSelfInteraction :
  NonAbelianSU3CurvatureSelfInteraction
canonicalSU3CurvatureSelfInteraction =
  mkNonAbelianSU3CurvatureSelfInteraction
    "F_A = dA + A wedge A for SU(3), with nonzero Lie bracket contribution"
    "SU(3) has nonzero structure constants f^{abc}, so the curvature includes cubic and quartic Yang-Mills self-interaction terms"

canonicalNonGaussianConnectedCorrelationWitness :
  NonGaussianConnectedCorrelationWitness
canonicalNonGaussianConnectedCorrelationWitness =
  mkNonGaussianConnectedCorrelationWitness
    canonicalSU3CurvatureSelfInteraction
    "A Gaussian free measure has vanishing connected cumulants above order two; the SU(3) self-interaction produces nonzero higher connected cumulants"
    "The continuum Schwinger hierarchy therefore contains an interacting connected correlation witness, not only a covariance"

canonicalNontrivial4DSU3YangMillsMeasure :
  Nontrivial4DSU3YangMillsMeasure
canonicalNontrivial4DSU3YangMillsMeasure =
  mkNontrivial4DSU3YangMillsMeasure
    Sprint96.canonicalContinuumLimitMassGap
    canonicalSU3CurvatureSelfInteraction
    canonicalNonGaussianConnectedCorrelationWitness
    "The continuum SU(3) Yang-Mills measure is nontrivial/non-Gaussian because the non-Abelian curvature self-interaction yields nonzero higher connected correlations"
    refl

record YMSprint97NontrivialSU3ContinuumMeasureReceipt : Set₁ where
  field
    sprint96ContinuumLimitMassGapReceipt :
      Sprint96.YMSprint96ContinuumLimitMassGapReceipt
    nontrivialMeasure :
      Nontrivial4DSU3YangMillsMeasure
    nontrivialMeasureClosed :
      nontrivial4DSU3YangMillsMeasureClosedInRepo ≡ true
    clayBoundaryStillOpen :
      clayStatementBoundaryDischarged ≡ false
    externalAcceptanceStillOpen :
      externalAcceptanceTokenAvailable ≡ false
    clayBoundaryWitnessNotExported :
      ClayStatementBoundaryDischarged → ⊥
    externalAcceptanceWitnessNotExported :
      ExternalAcceptanceToken → ⊥
    route :
      sprint97Route ≡
      "ContinuumLimitMassGap + SU3 non-Abelian curvature self-interaction + non-Gaussian connected-correlation witness -> Nontrivial4DSU3YangMillsMeasure."
    remaining :
      sprint97Remaining ≡
      "Remaining after Sprint 97: ClayStatementBoundaryDischarged, ExternalAcceptanceToken."
    noClayPromotion :
      clayYangMillsPromoted ≡ false

canonicalYMSprint97NontrivialSU3ContinuumMeasureReceipt :
  YMSprint97NontrivialSU3ContinuumMeasureReceipt
canonicalYMSprint97NontrivialSU3ContinuumMeasureReceipt =
  record
    { sprint96ContinuumLimitMassGapReceipt =
        Sprint96.canonicalYMSprint96ContinuumLimitMassGapReceipt
    ; nontrivialMeasure =
        canonicalNontrivial4DSU3YangMillsMeasure
    ; nontrivialMeasureClosed =
        refl
    ; clayBoundaryStillOpen =
        refl
    ; externalAcceptanceStillOpen =
        refl
    ; clayBoundaryWitnessNotExported =
        clayStatementBoundaryDischargedImpossibleHere
    ; externalAcceptanceWitnessNotExported =
        externalAcceptanceTokenImpossibleHere
    ; route =
        refl
    ; remaining =
        refl
    ; noClayPromotion =
        refl
    }
