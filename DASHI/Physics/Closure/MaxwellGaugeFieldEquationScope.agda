module DASHI.Physics.Closure.MaxwellGaugeFieldEquationScope where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ)
open import Data.List.Base using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_)

import DASHI.Physics.Closure.CanonicalGaugeMatterRecoveredMatterFieldTheorem as CGMRMFT
import DASHI.Physics.Closure.G2DiscreteCurvatureCarrier as G2DCC
import DASHI.Physics.Closure.KnownLimitsFullMatterGaugeTheorem as KLF
import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC
import DASHI.Physics.ShiftGaugeCurrentConsistency as SGCC

------------------------------------------------------------------------
-- G2 Maxwell gauge field-equation scope.
--
-- This module deliberately does not claim G2.  It records the exact
-- currently-inhabited canonical gauge/matter inputs and the missing fields
-- that a future MaxwellGaugeFieldEquationTheorem must provide.

data G2MaxwellFieldEquationScopeStatus : Set where
  obligationSurfaceOnlyNoPromotion :
    G2MaxwellFieldEquationScopeStatus

data G2MaxwellMissingField : Set where
  missingFieldStrengthFromConnection :
    G2MaxwellMissingField

  missingDiscreteCurvatureCarrierForShiftGaugeField :
    G2MaxwellMissingField

  missingCurvatureToFieldStrengthFromShiftGaugeConnection :
    G2MaxwellMissingField

  missingDiscreteMaxwellEquationFromFieldStrengthAndCurrent :
    G2MaxwellMissingField

  missingHomogeneousMaxwellEquation :
    G2MaxwellMissingField

  missingInhomogeneousMaxwellEquation :
    G2MaxwellMissingField

  missingMatterCurrentExtraction :
    G2MaxwellMissingField

  missingSpineActionU1SectorRestriction :
    G2MaxwellMissingField

  missingYangMillsSectorRestriction :
    G2MaxwellMissingField

  missingKillingFormDecomposition :
    G2MaxwellMissingField

  missingChargeNormalization :
    G2MaxwellMissingField

  missingBianchiFromExteriorNilpotency :
    G2MaxwellMissingField

  missingSourcedEquationFromSectorVariation :
    G2MaxwellMissingField

  missingGaugeCovarianceLaw :
    G2MaxwellMissingField

  missingSpinePreservationSection :
    G2MaxwellMissingField

data G2MaxwellObstructionStatus : Set where
  firstMissingObligationOnlyNoNegation :
    G2MaxwellObstructionStatus

data G2MaxwellClosureTheoremTargetStatus : Set where
  closureTheoremTargetObligationOnlyNoPromotion :
    G2MaxwellClosureTheoremTargetStatus

data G2MaxwellCurvatureDiscreteSurfaceStatus : Set where
  curvatureDiscreteSurfaceObligationOnlyNoPromotion :
    G2MaxwellCurvatureDiscreteSurfaceStatus

data G2MaxwellCurvatureDiscreteFirstMissing : Set where
  firstMissingDiscreteCurvatureCarrierForShiftGaugeField :
    G2MaxwellCurvatureDiscreteFirstMissing

record G2MaxwellKernelNamedObligations : Set where
  field
    u1EmbeddingObligation :
      String

    killingRestrictionObligation :
      String

    curvatureToFieldStrengthObligation :
      String

    sourcedCurrentObligation :
      String

    namedObligationBoundary :
      List String

record G2MaxwellCurvatureDiscreteEquationSurface : Setω where
  field
    surfaceStatus :
      G2MaxwellCurvatureDiscreteSurfaceStatus

    finiteGaugeCouplingSurface :
      SFGC.ShiftFiniteGaugeCoupling

    gaugeCurrentConsistencySurface :
      SGCC.ShiftGaugeCurrentConsistency

    staticGaugeConnectionCarrier :
      Set

    discreteCurrentEdgeCarrier :
      Set

    recoveredMatterCurrentCarrier :
      Set

    discreteCurvatureCarrierObligation :
      String

    discreteCurvatureCarrierRequirement :
      G2DCC.G2ShiftGaugeDiscreteCurvatureCarrierObligation

    curvatureToFieldStrengthLemmaObligation :
      String

    discreteHomogeneousMaxwellLawObligation :
      String

    discreteInhomogeneousMaxwellLawObligation :
      String

    firstMissing :
      G2MaxwellCurvatureDiscreteFirstMissing

    firstMissingFieldName :
      String

    firstMissingLemmaName :
      String

    surfaceBoundary :
      List String

canonicalG2MaxwellCurvatureDiscreteEquationSurface :
  G2MaxwellCurvatureDiscreteEquationSurface
canonicalG2MaxwellCurvatureDiscreteEquationSurface =
  record
    { surfaceStatus =
        curvatureDiscreteSurfaceObligationOnlyNoPromotion
    ; finiteGaugeCouplingSurface =
        SFGC.shiftFiniteGaugeCoupling
    ; gaugeCurrentConsistencySurface =
        SGCC.shiftGaugeCurrentConsistency
    ; staticGaugeConnectionCarrier =
        SFGC.GaugeField
    ; discreteCurrentEdgeCarrier =
        SGCC.Edge
    ; recoveredMatterCurrentCarrier =
        ℤ
    ; discreteCurvatureCarrierObligation =
        "supply a discrete curvature carrier for the static Phase4 link assignment SFGC.GaugeField"
    ; discreteCurvatureCarrierRequirement =
        G2DCC.canonicalSFGCGaugeDiscreteCurvatureCarrierObligation
    ; curvatureToFieldStrengthLemmaObligation =
        "supply curvatureToFieldStrengthFromShiftGaugeConnection after the discrete curvature carrier is fixed"
    ; discreteHomogeneousMaxwellLawObligation =
        "supply a discrete Bianchi/Faraday law over the field strength obtained from curvature"
    ; discreteInhomogeneousMaxwellLawObligation =
        "supply a sourced discrete Maxwell law relating the field strength to SGCC.edgeCurrent or a nontrivial current extractor"
    ; firstMissing =
        firstMissingDiscreteCurvatureCarrierForShiftGaugeField
    ; firstMissingFieldName =
        "DiscreteCurvatureCarrier for SFGC.GaugeField"
    ; firstMissingLemmaName =
        "curvatureToFieldStrengthFromShiftGaugeConnection"
    ; surfaceBoundary =
        "ShiftFiniteGaugeCoupling supplies a static Phase4 link field and covariant-operator targets, not a curvature carrier"
        ∷ "ShiftGaugeCurrentConsistency supplies an edge-current surface with neutral currentPhase, not a sourced Maxwell equation"
        ∷ "The first missing field is DiscreteCurvatureCarrier for SFGC.GaugeField; the first missing lemma after that is curvatureToFieldStrengthFromShiftGaugeConnection"
        ∷ "No MaxwellGaugeFieldEquationTheorem inhabitant is constructed by this surface"
        ∷ []
    }

record G2CanonicalGaugeMatterInputs : Setω where
  field
    knownLimitsFullMatterGauge :
      KLF.KnownLimitsFullMatterGaugeTheorem

    recoveredMatterField :
      CGMRMFT.CanonicalGaugeMatterRecoveredMatterFieldTheorem

    recoveredMatterFieldCarrier :
      Set

    inhabitedBundleFields :
      List String

    inhabitedMatterFieldFacts :
      List String

canonicalG2CanonicalGaugeMatterInputs :
  G2CanonicalGaugeMatterInputs
canonicalG2CanonicalGaugeMatterInputs =
  record
    { knownLimitsFullMatterGauge =
        KLF.canonicalKnownLimitsFullMatterGaugeTheorem
    ; recoveredMatterField =
        CGMRMFT.canonicalGaugeMatterRecoveredMatterFieldTheorem
    ; recoveredMatterFieldCarrier =
        CGMRMFT.CanonicalGaugeMatterRecoveredMatterFieldTheorem.RecoveredMatterFieldCarrier
          CGMRMFT.canonicalGaugeMatterRecoveredMatterFieldTheorem
    ; inhabitedBundleFields =
        "canonical known-limits full matter/gauge aggregate"
        ∷ "canonical gauge-matter strengthening theorem"
        ∷ "canonical interpretable observable theorem"
        ∷ "canonical recovered matter-field theorem"
        ∷ []
    ; inhabitedMatterFieldFacts =
        "RecoveredMatterFieldCarrier is inhabited as the canonical recovered matter-field carrier"
        ∷ "carrier-observable compatibility is supplied by CanonicalGaugeMatterRecoveredMatterFieldTheorem"
        ∷ "transport-observable compatibility is supplied by CanonicalGaugeMatterRecoveredMatterFieldTheorem"
        ∷ "admissible gauge collapse to interpretable charge is supplied by CanonicalGaugeMatterRecoveredMatterFieldTheorem"
        ∷ "recovered matter is preserved by evolve/coarse/offset in the canonical theorem"
        ∷ []
    }

record G2MaxwellEquationComponentObligations
  (inputs : G2CanonicalGaugeMatterInputs) : Setω where
  field
    ConnectionCarrier :
      Set

    FieldStrengthCarrier :
      Set

    CurrentCarrier :
      Set

    MaxwellEquationCarrier :
      Set

    fieldStrengthFromConnection :
      ConnectionCarrier →
      FieldStrengthCarrier

    currentFromRecoveredMatter :
      G2CanonicalGaugeMatterInputs.recoveredMatterFieldCarrier inputs →
      CurrentCarrier

    homogeneousMaxwellEquation :
      FieldStrengthCarrier →
      MaxwellEquationCarrier

    inhomogeneousMaxwellEquation :
      FieldStrengthCarrier →
      CurrentCarrier →
      MaxwellEquationCarrier

    homogeneousMaxwellEquationLaw :
      MaxwellEquationCarrier →
      Set

    inhomogeneousMaxwellEquationLaw :
      MaxwellEquationCarrier →
      Set

    homogeneousMaxwellEquationAtFieldStrength :
      (connection : ConnectionCarrier) →
      homogeneousMaxwellEquationLaw
        (homogeneousMaxwellEquation
          (fieldStrengthFromConnection connection))

    inhomogeneousMaxwellEquationAtMatterCurrent :
      (connection : ConnectionCarrier) →
      (matter :
        G2CanonicalGaugeMatterInputs.recoveredMatterFieldCarrier inputs) →
      inhomogeneousMaxwellEquationLaw
        (inhomogeneousMaxwellEquation
          (fieldStrengthFromConnection connection)
          (currentFromRecoveredMatter matter))

    gaugeCovarianceLaw :
      ConnectionCarrier →
      FieldStrengthCarrier →
      Set

    fieldStrengthGaugeCovariant :
      (connection : ConnectionCarrier) →
      gaugeCovarianceLaw
        connection
        (fieldStrengthFromConnection connection)

record G2MaxwellSectorRestrictionObligations
  (inputs : G2CanonicalGaugeMatterInputs)
  (equationObligations :
    G2MaxwellEquationComponentObligations inputs) : Setω where
  open G2MaxwellEquationComponentObligations equationObligations
    using
      ( ConnectionCarrier
      ; FieldStrengthCarrier
      ; CurrentCarrier
      ; MaxwellEquationCarrier
      ; fieldStrengthFromConnection
      ; currentFromRecoveredMatter
      ; inhomogeneousMaxwellEquation
      ; inhomogeneousMaxwellEquationLaw
      )

  field
    SpineActionCarrier :
      Set

    U1SectorCarrier :
      Set

    YangMillsActionCarrier :
      Set

    KillingFormDecompositionCarrier :
      Set

    ChargeNormalizationCarrier :
      Set

    ExteriorDerivativeCarrier :
      Set

    ExteriorDerivativeNilpotencyLaw :
      ExteriorDerivativeCarrier →
      Set

    bianchiIdentityFromNilpotency :
      (exteriorDerivative : ExteriorDerivativeCarrier) →
      ExteriorDerivativeNilpotencyLaw exteriorDerivative

    spineActionU1SectorRestriction :
      SpineActionCarrier →
      U1SectorCarrier

    u1SectorToYangMillsAction :
      U1SectorCarrier →
      YangMillsActionCarrier

    killingFormDecompositionForU1Restriction :
      SpineActionCarrier →
      U1SectorCarrier →
      KillingFormDecompositionCarrier

    chargeNormalizationForU1Sector :
      U1SectorCarrier →
      KillingFormDecompositionCarrier →
      ChargeNormalizationCarrier

    killingFormDecompositionLaw :
      SpineActionCarrier →
      U1SectorCarrier →
      KillingFormDecompositionCarrier →
      Set

    chargeNormalizationLaw :
      U1SectorCarrier →
      ChargeNormalizationCarrier →
      Set

    killingFormDecompositionDerived :
      (spineAction : SpineActionCarrier) →
      killingFormDecompositionLaw
        spineAction
        (spineActionU1SectorRestriction spineAction)
        (killingFormDecompositionForU1Restriction
          spineAction
          (spineActionU1SectorRestriction spineAction))

    chargeNormalizationDerived :
      (spineAction : SpineActionCarrier) →
      chargeNormalizationLaw
        (spineActionU1SectorRestriction spineAction)
        (chargeNormalizationForU1Sector
          (spineActionU1SectorRestriction spineAction)
          (killingFormDecompositionForU1Restriction
            spineAction
            (spineActionU1SectorRestriction spineAction)))

    sectorRestrictionPreservesFieldStrength :
      SpineActionCarrier →
      ConnectionCarrier →
      FieldStrengthCarrier →
      Set

    fieldStrengthPreservedByU1Restriction :
      (spineAction : SpineActionCarrier) →
      (connection : ConnectionCarrier) →
      sectorRestrictionPreservesFieldStrength
        spineAction
        connection
        (fieldStrengthFromConnection connection)

    currentExtractionCompatibleWithSectorRestriction :
      U1SectorCarrier →
      G2CanonicalGaugeMatterInputs.recoveredMatterFieldCarrier inputs →
      CurrentCarrier →
      Set

    currentExtractionPreservedByU1Restriction :
      (spineAction : SpineActionCarrier) →
      (matter :
        G2CanonicalGaugeMatterInputs.recoveredMatterFieldCarrier inputs) →
      currentExtractionCompatibleWithSectorRestriction
        (spineActionU1SectorRestriction spineAction)
        matter
        (currentFromRecoveredMatter matter)

    sourcedEquationFromSectorVariation :
      SpineActionCarrier →
      YangMillsActionCarrier →
      FieldStrengthCarrier →
      CurrentCarrier →
      MaxwellEquationCarrier

    sourcedEquationLawFromSectorVariation :
      (spineAction : SpineActionCarrier) →
      (connection : ConnectionCarrier) →
      (matter :
        G2CanonicalGaugeMatterInputs.recoveredMatterFieldCarrier inputs) →
      inhomogeneousMaxwellEquationLaw
        (sourcedEquationFromSectorVariation
          spineAction
          (u1SectorToYangMillsAction
            (spineActionU1SectorRestriction spineAction))
          (fieldStrengthFromConnection connection)
          (currentFromRecoveredMatter matter))

    sectorVariationMatchesSourcedMaxwellEquation :
      (spineAction : SpineActionCarrier) →
      (connection : ConnectionCarrier) →
      (matter :
        G2CanonicalGaugeMatterInputs.recoveredMatterFieldCarrier inputs) →
      sourcedEquationFromSectorVariation
        spineAction
        (u1SectorToYangMillsAction
          (spineActionU1SectorRestriction spineAction))
        (fieldStrengthFromConnection connection)
        (currentFromRecoveredMatter matter)
      ≡
      inhomogeneousMaxwellEquation
        (fieldStrengthFromConnection connection)
        (currentFromRecoveredMatter matter)

record G2MaxwellSpinePreservationObligations : Setω where
  field
    SpineCarrier :
      Set

    MaxwellLaneCarrier :
      Set

    embedMaxwellInSpine :
      MaxwellLaneCarrier →
      SpineCarrier

    recoverMaxwellFromSpine :
      SpineCarrier →
      MaxwellLaneCarrier

    maxwellSpineSection :
      (spine : SpineCarrier) →
      embedMaxwellInSpine (recoverMaxwellFromSpine spine) ≡ spine

    spinePreservationBoundary :
      List String

record G2MaxwellObstructionCertificate : Set where
  field
    missingField :
      G2MaxwellMissingField

    obstructionStatus :
      G2MaxwellObstructionStatus

    requiredTheoremOrReceipt :
      String

    whyNoNegationProof :
      String

    nextEvidence :
      String

    boundary :
      String

fieldStrengthFromConnectionCertificate :
  G2MaxwellObstructionCertificate
fieldStrengthFromConnectionCertificate =
  record
    { missingField =
        missingFieldStrengthFromConnection
    ; obstructionStatus =
        firstMissingObligationOnlyNoNegation
    ; requiredTheoremOrReceipt =
        "connection carrier, field-strength carrier, and fieldStrengthFromConnection map"
    ; whyNoNegationProof =
        "The current scope has not fixed a failed connection candidate; it only records that no such Maxwell field-strength construction is present"
    ; nextEvidence =
        "Provide a connection-to-field-strength construction compatible with the canonical recovered matter bundle"
    ; boundary =
        "Obligation certificate only; no G2 theorem promotion"
    }

discreteCurvatureCarrierCertificate :
  G2MaxwellObstructionCertificate
discreteCurvatureCarrierCertificate =
  record
    { missingField =
        missingDiscreteCurvatureCarrierForShiftGaugeField
    ; obstructionStatus =
        firstMissingObligationOnlyNoNegation
    ; requiredTheoremOrReceipt =
        "DiscreteCurvatureCarrier for the static Phase4 link gauge field SFGC.GaugeField"
    ; whyNoNegationProof =
        "The inspected gauge modules expose static links, vacuum compatibility, current consistency, and covariance targets, but no curvature carrier for the link field"
    ; nextEvidence =
        "Supply DiscreteCurvatureCarrier for SFGC.GaugeField; only then can curvatureToFieldStrengthFromShiftGaugeConnection be stated as a closed lemma"
    ; boundary =
        "Obligation certificate only; no G2 theorem promotion"
    }

curvatureToFieldStrengthCertificate :
  G2MaxwellObstructionCertificate
curvatureToFieldStrengthCertificate =
  record
    { missingField =
        missingCurvatureToFieldStrengthFromShiftGaugeConnection
    ; obstructionStatus =
        firstMissingObligationOnlyNoNegation
    ; requiredTheoremOrReceipt =
        "curvatureToFieldStrengthFromShiftGaugeConnection after a discrete curvature carrier is supplied"
    ; whyNoNegationProof =
        "Without a discrete curvature carrier for SFGC.GaugeField, the curvature-to-field-strength lemma is not yet typeable in the current Maxwell/G2 surface"
    ; nextEvidence =
        "After DiscreteCurvatureCarrier is fixed, supply a map from shift-gauge curvature to electromagnetic field strength and bind it to the Maxwell equation laws"
    ; boundary =
        "Obligation certificate only; no G2 theorem promotion"
    }

discreteMaxwellEquationCertificate :
  G2MaxwellObstructionCertificate
discreteMaxwellEquationCertificate =
  record
    { missingField =
        missingDiscreteMaxwellEquationFromFieldStrengthAndCurrent
    ; obstructionStatus =
        firstMissingObligationOnlyNoNegation
    ; requiredTheoremOrReceipt =
        "discrete homogeneous and sourced Maxwell equation laws over field strength and recovered matter current"
    ; whyNoNegationProof =
        "The current gauge-current lane has a neutral currentPhase reducer and no Maxwell equation consumer tying field strength to current"
    ; nextEvidence =
        "Supply discrete Bianchi/Faraday and sourced Maxwell laws after curvature-to-field-strength and current extraction are inhabited"
    ; boundary =
        "Obligation certificate only; no G2 theorem promotion"
    }

homogeneousEquationCertificate :
  G2MaxwellObstructionCertificate
homogeneousEquationCertificate =
  record
    { missingField =
        missingHomogeneousMaxwellEquation
    ; obstructionStatus =
        firstMissingObligationOnlyNoNegation
    ; requiredTheoremOrReceipt =
        "homogeneous Maxwell equation carrier and law over field strength"
    ; whyNoNegationProof =
        "No concrete field-strength carrier has been supplied, so no failed homogeneous equation proof can be exhibited"
    ; nextEvidence =
        "Supply the Bianchi/Faraday-style homogeneous equation law for fieldStrengthFromConnection"
    ; boundary =
        "Obligation certificate only; no G2 theorem promotion"
    }

inhomogeneousEquationCertificate :
  G2MaxwellObstructionCertificate
inhomogeneousEquationCertificate =
  record
    { missingField =
        missingInhomogeneousMaxwellEquation
    ; obstructionStatus =
        firstMissingObligationOnlyNoNegation
    ; requiredTheoremOrReceipt =
        "inhomogeneous Maxwell equation carrier and sourced law over recovered matter current"
    ; whyNoNegationProof =
        "The current recovered matter theorem gives a bundle-shaped matter field, not a current coupled to field strength"
    ; nextEvidence =
        "Supply currentFromRecoveredMatter and the sourced Maxwell equation law"
    ; boundary =
        "Obligation certificate only; no G2 theorem promotion"
    }

sectorRestrictionCertificate :
  G2MaxwellObstructionCertificate
sectorRestrictionCertificate =
  record
    { missingField =
        missingSpineActionU1SectorRestriction
    ; obstructionStatus =
        firstMissingObligationOnlyNoNegation
    ; requiredTheoremOrReceipt =
        "SpineActionU1SectorRestriction binding the canonical spine action to the U(1) Yang-Mills sector"
    ; whyNoNegationProof =
        "No concrete spine action restriction candidate has been supplied, so this scope records the route rather than a failed theorem"
    ; nextEvidence =
        "Provide a sector-restriction theorem showing the spine action restricts to the U(1) Yang-Mills action with field strength preserved"
    ; boundary =
        "Obligation certificate only; no G2 theorem promotion"
    }

killingFormDecompositionCertificate :
  G2MaxwellObstructionCertificate
killingFormDecompositionCertificate =
  record
    { missingField =
        missingKillingFormDecomposition
    ; obstructionStatus =
        firstMissingObligationOnlyNoNegation
    ; requiredTheoremOrReceipt =
        "Killing-form decomposition showing the selected U(1) sector has the required electromagnetic normalization component"
    ; whyNoNegationProof =
        "No accepted U(1) sector restriction has been supplied, so no failed Killing-form decomposition can be exhibited"
    ; nextEvidence =
        "After the sector restriction is fixed, provide the Killing-form decomposition used by the charge-normalized Maxwell action"
    ; boundary =
        "Obligation certificate only; no G2 theorem promotion"
    }

chargeNormalizationCertificate :
  G2MaxwellObstructionCertificate
chargeNormalizationCertificate =
  record
    { missingField =
        missingChargeNormalization
    ; obstructionStatus =
        firstMissingObligationOnlyNoNegation
    ; requiredTheoremOrReceipt =
        "charge normalization for the selected U(1) sector after Killing-form decomposition"
    ; whyNoNegationProof =
        "The current surface has no selected U(1) sector, Killing-form decomposition, or physical charge scale to normalize"
    ; nextEvidence =
        "Supply a charge-normalization law compatible with the recovered matter current and the sector Yang-Mills action"
    ; boundary =
        "Obligation certificate only; no G2 theorem or physical charge promotion"
    }

bianchiNilpotencyCertificate :
  G2MaxwellObstructionCertificate
bianchiNilpotencyCertificate =
  record
    { missingField =
        missingBianchiFromExteriorNilpotency
    ; obstructionStatus =
        firstMissingObligationOnlyNoNegation
    ; requiredTheoremOrReceipt =
        "Exterior-derivative nilpotency carrier proving the homogeneous/Bianchi part from field-strength construction"
    ; whyNoNegationProof =
        "The route is expected to be routine once an exterior-derivative carrier and field strength are supplied; neither is present here"
    ; nextEvidence =
        "Supply d^2=0 or the discrete exterior-derivative substitute and connect it to homogeneousMaxwellEquationAtFieldStrength"
    ; boundary =
        "Obligation certificate only; no G2 theorem promotion"
    }

sourcedSectorVariationCertificate :
  G2MaxwellObstructionCertificate
sourcedSectorVariationCertificate =
  record
    { missingField =
        missingSourcedEquationFromSectorVariation
    ; obstructionStatus =
        firstMissingObligationOnlyNoNegation
    ; requiredTheoremOrReceipt =
        "variation of the U(1) Yang-Mills sector action yielding the sourced Maxwell equation with extracted current"
    ; whyNoNegationProof =
        "The current surface has no accepted sector restriction, Yang-Mills action carrier, or current extraction law to vary"
    ; nextEvidence =
        "After SpineActionU1SectorRestriction, prove the sector variation matches inhomogeneousMaxwellEquation"
    ; boundary =
        "Obligation certificate only; no G2 theorem promotion"
    }

spinePreservationCertificate :
  G2MaxwellObstructionCertificate
spinePreservationCertificate =
  record
    { missingField =
        missingSpinePreservationSection
    ; obstructionStatus =
        firstMissingObligationOnlyNoNegation
    ; requiredTheoremOrReceipt =
        "Maxwell lane carrier, embedding/recovery maps, and section proof for the canonical spine"
    ; whyNoNegationProof =
        "A real obstruction would require a concrete pre-section Maxwell lane candidate; this scope only records the missing section field"
    ; nextEvidence =
        "Provide the G6 section-EM compatible Maxwell spine preservation proof"
    ; boundary =
        "Obligation certificate only; no G2 or G6 promotion"
    }

canonicalG2MaxwellObstructionCertificates :
  List G2MaxwellObstructionCertificate
canonicalG2MaxwellObstructionCertificates =
  fieldStrengthFromConnectionCertificate
  ∷ discreteCurvatureCarrierCertificate
  ∷ curvatureToFieldStrengthCertificate
  ∷ discreteMaxwellEquationCertificate
  ∷ homogeneousEquationCertificate
  ∷ inhomogeneousEquationCertificate
  ∷ sectorRestrictionCertificate
  ∷ killingFormDecompositionCertificate
  ∷ chargeNormalizationCertificate
  ∷ bianchiNilpotencyCertificate
  ∷ sourcedSectorVariationCertificate
  ∷ spinePreservationCertificate
  ∷ []

-- Obligation postulates.  These are intentionally the only postulates in this
-- module, and they are named as obligations rather than theorem witnesses.
postulate
  obligationMaxwellEquationComponentFields :
    G2MaxwellEquationComponentObligations
      canonicalG2CanonicalGaugeMatterInputs

  obligationMaxwellSectorRestrictionFields :
    G2MaxwellSectorRestrictionObligations
      canonicalG2CanonicalGaugeMatterInputs
      obligationMaxwellEquationComponentFields

  obligationMaxwellSpinePreservationFields :
    G2MaxwellSpinePreservationObligations

record MaxwellGaugeFieldEquationScope : Setω where
  field
    status :
      G2MaxwellFieldEquationScopeStatus

    canonicalGaugeMatterInputs :
      G2CanonicalGaugeMatterInputs

    maxwellEquationComponentObligations :
      G2MaxwellEquationComponentObligations canonicalGaugeMatterInputs

    maxwellSectorRestrictionObligations :
      G2MaxwellSectorRestrictionObligations
        canonicalGaugeMatterInputs
        maxwellEquationComponentObligations

    curvatureDiscreteEquationSurface :
      G2MaxwellCurvatureDiscreteEquationSurface

    maxwellSpinePreservationObligations :
      G2MaxwellSpinePreservationObligations

    missingFields :
      List G2MaxwellMissingField

    obstructionCertificates :
      List G2MaxwellObstructionCertificate

    noPromotionBoundary :
      List String

canonicalMaxwellGaugeFieldEquationScope :
  MaxwellGaugeFieldEquationScope
canonicalMaxwellGaugeFieldEquationScope =
  record
    { status =
        obligationSurfaceOnlyNoPromotion
    ; canonicalGaugeMatterInputs =
        canonicalG2CanonicalGaugeMatterInputs
    ; maxwellEquationComponentObligations =
        obligationMaxwellEquationComponentFields
    ; maxwellSectorRestrictionObligations =
        obligationMaxwellSectorRestrictionFields
    ; curvatureDiscreteEquationSurface =
        canonicalG2MaxwellCurvatureDiscreteEquationSurface
    ; maxwellSpinePreservationObligations =
        obligationMaxwellSpinePreservationFields
    ; missingFields =
        missingFieldStrengthFromConnection
        ∷ missingDiscreteCurvatureCarrierForShiftGaugeField
        ∷ missingCurvatureToFieldStrengthFromShiftGaugeConnection
        ∷ missingDiscreteMaxwellEquationFromFieldStrengthAndCurrent
        ∷ missingHomogeneousMaxwellEquation
        ∷ missingInhomogeneousMaxwellEquation
        ∷ missingMatterCurrentExtraction
        ∷ missingSpineActionU1SectorRestriction
        ∷ missingYangMillsSectorRestriction
        ∷ missingKillingFormDecomposition
        ∷ missingChargeNormalization
        ∷ missingBianchiFromExteriorNilpotency
        ∷ missingSourcedEquationFromSectorVariation
        ∷ missingGaugeCovarianceLaw
        ∷ missingSpinePreservationSection
        ∷ []
    ; obstructionCertificates =
        canonicalG2MaxwellObstructionCertificates
    ; noPromotionBoundary =
        "This scope does not construct MaxwellGaugeFieldEquationTheorem"
        ∷ "This scope does not upgrade CanonicalGaugeMatterRecoveredMatterFieldTheorem beyond bundle-shaped recovered matter fields"
        ∷ "The inspected finite/static gauge modules do not supply DiscreteCurvatureCarrier for SFGC.GaugeField"
        ∷ "curvatureToFieldStrengthFromShiftGaugeConnection is the first missing lemma after that carrier is supplied"
        ∷ "The Bianchi/homogeneous route is recorded as routine only after exterior-derivative nilpotency and field-strength construction are supplied"
        ∷ "The sourced Maxwell route requires SpineActionU1SectorRestriction, Yang-Mills sector binding, current extraction, and sector-variation equality"
        ∷ "The U(1) sector route also requires a Killing-form decomposition and charge-normalization law before physical Maxwell normalization can be claimed"
        ∷ "The field-strength-from-connection, Maxwell equation laws, current extraction, gauge covariance, and Maxwell spine section remain obligations"
        ∷ "This scope does not satisfy the G6 section-EM dependency"
        ∷ []
    }

record G2MaxwellSurfaceToBridgeLaw
  (surface : MaxwellGaugeFieldEquationScope) : Setω where
  field
    equationComponentBridgeLaw :
      G2MaxwellEquationComponentObligations
        (MaxwellGaugeFieldEquationScope.canonicalGaugeMatterInputs surface)

    sectorRestrictionBridgeLaw :
      G2MaxwellSectorRestrictionObligations
        (MaxwellGaugeFieldEquationScope.canonicalGaugeMatterInputs surface)
        equationComponentBridgeLaw

    spinePreservationBridgeLaw :
      G2MaxwellSpinePreservationObligations

    namedKernelObligations :
      G2MaxwellKernelNamedObligations

    bridgeLawBoundary :
      List String

record G2MaxwellClosureTheoremTarget
  (surface : MaxwellGaugeFieldEquationScope)
  (bridgeLaw : G2MaxwellSurfaceToBridgeLaw surface) : Setω where
  field
    targetStatus :
      G2MaxwellClosureTheoremTargetStatus

    targetTheoremName :
      String

    requiredBridgeLaw :
      G2MaxwellSurfaceToBridgeLaw surface

    remainingMissingFields :
      List G2MaxwellMissingField

    closureTargetBoundary :
      List String

record G2MaxwellTheoremKernel : Setω where
  field
    surface :
      MaxwellGaugeFieldEquationScope

    bridgeLaw :
      G2MaxwellSurfaceToBridgeLaw surface

    closureTheoremTarget :
      G2MaxwellClosureTheoremTarget surface bridgeLaw

    kernelBoundary :
      List String

canonicalG2MaxwellSurfaceToBridgeLaw :
  G2MaxwellSurfaceToBridgeLaw canonicalMaxwellGaugeFieldEquationScope
canonicalG2MaxwellSurfaceToBridgeLaw =
  record
    { equationComponentBridgeLaw =
        obligationMaxwellEquationComponentFields
    ; sectorRestrictionBridgeLaw =
        obligationMaxwellSectorRestrictionFields
    ; spinePreservationBridgeLaw =
        obligationMaxwellSpinePreservationFields
    ; namedKernelObligations =
        record
          { u1EmbeddingObligation =
              "construct the electromagnetic U(1) embedding/restriction from the canonical spine action"
          ; killingRestrictionObligation =
              "prove the Killing-form restriction/decomposition and charge normalization for the selected U(1) sector"
          ; curvatureToFieldStrengthObligation =
              "turn the connection/curvature carrier into electromagnetic field strength before using Maxwell equation laws"
          ; sourcedCurrentObligation =
              "extract a matter current from recovered matter and prove compatibility with the U(1) sector variation"
          ; namedObligationBoundary =
              "These named obligations are route labels over the existing typed obligation records"
              ∷ "They do not select a U(1) embedding, prove a Killing restriction, or derive curvature-to-field-strength closure"
              ∷ []
          }
    ; bridgeLawBoundary =
        "surface -> bridge law: canonical G2 scope inputs are routed to Maxwell equation-component, U(1) embedding/restriction, Killing restriction, curvature-to-field-strength, and spine-preservation obligations"
        ∷ "The bridge law is obligation-backed only; it does not construct field strength, current extraction, Maxwell equations, or a U(1) sector proof"
        ∷ []
    }

canonicalG2MaxwellClosureTheoremTarget :
  G2MaxwellClosureTheoremTarget
    canonicalMaxwellGaugeFieldEquationScope
    canonicalG2MaxwellSurfaceToBridgeLaw
canonicalG2MaxwellClosureTheoremTarget =
  record
    { targetStatus =
        closureTheoremTargetObligationOnlyNoPromotion
    ; targetTheoremName =
        "MaxwellGaugeFieldEquationTheorem"
    ; requiredBridgeLaw =
        canonicalG2MaxwellSurfaceToBridgeLaw
    ; remainingMissingFields =
        MaxwellGaugeFieldEquationScope.missingFields
          canonicalMaxwellGaugeFieldEquationScope
    ; closureTargetBoundary =
        "closure theorem target: derive homogeneous and sourced Maxwell equations from the bridge law"
        ∷ "The target remains uninhabited as a theorem; this record only names the target and its required bridge-law packet"
        ∷ "G6 section-EM remains outside this target until a real Maxwell spine section is supplied"
        ∷ []
    }

canonicalG2MaxwellTheoremKernel :
  G2MaxwellTheoremKernel
canonicalG2MaxwellTheoremKernel =
  record
    { surface =
        canonicalMaxwellGaugeFieldEquationScope
    ; bridgeLaw =
        canonicalG2MaxwellSurfaceToBridgeLaw
    ; closureTheoremTarget =
        canonicalG2MaxwellClosureTheoremTarget
    ; kernelBoundary =
        "G2 theorem-kernel route: surface -> bridge law -> closure theorem target"
        ∷ "The kernel is a typed obligation packet and does not promote G2"
        ∷ []
    }
