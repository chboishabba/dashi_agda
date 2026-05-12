module DASHI.Physics.Closure.MaxwellGaugeFieldEquationScope where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_)

import DASHI.Physics.Closure.CanonicalGaugeMatterRecoveredMatterFieldTheorem as CGMRMFT
import DASHI.Physics.Closure.KnownLimitsFullMatterGaugeTheorem as KLF

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

  missingHomogeneousMaxwellEquation :
    G2MaxwellMissingField

  missingInhomogeneousMaxwellEquation :
    G2MaxwellMissingField

  missingMatterCurrentExtraction :
    G2MaxwellMissingField

  missingGaugeCovarianceLaw :
    G2MaxwellMissingField

  missingSpinePreservationSection :
    G2MaxwellMissingField

data G2MaxwellObstructionStatus : Set where
  firstMissingObligationOnlyNoNegation :
    G2MaxwellObstructionStatus

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
  ∷ homogeneousEquationCertificate
  ∷ inhomogeneousEquationCertificate
  ∷ spinePreservationCertificate
  ∷ []

-- Obligation postulates.  These are intentionally the only postulates in this
-- module, and they are named as obligations rather than theorem witnesses.
postulate
  obligationMaxwellEquationComponentFields :
    G2MaxwellEquationComponentObligations
      canonicalG2CanonicalGaugeMatterInputs

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
    ; maxwellSpinePreservationObligations =
        obligationMaxwellSpinePreservationFields
    ; missingFields =
        missingFieldStrengthFromConnection
        ∷ missingHomogeneousMaxwellEquation
        ∷ missingInhomogeneousMaxwellEquation
        ∷ missingMatterCurrentExtraction
        ∷ missingGaugeCovarianceLaw
        ∷ missingSpinePreservationSection
        ∷ []
    ; obstructionCertificates =
        canonicalG2MaxwellObstructionCertificates
    ; noPromotionBoundary =
        "This scope does not construct MaxwellGaugeFieldEquationTheorem"
        ∷ "This scope does not upgrade CanonicalGaugeMatterRecoveredMatterFieldTheorem beyond bundle-shaped recovered matter fields"
        ∷ "The field-strength-from-connection, Maxwell equation laws, current extraction, gauge covariance, and Maxwell spine section remain obligations"
        ∷ "This scope does not satisfy the G6 section-EM dependency"
        ∷ []
    }
