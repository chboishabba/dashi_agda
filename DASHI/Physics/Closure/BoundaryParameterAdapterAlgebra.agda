module DASHI.Physics.Closure.BoundaryParameterAdapterAlgebra where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Boundaries.ClayYMGap as Clay
import DASHI.Physics.Boundaries.HiggsPDGBoundary as HiggsPDG
import DASHI.Physics.QFT.DHRThermodynamicLimitBoundary as DHRLimitBoundary

------------------------------------------------------------------------
-- Boundary-parameter adapter algebra.
--
-- This module records the typed entry surface for external boundary tokens.
-- It keeps the Clay/YM, Higgs/PDG, and DHR thermodynamic-limit anchors
-- explicit, while leaving boundary ingress, legal consumption, propagation,
-- and illegal-use detection as fail-closed obligations.

data BoundaryParameterAdapterStatus : Set where
  boundaryTokensRecordedNoPromotion :
    BoundaryParameterAdapterStatus

data BoundaryParameterAdapterOpenObligation : Set where
  missingBoundaryIngressFunctoriality :
    BoundaryParameterAdapterOpenObligation

  missingLegalConsumptionInterface :
    BoundaryParameterAdapterOpenObligation

  missingFunctorialPropagation :
    BoundaryParameterAdapterOpenObligation

  missingIllegalUseExclusion :
    BoundaryParameterAdapterOpenObligation

  missingAdapterAuditTrail :
    BoundaryParameterAdapterOpenObligation

canonicalBoundaryParameterAdapterOpenObligations :
  List BoundaryParameterAdapterOpenObligation
canonicalBoundaryParameterAdapterOpenObligations =
  missingBoundaryIngressFunctoriality
  ∷ missingLegalConsumptionInterface
  ∷ missingFunctorialPropagation
  ∷ missingIllegalUseExclusion
  ∷ missingAdapterAuditTrail
  ∷ []

data BoundaryParameterAdapterProofShape : Set where
  ingressRecorded :
    BoundaryParameterAdapterProofShape

  legalConsumptionDelimited :
    BoundaryParameterAdapterProofShape

  propagationTracked :
    BoundaryParameterAdapterProofShape

  illegalUseRejected :
    BoundaryParameterAdapterProofShape

  auditTrailPreserved :
    BoundaryParameterAdapterProofShape

canonicalBoundaryParameterAdapterProofShape :
  List BoundaryParameterAdapterProofShape
canonicalBoundaryParameterAdapterProofShape =
  ingressRecorded
  ∷ legalConsumptionDelimited
  ∷ propagationTracked
  ∷ illegalUseRejected
  ∷ auditTrailPreserved
  ∷ []

record BoundaryParameterAdapterAlgebraReceipt : Setω where
  field
    clayYMGapReceipt :
      Clay.ClayYMGapReceipt

    higgsPDGReceipt :
      HiggsPDG.HiggsPDGBoundaryReceipt

    dhrThermodynamicLimitReceipt :
      DHRLimitBoundary.DHRThermodynamicLimitBoundaryReceipt

    clayIngressLabel :
      String

    clayIngressLabelIsCanonical :
      clayIngressLabel ≡ "ClayYMGapBoundary"

    higgsIngressLabel :
      String

    higgsIngressLabelIsCanonical :
      higgsIngressLabel ≡ "HiggsPDGBoundary"

    dhrIngressLabel :
      String

    dhrIngressLabelIsCanonical :
      dhrIngressLabel ≡ "DHRThermodynamicLimitBoundary"

    ingressFunctorLabel :
      String

    ingressFunctorLabelIsCanonical :
      ingressFunctorLabel ≡ "boundary-parameter-adapter-functor"

    legalConsumptionTargetRecorded :
      Bool

    legalConsumptionTargetRecordedIsTrue :
      legalConsumptionTargetRecorded ≡ true

    propagationTargetRecorded :
      Bool

    propagationTargetRecordedIsTrue :
      propagationTargetRecorded ≡ true

    illegalUseDetected :
      Bool

    illegalUseDetectedIsFalse :
      illegalUseDetected ≡ false

    adapterPromoted :
      Bool

    adapterPromotedIsFalse :
      adapterPromoted ≡ false

    openObligations :
      List BoundaryParameterAdapterOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalBoundaryParameterAdapterOpenObligations

    proofShape :
      List BoundaryParameterAdapterProofShape

    proofShapeIsCanonical :
      proofShape ≡ canonicalBoundaryParameterAdapterProofShape

    boundaryNotes :
      List String

open BoundaryParameterAdapterAlgebraReceipt public

canonicalBoundaryParameterAdapterAlgebraReceipt :
  BoundaryParameterAdapterAlgebraReceipt
canonicalBoundaryParameterAdapterAlgebraReceipt =
  record
    { clayYMGapReceipt =
        Clay.canonicalClayYMGapReceipt
    ; higgsPDGReceipt =
        HiggsPDG.canonicalHiggsPDGBoundaryReceipt
    ; dhrThermodynamicLimitReceipt =
        DHRLimitBoundary.canonicalDHRThermodynamicLimitBoundaryReceipt
    ; clayIngressLabel =
        "ClayYMGapBoundary"
    ; clayIngressLabelIsCanonical =
        refl
    ; higgsIngressLabel =
        "HiggsPDGBoundary"
    ; higgsIngressLabelIsCanonical =
        refl
    ; dhrIngressLabel =
        "DHRThermodynamicLimitBoundary"
    ; dhrIngressLabelIsCanonical =
        refl
    ; ingressFunctorLabel =
        "boundary-parameter-adapter-functor"
    ; ingressFunctorLabelIsCanonical =
        refl
    ; legalConsumptionTargetRecorded =
        true
    ; legalConsumptionTargetRecordedIsTrue =
        refl
    ; propagationTargetRecorded =
        true
    ; propagationTargetRecordedIsTrue =
        refl
    ; illegalUseDetected =
        false
    ; illegalUseDetectedIsFalse =
        refl
    ; adapterPromoted =
        false
    ; adapterPromotedIsFalse =
        refl
    ; openObligations =
        canonicalBoundaryParameterAdapterOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; proofShape =
        canonicalBoundaryParameterAdapterProofShape
    ; proofShapeIsCanonical =
        refl
    ; boundaryNotes =
        "The Clay/YM, Higgs/PDG, and DHR limit receipts are recorded as external anchors"
        ∷ "Boundary ingress is typed as an adapter algebra, not an internal theorem claim"
        ∷ "Legal consumption, propagation, and illegal-use detection remain fail-closed targets"
        ∷ "No boundary token is fabricated or promoted here"
        ∷ []
    }

boundaryParameterAdapterFirstOpenObligation :
  BoundaryParameterAdapterOpenObligation
boundaryParameterAdapterFirstOpenObligation =
  missingBoundaryIngressFunctoriality
