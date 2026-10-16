module DASHI.Governance.BoloBoloLongitudinalNonDominationExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloFederationCostComparisonExact as Comparison
import DASHI.Governance.BoloBoloLongitudinalPromotionGateExact as Longitudinal
import DASHI.Governance.ITIRNonDominationReappropriationExact as NonDom
import DASHI.Governance.OccupyRealizedControlAcquisitionExact as Realized

------------------------------------------------------------------------
-- LONGITUDINAL COORDINATION ADVANTAGE + NON-DOMINATION GATE
--
-- DASHI synthesis.  A nested architecture may be cheaper / more robust while
-- still concentrating realised agenda-setting, facilitation, delegation,
-- blocking, correction or reopening power.  Conversely, a non-dominating
-- authority arrangement need not be the lower-cost coordination architecture.
--
-- Therefore neither result promotes the other.  A stronger humane / egalitarian
-- governance claim must carry both results on the SAME target institution plus
-- an audit of realised control rather than relying on horizontal/anarchist/
-- democratic self-description.
------------------------------------------------------------------------

record JointLongitudinalNonDominationCertificate
    (threshold : Nat)
    (model : Comparison.CounterfactualCoordinationCostModel) : Set₂ where
  constructor joint-longitudinal-nondomination-certificate
  field
    longitudinalCoordinationAdvantage :
      Longitudinal.LongitudinalValidatedMeaningfulBoloAdvantage threshold model

    nonDomination : NonDom.NonDominationOperationalReceipt

    SameTargetBinding : Set
    sameTargetBindingWitness : SameTargetBinding

    RealizedControlAuditPassed : Set
    realizedControlAuditWitness : RealizedControlAuditPassed

    PowerConcentrationSensitivityPassed : Set
    powerConcentrationSensitivityWitness : PowerConcentrationSensitivityPassed

    RoleRotationAndMandateAuditPassed : Set
    roleRotationAndMandateAuditWitness : RoleRotationAndMandateAuditPassed

    CorrectionAndReopeningAuditPassed : Set
    correctionAndReopeningAuditWitness : CorrectionAndReopeningAuditPassed

open JointLongitudinalNonDominationCertificate public

------------------------------------------------------------------------
-- Existing empirical consumer: source-explicit coding targets for realised
-- issue surfacing, agenda framing, facilitation, role rotation, delegation,
-- block/advance, reportback, repeated influence, correction and reopening.
-- This owner reuses that surface; it does not claim those observations have
-- already been acquired for the target bolo pilot.
------------------------------------------------------------------------

realizedControlBoundaryAnchor : Realized.RealizedControlAcquisitionBoundary
realizedControlBoundaryAnchor = Realized.canonicalRealizedControlAcquisitionBoundary

nonDominationBoundaryAnchor : NonDom.ReappropriationBoundary
nonDominationBoundaryAnchor = NonDom.canonicalReappropriationBoundary

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record LongitudinalNonDominationBoundary : Set where
  constructor longitudinal-nondomination-boundary
  field
    longRunCoordinationAdvantageAutomaticallyPaysNonDomination : Bool
    nonDominationAutomaticallyPaysCoordinationAdvantage : Bool
    sameTargetBindingRequired : Bool
    realizedControlAuditRequired : Bool
    powerConcentrationSensitivityRequired : Bool
    roleRotationAndMandateAuditRequired : Bool
    correctionAndReopeningAuditRequired : Bool
    horizontalOrAnarchistLabelPaysNonDomination : Bool
    rotatingSpokesAutomaticallyProveEqualInfluence : Bool
    repeatedInfluenceAutomaticallyProvesDomination : Bool
    jointCoordinationAndNonDominationProvesOverallPoliticalSuperiority : Bool
    jointResultProvesEcologicalOrResourceViability : Bool

open LongitudinalNonDominationBoundary public

canonicalLongitudinalNonDominationBoundary : LongitudinalNonDominationBoundary
canonicalLongitudinalNonDominationBoundary =
  longitudinal-nondomination-boundary
    false false
    true true true true true
    false false false false false

canonicalLongitudinalNonDominationReceipt : GenericReceipt.GenericReceipt
canonicalLongitudinalNonDominationReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo longitudinal coordination + non-domination promotion gate"
    "DASHI.Governance.BoloBoloLongitudinalNonDominationExact"
    "JointLongitudinalNonDominationCertificate / canonicalLongitudinalNonDominationBoundary"
    "requires a repeated longitudinal meaningful coordination advantage and a proof-relevant non-domination receipt on the same target institution, together with realised-control, power-concentration, role/mandate and correction/reopening audits"
    "coordination efficiency does not establish non-domination; non-domination does not establish coordination advantage; horizontal/anarchist/democratic labels and rotating spokes do not certify equal realised influence; even the joint result does not establish ecological viability or overall political superiority"
    "agda -i . DASHI/Governance/BoloBoloLongitudinalNonDominationRegression.agda"
