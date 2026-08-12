module DASHI.Governance.IranUS2026RestitutionObservation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source-bounded 2026 Iran/US observation.
--
-- This module records the empirical distinctions motivating the generic
-- ProvenanceRestitutionBoundary.  It does not turn news reports, diplomatic
-- claims, or a preliminary memorandum into a theorem of legal liability.
--
-- Source anchors (news/policy sources; no scholarly DOI):
-- * ABC News, 18 June 2026, reporting the preliminary US-Iran memorandum and
--   reconstruction/economic-development financing framework.
-- * Council on Foreign Relations, 2026, "Trump's Iran Deal: What We Know So
--   Far", discussing Iran's reparations demand and the reconstruction package.
-- * Reuters, 9 August 2026, "Iran ties Hormuz reopening to US concessions on
--   several demands", reporting an explicit compensation demand.
------------------------------------------------------------------------

record SourceReceipt : Set where
  constructor sourceReceipt
  field
    authorOrPublisher : String
    title : String
    date : String
    doiOrBoundary : String

open SourceReceipt public

abcMOUReceipt : SourceReceipt
abcMOUReceipt =
  sourceReceipt
    "ABC News"
    "US and Iran sign memorandum aimed at ending war"
    "18 June 2026"
    "news report; no DOI"

cfrDealReceipt : SourceReceipt
cfrDealReceipt =
  sourceReceipt
    "Council on Foreign Relations"
    "Trump's Iran Deal: What We Know So Far"
    "2026"
    "policy analysis; no DOI"

reutersCompensationReceipt : SourceReceipt
reutersCompensationReceipt =
  sourceReceipt
    "Reuters"
    "Iran ties Hormuz reopening to US concessions on several demands"
    "9 August 2026"
    "news report; no DOI"

record IranUS2026Observation : Set where
  constructor iranUS2026Observation
  field
    preliminarySettlementObserved : Bool
    preliminarySettlementObservedIsTrue : preliminarySettlementObserved ≡ true
    reconstructionFinancingObserved : Bool
    reconstructionFinancingObservedIsTrue : reconstructionFinancingObserved ≡ true
    compensationDemandObserved : Bool
    compensationDemandObservedIsTrue : compensationDemandObserved ≡ true

    legalUSReparationsAdmissionEstablished : Bool
    legalUSReparationsAdmissionEstablishedIsFalse :
      legalUSReparationsAdmissionEstablished ≡ false

    frozenAssetReleaseAutomaticallyCompensation : Bool
    frozenAssetReleaseAutomaticallyCompensationIsFalse :
      frozenAssetReleaseAutomaticallyCompensation ≡ false

canonicalIranUS2026Observation : IranUS2026Observation
canonicalIranUS2026Observation =
  iranUS2026Observation
    true refl
    true refl
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- The important formal use is route plurality: injury provenance can feed a
-- reparative/bargaining branch rather than only an enemy->coercion branch.
------------------------------------------------------------------------

data IranPolicyRoute : Set where
  coerciveThreat settlement reconstruction compensationBargaining : IranPolicyRoute

record IranPolicyTrajectory : Set where
  constructor iranPolicyTrajectory
  field
    initial : IranPolicyRoute
    next : IranPolicyRoute
    later : IranPolicyRoute
    currentBargaining : IranPolicyRoute

canonicalIranPolicyTrajectory : IranPolicyTrajectory
canonicalIranPolicyTrajectory =
  iranPolicyTrajectory
    coerciveThreat
    settlement
    reconstruction
    compensationBargaining

record EmpiricalAuthorityBoundary : Set where
  constructor empiricalAuthorityBoundary
  field
    observationIsLegalJudgment : Bool
    observationIsLegalJudgmentIsFalse : observationIsLegalJudgment ≡ false
    reconstructionEqualsAdmittedReparations : Bool
    reconstructionEqualsAdmittedReparationsIsFalse :
      reconstructionEqualsAdmittedReparations ≡ false

canonicalEmpiricalAuthorityBoundary : EmpiricalAuthorityBoundary
canonicalEmpiricalAuthorityBoundary =
  empiricalAuthorityBoundary false refl false refl
