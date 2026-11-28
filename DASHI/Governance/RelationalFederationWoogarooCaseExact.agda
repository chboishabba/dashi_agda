module DASHI.Governance.RelationalFederationWoogarooCaseExact where

-- DASHI cross-owner case consumer. Original source authors and claim
-- boundaries remain in the imported Woogaroo owners. No new legal finding,
-- field measurement, ecological equivalence or intervention authority.
-- See Docs/RelationalFederationWoogarooCase20261129.md.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Law.SensibLawWoogarooPriorActionAuditScope20261110Exact as Audit
import DASHI.Law.SensibLawWoogarooOperativeInstrumentEvidenceCut20261109Exact as Instrument
import DASHI.Law.SensibLawWoogarooMWWJointGainConfidence20261109Exact as Offset
import DASHI.Law.SensibLawWoogarooGasSecondThirdOrderNonPromotion20261030Exact as Gas

priorAudit : Audit.GovernmentAuditSummary
priorAudit = Audit.original2025AuditSummary

priorAuditCannotPayCurrentIdentity :
  Audit.SameAction Audit.priorSpringview20147306
    Audit.currentSpringview20198575 → ⊥
priorAuditCannotPayCurrentIdentity = Audit.originalPriorAuditIsNotCurrentApprovalAudit

operativeSource : Instrument.Revision
operativeSource = Instrument.signedApproval

finalPDSource : Instrument.Revision
finalPDSource = Instrument.finalJulyPD

historicalOffsetNumerator : Nat → Nat → Nat
historicalOffsetNumerator = Offset.jointNumerator

meetingCannotDetermineAgenda :
  NF.FactorsThrough Gas.diary Gas.agenda → ⊥
meetingCannotDetermineAgenda = Gas.diaryCannotDetermineGasAgenda

connectionCannotDetermineBeneficiary :
  NF.FactorsThrough Gas.connection Gas.beneficiary → ⊥
connectionCannotDetermineBeneficiary = Gas.connectionCannotDetermineBeneficiary

-- A synthetic test only: same modeled compensation label, distinct
-- continuity of original habitat function. Not a claim about the case.
data HabitatFixture : Set where
  continuityRetained continuityLost : HabitatFixture

modelledCoverage : HabitatFixture → Nat
modelledCoverage _ = 100

originalHabitatContinuity : HabitatFixture → Bool
originalHabitatContinuity continuityRetained = true
originalHabitatContinuity continuityLost = false

coverageCannotDetermineContinuity :
  NF.FactorsThrough modelledCoverage originalHabitatContinuity → ⊥
coverageCannotDetermineContinuity =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness continuityRetained continuityLost refl (λ ()))

-- All witnesses must be for the same supplied action/revision/parcel/time
-- target, not disparate existential receipts. Scope census, evidence
-- authentication and authority remain external obligations.
record CaseAdmission (Target : Set)
  (InstrumentIdentity SpatialIdentity CumulativeImpact
   EcologicalFunction MaterialProvision Authority Outcome : Target → Set)
  (t : Target) : Set where
  field
    instrumentWitness : InstrumentIdentity t
    spatialWitness : SpatialIdentity t
    cumulativeWitness : CumulativeImpact t
    ecologicalWitness : EcologicalFunction t
    provisioningWitness : MaterialProvision t
    authorityWitness : Authority t
    outcomeWitness : Outcome t
