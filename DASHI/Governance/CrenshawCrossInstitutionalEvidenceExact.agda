module DASHI.Governance.CrenshawCrossInstitutionalEvidenceExact where

-- K1-K3: source-specific passage and causal requirements across court,
-- school discipline, policing and historical racial order.
-- Crenshaw's 1988/1991 articles and coauthored 2015 reports motivate
-- this original DASHI interface, but DO NOT establish any particular
-- causal chain or make the author a litigant/counsel for the older cases.
open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.CrenshawRightsReformDualEffectExact as Reform

data Institution : Set where
  employmentCourt schoolDiscipline policeAgency detentionSystem :
    Institution

data ClaimKind : Set where
  doctrinalExclusion schoolExclusion policingHarm custodialOutcome :
    ClaimKind

record InstitutionClaim : Set where
  constructor institution-claim
  field
    institution : Institution
    claimKind : ClaimKind

open InstitutionClaim public

-- A report about one domain is not interchangeable with the others.
data EvidentiaryDomain : Set where
  judicialRecord schoolRecord policingRecord custodyRecord :
    EvidentiaryDomain

data Supports : EvidentiaryDomain → ClaimKind → Set where
  judicialSupportsDoctrine : Supports judicialRecord doctrinalExclusion
  schoolSupportsExclusion : Supports schoolRecord schoolExclusion
  policingSupportsHarm : Supports policingRecord policingHarm
  custodySupportsOutcome : Supports custodyRecord custodialOutcome

judicialTranscriptCannotPayPoliceHarm :
  Supports judicialRecord policingHarm → ⊥
judicialTranscriptCannotPayPoliceHarm ()

schoolDisciplineDoesNotByItselfPayCustodialOutcome :
  Supports schoolRecord custodialOutcome → ⊥
schoolDisciplineDoesNotByItselfPayCustodialOutcome ()

policeReportDoesNotByItselfPayLegalDoctrine :
  Supports policingRecord doctrinalExclusion → ⊥
policeReportDoesNotByItselfPayLegalDoctrine ()

-- The causal historical weld is parametrised by external source and
-- inference rules; the interface offers NO self-authorizing witness.
record HistoricalCausalValidator
  (History School Police Custody : Set) : Set₁ where
  field
    originalHistorySource : History → Set
    sourcePaidHistoricalMechanism : History → School → Set
    schoolToPoliceSource : School → Police → Set
    policeToCustodySource : Police → Custody → Set
    alternativeExplanationsConsidered : School → Custody → Set
    participantDataAdmissible : School → Custody → Set

open HistoricalCausalValidator public

record HistoricalCarceralTrace
  {History School Police Custody : Set}
  (validator : HistoricalCausalValidator History School Police Custody)
  (h : History) (s : School) (p : Police) (c : Custody) : Set where
  constructor historical-carceral-trace
  field
    historicalSource : originalHistorySource validator h
    historicalMechanism :
      sourcePaidHistoricalMechanism validator h s
    schoolPolicingWeld : schoolToPoliceSource validator s p
    policingCustodyWeld : policeToCustodySource validator p c
    alternatives : alternativeExplanationsConsidered validator s c
    ethics : participantDataAdmissible validator s c

open HistoricalCarceralTrace public

traceRequiresActualHistoricalMechanism :
  ∀ {History School Police Custody : Set}
    {v : HistoricalCausalValidator History School Police Custody}
    {h : History} {s : School} {p : Police} {c : Custody} →
  HistoricalCarceralTrace v h s p c →
  sourcePaidHistoricalMechanism v h s
traceRequiresActualHistoricalMechanism = historicalMechanism

traceRequiresAlternativeCauseReview :
  ∀ {History School Police Custody : Set}
    {v : HistoricalCausalValidator History School Police Custody}
    {h : History} {s : School} {p : Police} {c : Custody} →
  HistoricalCarceralTrace v h s p c →
  alternativeExplanationsConsidered v s c
traceRequiresAlternativeCauseReview = alternatives

-- A negative control: possession of modern school and police reports
-- cannot make an independent historical lineage receipt appear.
data DemoHistory : Set where onlyUnverifiedHistory : DemoHistory
data DemoSchool : Set where observedSchool : DemoSchool
data DemoPolice : Set where observedPolice : DemoPolice
data DemoCustody : Set where observedCustody : DemoCustody

missingHistoricalWeld : HistoricalCausalValidator
  DemoHistory DemoSchool DemoPolice DemoCustody
missingHistoricalWeld = record
  { originalHistorySource = λ _ → ⊥
  ; sourcePaidHistoricalMechanism = λ _ _ → ⊥
  ; schoolToPoliceSource = λ _ _ → ⊤
  ; policeToCustodySource = λ _ _ → ⊤
  ; alternativeExplanationsConsidered = λ _ _ → ⊤
  ; participantDataAdmissible = λ _ _ → ⊤
  }

modernReportsCannotManufactureHistoricalLineage :
  HistoricalCarceralTrace missingHistoricalWeld
    onlyUnverifiedHistory observedSchool observedPolice observedCustody → ⊥
modernReportsCannotManufactureHistoricalLineage receipt =
  historicalSource receipt

-- Do not recast legal rights as either sufficient for material freedom
-- or intrinsically worthless: both source-motivated possibilities remain.
reformRecognitionDoesNotDetermineMaterialChange :
  INF.FactorsThrough
    Reform.formalRecognition Reform.materialReallocation → ⊥
reformRecognitionDoesNotDetermineMaterialChange =
  Reform.formalRightDoesNotGuaranteeMaterialTransformation
