module DASHI.Governance.CrenshawCarceralMissingnessExact where

-- Source motivation: Crenshaw, Ritchie et al. (2015), Say Her Name,
-- explicitly non-exhaustive police-violence documentation. A closed
-- record and a negative report are different propositions.
-- Finite countermodel is DASHI original; no actual victim or agency
-- is assigned a synthetic state.

open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as INF

data ReportingWorld : Set where
  harmOutsideRecordedCorpus noHarmInRecordedPeriod : ReportingWorld

-- In both worlds this particular non-exhaustive record contains no entry.
entryInSelectedCorpus : ReportingWorld → Bool
entryInSelectedCorpus harmOutsideRecordedCorpus = false
entryInSelectedCorpus noHarmInRecordedPeriod = false

independentHarm : ReportingWorld → Bool
independentHarm harmOutsideRecordedCorpus = true
independentHarm noHarmInRecordedPeriod = false

missingRecordCannotDecideHarm :
  INF.NonFactorabilityWitness
    entryInSelectedCorpus independentHarm
missingRecordCannotDecideHarm =
  INF.nonFactorabilityWitness
    harmOutsideRecordedCorpus noHarmInRecordedPeriod refl (λ ())

recordAbsenceDoesNotProveAbsenceOfHarm :
  INF.FactorsThrough entryInSelectedCorpus independentHarm → ⊥
recordAbsenceDoesNotProveAbsenceOfHarm =
  INF.witnessRulesOutEveryFlatFactorisation
    missingRecordCannotDecideHarm

anyRecordRechartStillCannotEstablishAbsence :
  ∀ {R : Set} (f : Bool → R) →
  INF.FactorsThrough
    (λ world → f (entryInSelectedCorpus world))
    independentHarm → ⊥
anyRecordRechartStillCannotEstablishAbsence f =
  INF.rechartingCannotRecoverErasedPhenomenon
    f missingRecordCannotDecideHarm

-- A genuine institution-level coverage claim needs its own completeness
-- evidence and precise population, time window, incidents and reporting
-- criteria; a citation to an explicitly non-exhaustive report is not enough.
record CoverageVerification (RecordScope : Set) : Set₁ where
  field
    sourcePopulationDefined : RecordScope → Set
    reportingWindowDefined : RecordScope → Set
    incidentDefinitionAudited : RecordScope → Set
    missingnessMethodEvaluated : RecordScope → Set
    independentDataCompared : RecordScope → Set

-- Observation gaps are not themselves proof of positive incidents.
-- The countermodel refutes deduction in either direction from the same
-- selected corpus surface alone.
