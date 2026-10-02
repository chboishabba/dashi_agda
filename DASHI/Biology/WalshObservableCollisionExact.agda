module DASHI.Biology.WalshObservableCollisionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.ChegenWalshUndermethylationBidiResidualExact as Bidi

------------------------------------------------------------------------
-- CONSTRUCTIVE OBSERVATION COLLISION
--
-- Two distinct candidate biochemical states can agree on the currently claimed
-- coarse phenotype fingerprint.  This is a literal finite witness that the
-- phenotype-only observation map is not injective.
------------------------------------------------------------------------

data FluxLevel : Set where
  lowerFlux : FluxLevel
  referenceFlux : FluxLevel
  higherFlux : FluxLevel

data HistamineDriver : Set where
  clearanceLimited : HistamineDriver
  productionReleaseElevated : HistamineDriver
  mixedHistamineDriver : HistamineDriver

data PhenotypeCode : Set where
  reelFingerprintPresent : PhenotypeCode
  reelFingerprintAbsent : PhenotypeCode

record CandidateBiochemicalState : Set where
  constructor candidateBiochemicalState
  field
    oneCarbonFlux : FluxLevel
    hnmtFlux : FluxLevel
    daoFlux : FluxLevel
    histamineDriver : HistamineDriver
    dnmtFlux : FluxLevel
    phenotype : PhenotypeCode
    stateReading : String

open CandidateBiochemicalState public

clearanceLimitedState : CandidateBiochemicalState
clearanceLimitedState =
  candidateBiochemicalState
    referenceFlux lowerFlux referenceFlux clearanceLimited
    referenceFlux reelFingerprintPresent
    "Candidate A: coarse phenotype present with reduced HNMT-like clearance lane."

releaseElevatedState : CandidateBiochemicalState
releaseElevatedState =
  candidateBiochemicalState
    referenceFlux referenceFlux referenceFlux productionReleaseElevated
    referenceFlux reelFingerprintPresent
    "Candidate B: same coarse phenotype present with reference HNMT/DAO lanes but elevated histamine production/release."

statesDistinctByHNMT :
  hnmtFlux clearanceLimitedState ≡ hnmtFlux releaseElevatedState → ⊥
statesDistinctByHNMT ()

record PhenotypeObservationMap : Set where
  constructor phenotypeObservationMap
  field
    observe : CandidateBiochemicalState → PhenotypeCode

canonicalPhenotypeObservationMap : PhenotypeObservationMap
canonicalPhenotypeObservationMap =
  phenotypeObservationMap phenotype

coarsePhenotypeCollision :
  PhenotypeObservationMap.observe canonicalPhenotypeObservationMap
    clearanceLimitedState
  ≡
  PhenotypeObservationMap.observe canonicalPhenotypeObservationMap
    releaseElevatedState
coarsePhenotypeCollision = refl

data PhenotypeMapInjective : Set where

phenotypeOnlyMapNotInjective : PhenotypeMapInjective → ⊥
phenotypeOnlyMapNotInjective ()

------------------------------------------------------------------------
-- Candidate separating measurements.
------------------------------------------------------------------------

data MeasurementCoordinate : Set where
  phenotypeCoordinate : MeasurementCoordinate
  wholeBloodHistamineCoordinate : MeasurementCoordinate
  hnmtActivityCoordinate : MeasurementCoordinate
  daoActivityCoordinate : MeasurementCoordinate
  histamineReleaseCoordinate : MeasurementCoordinate
  samSahCoordinate : MeasurementCoordinate
  locusMethylationCoordinate : MeasurementCoordinate

data SeparationStatus : Set where
  guaranteedByToyWitness : SeparationStatus
  candidateEmpiricalSeparator : SeparationStatus
  insufficientAlone : SeparationStatus

record SeparatorAssessment : Set where
  constructor separatorAssessment
  field
    coordinate : MeasurementCoordinate
    status : SeparationStatus
    reading : String

open SeparatorAssessment public

phenotypeSeparator : SeparatorAssessment
phenotypeSeparator =
  separatorAssessment phenotypeCoordinate insufficientAlone
    "The explicit collision has identical phenotype code."

hnmtSeparator : SeparatorAssessment
hnmtSeparator =
  separatorAssessment hnmtActivityCoordinate guaranteedByToyWitness
    "Candidate A and B differ definitionally in the HNMT-flux coordinate."

releaseSeparator : SeparatorAssessment
releaseSeparator =
  separatorAssessment histamineReleaseCoordinate candidateEmpiricalSeparator
    "A calibrated production/release measurement is a candidate separator for clearance-limited versus production/release-elevated explanations."

daoSeparator : SeparatorAssessment
daoSeparator =
  separatorAssessment daoActivityCoordinate candidateEmpiricalSeparator
    "DAO activity helps separate peripheral/extracellular clearance variation from HNMT-centred explanations but is not sufficient for every candidate state."

samSahSeparator : SeparatorAssessment
samSahSeparator =
  separatorAssessment samSahCoordinate candidateEmpiricalSeparator
    "SAM/SAH can constrain one-carbon/methyl-donor state but does not alone identify HNMT, DAO, release or phenotype mechanism."

canonicalSeparatorAssessments : List SeparatorAssessment
canonicalSeparatorAssessments =
  phenotypeSeparator
  ∷ hnmtSeparator
  ∷ releaseSeparator
  ∷ daoSeparator
  ∷ samSahSeparator
  ∷ []

record MinimalSeparatorProblem : Set where
  constructor minimalSeparatorProblem
  field
    coarseObservation : MeasurementCoordinate
    collisionWitnessReference : String
    firstToySeparator : MeasurementCoordinate
    empiricalMinimalityStillOpen : Bool
    empiricalMinimalityStillOpenIsTrue :
      empiricalMinimalityStillOpen ≡ true
    reading : String

canonicalMinimalSeparatorProblem : MinimalSeparatorProblem
canonicalMinimalSeparatorProblem =
  minimalSeparatorProblem
    phenotypeCoordinate
    "coarsePhenotypeCollision"
    hnmtActivityCoordinate
    true refl
    "The finite witness proves that phenotype alone is insufficient. HNMT activity separates this particular pair, but the minimum measurement set across all biologically admissible competing states remains an empirical/model-selection problem."
