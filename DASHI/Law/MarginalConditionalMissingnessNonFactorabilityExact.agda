module DASHI.Law.MarginalConditionalMissingnessNonFactorabilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as NF

------------------------------------------------------------------------
-- Equal marginal missingness does not determine where missingness is
-- concentrated in the encounter fibre.
------------------------------------------------------------------------

data SearchStratum : Set where
  searched notSearched : SearchStratum

data MissingnessPattern : Set where
  missingConcentratedAfterSearch
  missingConcentratedWithoutSearch : MissingnessPattern

record StratifiedMissingnessPopulation : Set where
  constructor stratifiedMissingnessPopulation
  field
    totalRecords : ℕ
    totalMissing : ℕ
    missingAfterSearch : ℕ
    missingWithoutSearch : ℕ
    pattern : MissingnessPattern
    populationReference : String

open StratifiedMissingnessPopulation public

marginalMissingnessObserver : StratifiedMissingnessPopulation → ℕ
marginalMissingnessObserver = totalMissing

conditionalMissingnessStructure : StratifiedMissingnessPopulation → MissingnessPattern
conditionalMissingnessStructure = pattern

searchedConcentratedPopulation : StratifiedMissingnessPopulation
searchedConcentratedPopulation = stratifiedMissingnessPopulation
  10 2 2 0 missingConcentratedAfterSearch
  "synthetic population: same total missingness, all missing records in searched stratum"

nonSearchedConcentratedPopulation : StratifiedMissingnessPopulation
nonSearchedConcentratedPopulation = stratifiedMissingnessPopulation
  10 2 0 2 missingConcentratedWithoutSearch
  "synthetic population: same total missingness, all missing records in non-searched stratum"

sameMarginalMissingness :
  marginalMissingnessObserver searchedConcentratedPopulation ≡
  marginalMissingnessObserver nonSearchedConcentratedPopulation
sameMarginalMissingness = refl

conditionalPatternsDiffer :
  conditionalMissingnessStructure searchedConcentratedPopulation ≡
  conditionalMissingnessStructure nonSearchedConcentratedPopulation → ⊥
conditionalPatternsDiffer ()

marginalMissingnessNonFactorability :
  NF.NonFactorabilityWitness marginalMissingnessObserver conditionalMissingnessStructure
marginalMissingnessNonFactorability = NF.nonFactorabilityWitness
  searchedConcentratedPopulation
  nonSearchedConcentratedPopulation
  sameMarginalMissingness
  conditionalPatternsDiffer

marginalRateCannotReconstructConditionalMechanism :
  NF.FactorsThrough marginalMissingnessObserver conditionalMissingnessStructure → ⊥
marginalRateCannotReconstructConditionalMechanism =
  NF.witnessRulesOutEveryFlatFactorisation marginalMissingnessNonFactorability

------------------------------------------------------------------------
-- Recharting the same marginal rate cannot repair the lost conditional axis.
------------------------------------------------------------------------

marginalRechartCannotRecoverConditionalMechanism :
  ∀ {Recharted : Set} →
  (rechart : ℕ → Recharted) →
  NF.FactorsThrough
    (λ population → rechart (marginalMissingnessObserver population))
    conditionalMissingnessStructure → ⊥
marginalRechartCannotRecoverConditionalMechanism rechart =
  NF.rechartingCannotRecoverErasedPhenomenon
    rechart marginalMissingnessNonFactorability

------------------------------------------------------------------------
-- Stratification fibres.  Search/outcome, officer and place are separate
-- axes; a marginal total cannot certify closure of any conditional profile.
------------------------------------------------------------------------

data OutcomeAxis : Set where
  searchOccurred searchDidNotOccur : OutcomeAxis

data OfficerAxis : Set where
  officerA officerB officerUnknown : OfficerAxis

data PlaceAxis : Set where
  placeA placeB placeUnknown : PlaceAxis

record MissingnessStratum : Set where
  constructor missingnessStratum
  field
    outcomeAxis : OutcomeAxis
    officerAxis : OfficerAxis
    placeAxis : PlaceAxis
    observedCount : ℕ
    missingCount : ℕ
    stratumReference : String

open MissingnessStratum public

record ConditionalMissingnessAudit : Set where
  constructor conditionalMissingnessAudit
  field
    overallMissingCount : ℕ
    searchedMissingCount : ℕ
    nonSearchedMissingCount : ℕ
    officerStratificationClosed : Bool
    placeStratificationClosed : Bool
    auditReference : String

open ConditionalMissingnessAudit public

canonicalConditionalAudit : ConditionalMissingnessAudit
canonicalConditionalAudit = conditionalMissingnessAudit
  2 2 0 false false
  "synthetic conditional audit; outcome closed, officer/place strata still open"

------------------------------------------------------------------------
-- BIDI routing: headline marginal missingness requires only the marginal count;
-- outcome-, officer-, and place-conditioned claims require their own crosstabs.
------------------------------------------------------------------------

data MissingnessStructureClaim : Set where
  marginalMissingnessRate
  outcomeConditionedMissingness
  officerConditionedMissingness
  placeConditionedMissingness : MissingnessStructureClaim

data MissingnessStructureProducer : Set where
  marginalMissingCountProducer
  outcomeMissingnessCrossTabProducer
  officerMissingnessCrossTabProducer
  placeMissingnessCrossTabProducer : MissingnessStructureProducer

reverseMissingnessStructure : MissingnessStructureClaim → MissingnessStructureProducer
reverseMissingnessStructure marginalMissingnessRate = marginalMissingCountProducer
reverseMissingnessStructure outcomeConditionedMissingness = outcomeMissingnessCrossTabProducer
reverseMissingnessStructure officerConditionedMissingness = officerMissingnessCrossTabProducer
reverseMissingnessStructure placeConditionedMissingness = placeMissingnessCrossTabProducer

record MissingnessStructureCutset : Set where
  constructor missingnessStructureCutset
  field
    marginalClosed : Bool
    outcomeCrossTabClosed : Bool
    officerCrossTabClosed : Bool
    placeCrossTabClosed : Bool
    cutsetReference : String

open MissingnessStructureCutset public

data MissingnessStructureResidual : Set where
  marginalResidual outcomeCrossTabResidual officerCrossTabResidual placeCrossTabResidual structureClosed : MissingnessStructureResidual

firstMissingnessStructureResidual : MissingnessStructureClaim → MissingnessStructureCutset → MissingnessStructureResidual
firstMissingnessStructureResidual marginalMissingnessRate c with marginalClosed c
... | false = marginalResidual
... | true = structureClosed
firstMissingnessStructureResidual outcomeConditionedMissingness c with marginalClosed c
... | false = marginalResidual
... | true with outcomeCrossTabClosed c
...   | false = outcomeCrossTabResidual
...   | true = structureClosed
firstMissingnessStructureResidual officerConditionedMissingness c with marginalClosed c
... | false = marginalResidual
... | true with officerCrossTabClosed c
...   | false = officerCrossTabResidual
...   | true = structureClosed
firstMissingnessStructureResidual placeConditionedMissingness c with marginalClosed c
... | false = marginalResidual
... | true with placeCrossTabClosed c
...   | false = placeCrossTabResidual
...   | true = structureClosed

canonicalMarginalOnlyCutset : MissingnessStructureCutset
canonicalMarginalOnlyCutset = missingnessStructureCutset true false false false
  "marginal missing count closed; all conditional stratification producers open"

marginalDoesNotCloseOutcomeConditioning :
  firstMissingnessStructureResidual outcomeConditionedMissingness canonicalMarginalOnlyCutset ≡ outcomeCrossTabResidual
marginalDoesNotCloseOutcomeConditioning = refl

marginalDoesNotCloseOfficerConditioning :
  firstMissingnessStructureResidual officerConditionedMissingness canonicalMarginalOnlyCutset ≡ officerCrossTabResidual
marginalDoesNotCloseOfficerConditioning = refl

marginalDoesNotClosePlaceConditioning :
  firstMissingnessStructureResidual placeConditionedMissingness canonicalMarginalOnlyCutset ≡ placeCrossTabResidual
marginalDoesNotClosePlaceConditioning = refl

record MarginalConditionalMissingnessBoundary : Set where
  constructor marginalConditionalMissingnessBoundary
  field
    sameMarginalImpliesSameConditionalMechanism : Bool
    sameMarginalImpliesSameConditionalMechanismIsFalse : sameMarginalImpliesSameConditionalMechanism ≡ false
    marginalRateProvesOfficerPattern : Bool
    marginalRateProvesOfficerPatternIsFalse : marginalRateProvesOfficerPattern ≡ false
    marginalRateProvesPlacePattern : Bool
    marginalRateProvesPlacePatternIsFalse : marginalRateProvesPlacePattern ≡ false

canonicalMarginalConditionalBoundary : MarginalConditionalMissingnessBoundary
canonicalMarginalConditionalBoundary =
  marginalConditionalMissingnessBoundary false refl false refl false refl
