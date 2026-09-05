module DASHI.Law.MarginalConditionalMissingnessValidation where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Law.MarginalConditionalMissingnessNonFactorabilityExact as Conditional

sameHeadlineMissingnessCanHideDifferentConditionalStructures :
  NF.NonFactorabilityWitness
    Conditional.marginalMissingnessObserver
    Conditional.conditionalMissingnessStructure
sameHeadlineMissingnessCanHideDifferentConditionalStructures =
  Conditional.marginalMissingnessNonFactorability

marginalMissingnessCannotReconstructConditionalMechanism :
  NF.FactorsThrough
    Conditional.marginalMissingnessObserver
    Conditional.conditionalMissingnessStructure → ⊥
marginalMissingnessCannotReconstructConditionalMechanism =
  Conditional.marginalRateCannotReconstructConditionalMechanism

sameMarginalCountRegression :
  Conditional.marginalMissingnessObserver Conditional.searchedConcentratedPopulation ≡
  Conditional.marginalMissingnessObserver Conditional.nonSearchedConcentratedPopulation
sameMarginalCountRegression = Conditional.sameMarginalMissingness

outcomeConditioningNeedsOwnCrossTab :
  Conditional.firstMissingnessStructureResidual
    Conditional.outcomeConditionedMissingness
    Conditional.canonicalMarginalOnlyCutset
  ≡ Conditional.outcomeCrossTabResidual
outcomeConditioningNeedsOwnCrossTab =
  Conditional.marginalDoesNotCloseOutcomeConditioning

officerConditioningNeedsOwnCrossTab :
  Conditional.firstMissingnessStructureResidual
    Conditional.officerConditionedMissingness
    Conditional.canonicalMarginalOnlyCutset
  ≡ Conditional.officerCrossTabResidual
officerConditioningNeedsOwnCrossTab =
  Conditional.marginalDoesNotCloseOfficerConditioning

placeConditioningNeedsOwnCrossTab :
  Conditional.firstMissingnessStructureResidual
    Conditional.placeConditionedMissingness
    Conditional.canonicalMarginalOnlyCutset
  ≡ Conditional.placeCrossTabResidual
placeConditioningNeedsOwnCrossTab =
  Conditional.marginalDoesNotClosePlaceConditioning
