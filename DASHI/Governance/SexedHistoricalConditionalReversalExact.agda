module DASHI.Governance.SexedHistoricalConditionalReversalExact where

------------------------------------------------------------------------
-- CONDITIONAL / MARGINAL REVERSAL FOR SEXED HISTORICAL CONSTRUCTION STUDIES
--
-- Synthetic finite calibration only.  The fixture demonstrates that a pooled
-- male/female contrast can reverse the direction seen within each declared
-- historical/power stratum when group composition differs across strata.
--
-- This is a design warning, not an empirical claim about any population.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.SexedHistoricalStatisticalExperimentHyperfabricExact as Stats
import DASHI.Governance.SexedHistoricalCoConstitutionHyperfabricExact as Hyper

------------------------------------------------------------------------
-- Two coarse strata and exact integer cells.
------------------------------------------------------------------------

data StudyStratum : Set where
  highOpportunityStratum
  lowOpportunityStratum
  : StudyStratum

record BinomialCell : Set where
  constructor binomial-cell
  field
    successes : Nat
    total : Nat

open BinomialCell public

-- Female-coded outcome rate exceeds male-coded outcome rate in each stratum:
--
--   high: female 9/10, male 80/100
--   low : female 20/100, male 1/10
--
-- but pooled totals reverse:
--
--   female 29/110, male 81/110.
--
-- The numbers are intentionally synthetic and merely make composition-induced
-- reversal explicit.

femaleHigh : BinomialCell
femaleHigh = binomial-cell 9 10

maleHigh : BinomialCell
maleHigh = binomial-cell 80 100

femaleLow : BinomialCell
femaleLow = binomial-cell 20 100

maleLow : BinomialCell
maleLow = binomial-cell 1 10

femalePooled : BinomialCell
femalePooled = binomial-cell 29 110

malePooled : BinomialCell
malePooled = binomial-cell 81 110

femaleHighSuccesses : successes femaleHigh ≡ 9
femaleHighSuccesses = refl

maleHighSuccesses : successes maleHigh ≡ 80
maleHighSuccesses = refl

femaleLowSuccesses : successes femaleLow ≡ 20
femaleLowSuccesses = refl

maleLowSuccesses : successes maleLow ≡ 1
maleLowSuccesses = refl

femalePooledSuccesses : successes femalePooled ≡ 29
femalePooledSuccesses = refl

malePooledSuccesses : successes malePooled ≡ 81
malePooledSuccesses = refl

------------------------------------------------------------------------
-- Typed direction surface.  We do not smuggle a division/order library into
-- this calibration owner; the exact integer cells above remain available for
-- downstream numerical replay.
------------------------------------------------------------------------

data ContrastDirection : Set where
  femaleHigher
  maleHigher
  equalOrUnresolved
  : ContrastDirection

withinStratumDirection : StudyStratum → ContrastDirection
withinStratumDirection highOpportunityStratum = femaleHigher
withinStratumDirection lowOpportunityStratum = femaleHigher

pooledDirection : ContrastDirection
pooledDirection = maleHigher

withinHighDiffersFromPooled :
  withinStratumDirection highOpportunityStratum ≡ pooledDirection → ⊥
withinHighDiffersFromPooled ()

withinLowDiffersFromPooled :
  withinStratumDirection lowOpportunityStratum ≡ pooledDirection → ⊥
withinLowDiffersFromPooled ()

------------------------------------------------------------------------
-- Same recorded-sex surface can hide different stratum composition.
------------------------------------------------------------------------

data CompositionFineState : Set where
  femaleMostlyHighOpportunity
  femaleMostlyLowOpportunity
  : CompositionFineState

recordedSex : CompositionFineState → Stats.RecordedSexCategory
recordedSex _ = Stats.recordedFemale

composition : CompositionFineState → StudyStratum
composition femaleMostlyHighOpportunity = highOpportunityStratum
composition femaleMostlyLowOpportunity = lowOpportunityStratum

recordedSexCannotRecoverStratumComposition :
  INF.FactorsThrough recordedSex composition → ⊥
recordedSexCannotRecoverStratumComposition =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      femaleMostlyHighOpportunity
      femaleMostlyLowOpportunity
      refl
      (λ ()))

------------------------------------------------------------------------
-- Construction and power remain distinct conditioning variables.
------------------------------------------------------------------------

record ConditioningCell : Set where
  constructor conditioning-cell
  field
    construction : Stats.ConstructionDirection
    power : Hyper.PowerLevel
    stratum : StudyStratum

open ConditioningCell public

femaleSelfHighPower : ConditioningCell
femaleSelfHighPower =
  conditioning-cell Stats.feminineToFeminine Hyper.highPower highOpportunityStratum

femaleSelfLowPower : ConditioningCell
femaleSelfLowPower =
  conditioning-cell Stats.feminineToFeminine Hyper.lowPower lowOpportunityStratum

sameConstructionDifferentPower :
  construction femaleSelfHighPower ≡ construction femaleSelfLowPower
sameConstructionDifferentPower = refl

sameConstructionDoesNotForceSameStratumPower :
  power femaleSelfHighPower ≡ power femaleSelfLowPower → ⊥
sameConstructionDoesNotForceSameStratumPower ()

------------------------------------------------------------------------
-- No-promotion boundaries.
------------------------------------------------------------------------

data PooledSexDifferencePromotesWithinStratumEffect : Set where

data MarginalReversalPromotesBiasProof : Set where

data StratificationPromotesCausalIdentification : Set where

data ConditionalAssociationPromotesSexEssence : Set where

pooledSexDifferenceDoesNotPromoteWithinStratumEffect :
  PooledSexDifferencePromotesWithinStratumEffect → ⊥
pooledSexDifferenceDoesNotPromoteWithinStratumEffect ()

marginalReversalDoesNotByItselfProveBias :
  MarginalReversalPromotesBiasProof → ⊥
marginalReversalDoesNotByItselfProveBias ()

stratificationDoesNotPromoteCausalIdentification :
  StratificationPromotesCausalIdentification → ⊥
stratificationDoesNotPromoteCausalIdentification ()

conditionalAssociationDoesNotPromoteSexEssence :
  ConditionalAssociationPromotesSexEssence → ⊥
conditionalAssociationDoesNotPromoteSexEssence ()

record SexedHistoricalConditionalReversalBoundary : Set where
  constructor sexed-historical-conditional-reversal-boundary
  field
    pooledDirectionDeterminesConditionalDirection : Bool
    recordedSexDeterminesStratumComposition : Bool
    constructionDirectionDeterminesPowerStratum : Bool
    stratificationEqualsCausalIdentification : Bool
    reversalAutomaticallyProvesConfounding : Bool
    exactSyntheticCountsRetained : Bool

canonicalSexedHistoricalConditionalReversalBoundary :
  SexedHistoricalConditionalReversalBoundary
canonicalSexedHistoricalConditionalReversalBoundary =
  sexed-historical-conditional-reversal-boundary
    false false false false false true
