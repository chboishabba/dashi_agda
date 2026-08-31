module DASHI.Governance.SexedHistoricalDialecticalJoinAdaptiveSearchExact where

------------------------------------------------------------------------
-- ADAPTIVE BIDI SEARCH FOR A PRODUCTIVE DIALECTICAL JOIN
--
-- Candidate joins can agree on a coarse 'both contributions represented'
-- surface while differing on whether they preserve the order residual or add a
-- genuinely new affordance.  The next measurement is therefore selected by
-- the unresolved consumer obligation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.EpistemicSuspensionExact as Suspension
import DASHI.Governance.SexedHistoricalProductiveDialecticalFibreJoinExact as Join

------------------------------------------------------------------------
-- 1. Candidate join fibre.
------------------------------------------------------------------------

data CandidateJoin : Set where
  coexistenceOnly
  residualPreservingNoExpansion
  productiveRelationalJoin
  : CandidateJoin

data CoarseCandidateSurface : Set where bothContributionsVisible : CoarseCandidateSurface

data ResidualStatus : Set where residualErased residualRetained : ResidualStatus

data ExpansionStatus : Set where noStrictExpansion strictExpansion : ExpansionStatus

coarseCandidate : CandidateJoin → CoarseCandidateSurface
coarseCandidate _ = bothContributionsVisible

residualStatus : CandidateJoin → ResidualStatus
residualStatus coexistenceOnly = residualErased
residualStatus residualPreservingNoExpansion = residualRetained
residualStatus productiveRelationalJoin = residualRetained

expansionStatus : CandidateJoin → ExpansionStatus
expansionStatus coexistenceOnly = noStrictExpansion
expansionStatus residualPreservingNoExpansion = noStrictExpansion
expansionStatus productiveRelationalJoin = strictExpansion

coarseCandidateCannotRecoverExpansion :
  INF.FactorsThrough coarseCandidate expansionStatus → ⊥
coarseCandidateCannotRecoverExpansion =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      residualPreservingNoExpansion
      productiveRelationalJoin
      refl
      (λ ()))

residualAloneCannotRecoverProductivity :
  INF.FactorsThrough residualStatus expansionStatus → ⊥
residualAloneCannotRecoverProductivity =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      residualPreservingNoExpansion
      productiveRelationalJoin
      refl
      (λ ()))

------------------------------------------------------------------------
-- 2. Consumer obligations and question-indexed measurements.
------------------------------------------------------------------------

data JoinObligation : Set where
  verifyBothContributions
  verifyResidualRetention
  verifyStrictAffordanceExpansion
  verifyLocalReachability
  : JoinObligation

data JoinMeasurement : Set where
  contributionTrace
  pathOrderProbe
  optionConeProbe
  historyPowerGateProbe
  : JoinMeasurement

data MeasurementValue : Set where
  bothSeen
  residualMissing
  residualSeen
  expansionMissing
  expansionSeen
  localGateUnknown
  : MeasurementValue

measure : JoinMeasurement → CandidateJoin → MeasurementValue
measure contributionTrace _ = bothSeen
measure pathOrderProbe coexistenceOnly = residualMissing
measure pathOrderProbe residualPreservingNoExpansion = residualSeen
measure pathOrderProbe productiveRelationalJoin = residualSeen
measure optionConeProbe coexistenceOnly = expansionMissing
measure optionConeProbe residualPreservingNoExpansion = expansionMissing
measure optionConeProbe productiveRelationalJoin = expansionSeen
measure historyPowerGateProbe _ = localGateUnknown

optionConeProbeSeparatesResidualOnlyFromProductive :
  measure optionConeProbe residualPreservingNoExpansion
  ≡ measure optionConeProbe productiveRelationalJoin → ⊥
optionConeProbeSeparatesResidualOnlyFromProductive ()

pathProbeDoesNotSeparateThoseTwo :
  measure pathOrderProbe residualPreservingNoExpansion
  ≡ measure pathOrderProbe productiveRelationalJoin
pathProbeDoesNotSeparateThoseTwo = refl

------------------------------------------------------------------------
-- 3. Ternary adaptive policy.  The unresolved consumer selects the coordinate
--    that can discharge that obligation rather than a generic extra datum.
------------------------------------------------------------------------

nextJoinMeasurement :
  JoinObligation → Suspension.EpistemicDisposition → JoinMeasurement
nextJoinMeasurement verifyBothContributions Suspension.suspendAndRefine = contributionTrace
nextJoinMeasurement verifyResidualRetention Suspension.suspendAndRefine = pathOrderProbe
nextJoinMeasurement verifyStrictAffordanceExpansion Suspension.suspendAndRefine = optionConeProbe
nextJoinMeasurement verifyLocalReachability Suspension.suspendAndRefine = historyPowerGateProbe
nextJoinMeasurement _ Suspension.rejectHere = contributionTrace
nextJoinMeasurement _ Suspension.acceptHere = contributionTrace

unresolvedProductivitySelectsOptionConeProbe :
  nextJoinMeasurement verifyStrictAffordanceExpansion Suspension.suspendAndRefine
  ≡ optionConeProbe
unresolvedProductivitySelectsOptionConeProbe = refl

selectedProductivityProbeSeparatesCanonicalCandidates :
  measure
    (nextJoinMeasurement
      verifyStrictAffordanceExpansion Suspension.suspendAndRefine)
    residualPreservingNoExpansion
  ≡ measure
    (nextJoinMeasurement
      verifyStrictAffordanceExpansion Suspension.suspendAndRefine)
    productiveRelationalJoin → ⊥
selectedProductivityProbeSeparatesCanonicalCandidates =
  optionConeProbeSeparatesResidualOnlyFromProductive

------------------------------------------------------------------------
-- 4. The productive receipt can close the abstract-join consumer, but the
--    separate local-reachability consumer remains independent.
------------------------------------------------------------------------

canonicalProductiveReceipt : Join.ProductiveDialecticalJoin
canonicalProductiveReceipt = Join.canonicalProductiveJoin

data AbstractJoinReceiptImpliesLocalReachability : Set where

data AnyMeasurementClosesEveryJoinObligation : Set where

data ResidualRetentionAloneIsProductiveSynthesis : Set where

abstractJoinReceiptDoesNotImplyLocalReachability :
  AbstractJoinReceiptImpliesLocalReachability → ⊥
abstractJoinReceiptDoesNotImplyLocalReachability ()

anyMeasurementDoesNotCloseEveryJoinObligation :
  AnyMeasurementClosesEveryJoinObligation → ⊥
anyMeasurementDoesNotCloseEveryJoinObligation ()

residualRetentionAloneIsNotProductiveSynthesis :
  ResidualRetentionAloneIsProductiveSynthesis → ⊥
residualRetentionAloneIsNotProductiveSynthesis ()

record DialecticalJoinAdaptiveSearchBoundary : Set where
  constructor dialectical-join-adaptive-search-boundary
  field
    coarseCoexistenceRecoversProductivity : Bool
    residualRetentionAloneRecoversProductivity : Bool
    unresolvedProductivitySelectsAffordanceMeasurement : Bool
    productiveReceiptAutomaticallyProvesLocalReachability : Bool
    measurementChoiceCanBeConsumerIndexed : Bool

canonicalDialecticalJoinAdaptiveSearchBoundary :
  DialecticalJoinAdaptiveSearchBoundary
canonicalDialecticalJoinAdaptiveSearchBoundary =
  dialectical-join-adaptive-search-boundary false false true false true
