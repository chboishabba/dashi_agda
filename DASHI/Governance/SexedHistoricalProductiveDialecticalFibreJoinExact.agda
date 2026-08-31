module DASHI.Governance.SexedHistoricalProductiveDialecticalFibreJoinExact where

------------------------------------------------------------------------
-- PRODUCTIVE DIALECTICAL JOIN OVER HISTORY-BEARING FIBRE TRANSPORT
--
-- The purpose of this owner is not to decree a philosophical synthesis.  It
-- gives a finite DASHI criterion for a candidate join of two non-identical,
-- noncommuting construction grammars to count as productive:
--
--   * both transported contributions remain represented;
--   * their order/noncommutation residual remains observable;
--   * the join is not reducible to either one-sided grammar;
--   * at least one later affordance is available only after the join.
--
-- Lacanian / Irigarayan source roles are bounded by the existing source owners.
-- The finite states below are schematic comparison fixtures, not claims that
-- either source uniquely supplies these exact constructors.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.LacanIrigarayTernaryGrammarBridgeExact as LacanIrigaray
import DASHI.Core.FeministRechartingSourceBridgeExact as Rechart
import DASHI.Core.EpistemicSuspensionExact as Suspension
import DASHI.Governance.OptionConeCoercionExact as Cone
import DASHI.Governance.SexedHistoricalEffectiveFibreTransportExact as Effective
import DASHI.Governance.SexedHistoricalDialecticalOrderHolonomyAnalogueExact as Order

------------------------------------------------------------------------
-- 1. Two bounded grammar contributions and a transported residual.
------------------------------------------------------------------------

data GrammarContribution : Set where
  nonSovereignRelationalSubject
  positiveIrreducibleDifference
  : GrammarContribution

data TransportOrder : Set where
  lacanThenRechart rechartThenLacan : TransportOrder

data OrderResidual : Set where
  residualLR residualRL : OrderResidual

data JoinState : Set where
  oneSidedLacan
  oneSidedRechart
  reciprocalResidualJoin
  : JoinState

leftContributionPresent : JoinState → Bool
leftContributionPresent oneSidedLacan = true
leftContributionPresent oneSidedRechart = false
leftContributionPresent reciprocalResidualJoin = true

rightContributionPresent : JoinState → Bool
rightContributionPresent oneSidedLacan = false
rightContributionPresent oneSidedRechart = true
rightContributionPresent reciprocalResidualJoin = true

residualVisible : JoinState → Bool
residualVisible oneSidedLacan = false
residualVisible oneSidedRechart = false
residualVisible reciprocalResidualJoin = true

------------------------------------------------------------------------
-- 2. History transport: the two construction orders remain different rather
--    than being identified by a fake synthesis equality.
------------------------------------------------------------------------

transportResidual : TransportOrder → OrderResidual
transportResidual lacanThenRechart = residualLR
transportResidual rechartThenLacan = residualRL

transportOrdersRemainDistinct :
  transportResidual lacanThenRechart
  ≡ transportResidual rechartThenLacan → ⊥
transportOrdersRemainDistinct ()

canonicalHistoricalOrderDefectStillAvailable :
  Order.reinterpretAfterInstitutionalise
  ≡ Order.institutionaliseAfterReinterpret → ⊥
canonicalHistoricalOrderDefectStillAvailable = Order.orderDefect

------------------------------------------------------------------------
-- 3. Productive join criterion.  This is a receipt, not an automatic law of
--    dialectics.  A candidate can fail any field and remain rejected/unresolved.
------------------------------------------------------------------------

record ProductiveDialecticalJoin : Set where
  constructor productive-dialectical-join
  field
    joinState : JoinState
    preservesLacanContribution : leftContributionPresent joinState ≡ true
    preservesRechartContribution : rightContributionPresent joinState ≡ true
    preservesOrderResidual : residualVisible joinState ≡ true
    notLacanOnly : joinState ≡ oneSidedLacan → ⊥
    notRechartOnly : joinState ≡ oneSidedRechart → ⊥
open ProductiveDialecticalJoin public

canonicalProductiveJoin : ProductiveDialecticalJoin
canonicalProductiveJoin =
  productive-dialectical-join
    reciprocalResidualJoin refl refl refl (λ ()) (λ ())

------------------------------------------------------------------------
-- 4. Strict affordance expansion: the join must make at least one move
--    available that neither one-sided grammar can supply by itself.
------------------------------------------------------------------------

data RelationalOption : Set where
  inheritedIdentification
  oppositionalInversion
  reciprocalRecognition
  relationalAutonomy
  : RelationalOption

data RelationalWorld : Set where
  lacanWorld rechartWorld joinedWorld : RelationalWorld

data Available : RelationalWorld → RelationalOption → Set where
  lacanInherited : Available lacanWorld inheritedIdentification
  rechartInversion : Available rechartWorld oppositionalInversion

  joinInherited : Available joinedWorld inheritedIdentification
  joinInversion : Available joinedWorld oppositionalInversion
  joinRecognition : Available joinedWorld reciprocalRecognition
  joinAutonomy : Available joinedWorld relationalAutonomy

relationalReachability : Cone.SafeReachabilitySystem RelationalWorld RelationalOption
relationalReachability = Cone.safeReachabilitySystem Available

lacanIncludedInJoin :
  (option : RelationalOption) → Available lacanWorld option → Available joinedWorld option
lacanIncludedInJoin inheritedIdentification lacanInherited = joinInherited

rechartIncludedInJoin :
  (option : RelationalOption) → Available rechartWorld option → Available joinedWorld option
rechartIncludedInJoin oppositionalInversion rechartInversion = joinInversion

joinStrictlyExpandsLacanCone :
  Cone.StrictSafeReachabilityContraction relationalReachability joinedWorld lacanWorld
joinStrictlyExpandsLacanCone =
  Cone.strictSafeReachabilityContraction
    lacanIncludedInJoin
    relationalAutonomy
    joinAutonomy
    (λ ())

joinStrictlyExpandsRechartCone :
  Cone.StrictSafeReachabilityContraction relationalReachability joinedWorld rechartWorld
joinStrictlyExpandsRechartCone =
  Cone.strictSafeReachabilityContraction
    rechartIncludedInJoin
    reciprocalRecognition
    joinRecognition
    (λ ())

------------------------------------------------------------------------
-- 5. The joined public label still does not recover path/order residual.
------------------------------------------------------------------------

data CoarseJoinSurface : Set where sameProductiveJoinSurface : CoarseJoinSurface

data FineJoinedHistory : Set where joinedLR joinedRL : FineJoinedHistory

coarseJoin : FineJoinedHistory → CoarseJoinSurface
coarseJoin _ = sameProductiveJoinSurface

joinOrderResidual : FineJoinedHistory → OrderResidual
joinOrderResidual joinedLR = residualLR
joinOrderResidual joinedRL = residualRL

productiveJoinDoesNotEraseTransportOrder :
  INF.FactorsThrough coarseJoin joinOrderResidual → ⊥
productiveJoinDoesNotEraseTransportOrder =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness joinedLR joinedRL refl (λ ()))

------------------------------------------------------------------------
-- 6. Join search remains ternary.  Absence of a productive receipt is not
--    automatically proof of impossibility; unresolved joins request refinement.
------------------------------------------------------------------------

data CandidateJoinStatus : Set where
  rejectedJoin unresolvedJoin productiveJoin : CandidateJoinStatus

joinDisposition : CandidateJoinStatus → Suspension.EpistemicDisposition
joinDisposition rejectedJoin = Suspension.rejectHere
joinDisposition unresolvedJoin = Suspension.suspendAndRefine
joinDisposition productiveJoin = Suspension.acceptHere

unresolvedJoinRequestsRefinement :
  joinDisposition unresolvedJoin ≡ Suspension.suspendAndRefine
unresolvedJoinRequestsRefinement = refl

------------------------------------------------------------------------
-- 7. Lacan / Irigaray source and rechart boundaries remain authoritative.
------------------------------------------------------------------------

irigarayIsNotMerelyLacanSignFlip =
  LacanIrigaray.noTernaryRelabellingPreservesGrammar

positiveRechartMustAddResidualStructure =
  Rechart.canonicalPositiveRechartingIsStrict

------------------------------------------------------------------------
-- 8. Cross-pollination with local fibre reachability.  A productive abstract
--    join need not yet be locally reachable in every historical fibre.
------------------------------------------------------------------------

data ProductiveJoinImpliesLocalReachabilityEverywhere : Set where

data JoinErasesPowerHistoryResiduals : Set where

data NoncommutationImpliesMutualDestruction : Set where

data ProductiveJoinIsGuaranteedSynthesis : Set where

data CoConstitutionMeansOwnershipOfOtherMeaning : Set where

productiveJoinDoesNotGuaranteeLocalReachabilityEverywhere :
  ProductiveJoinImpliesLocalReachabilityEverywhere → ⊥
productiveJoinDoesNotGuaranteeLocalReachabilityEverywhere ()

joinDoesNotErasePowerHistoryResiduals : JoinErasesPowerHistoryResiduals → ⊥
joinDoesNotErasePowerHistoryResiduals ()

noncommutationDoesNotImplyMutualDestruction :
  NoncommutationImpliesMutualDestruction → ⊥
noncommutationDoesNotImplyMutualDestruction ()

productiveJoinIsNotGuaranteedByDialecticalOpposition :
  ProductiveJoinIsGuaranteedSynthesis → ⊥
productiveJoinIsNotGuaranteedByDialecticalOpposition ()

coConstitutionDoesNotCreateOwnershipOfOtherMeaning :
  CoConstitutionMeansOwnershipOfOtherMeaning → ⊥
coConstitutionDoesNotCreateOwnershipOfOtherMeaning ()

formalEffectiveGapStillOpen :
  Effective.localReachability Effective.inheritedClosedFibre Effective.formalFM
  ≡ Effective.localReachability Effective.pluralResourceFibre Effective.formalFM → ⊥
formalEffectiveGapStillOpen ()

record ProductiveDialecticalFibreJoinBoundary : Set where
  constructor productive-dialectical-fibre-join-boundary
  field
    productiveJoinPreservesBothContributions : Bool
    productiveJoinRetainsOrderResidual : Bool
    productiveJoinStrictlyExpandsAffordanceCone : Bool
    productiveJoinEqualsOneSidedGrammar : Bool
    noncommutationMeansMutualDestruction : Bool
    dialecticalOppositionGuaranteesSynthesis : Bool
    productiveAbstractJoinIsLocallyReachableEverywhere : Bool
    coConstitutionCreatesOwnershipOfOtherMeaning : Bool

canonicalProductiveDialecticalFibreJoinBoundary :
  ProductiveDialecticalFibreJoinBoundary
canonicalProductiveDialecticalFibreJoinBoundary =
  productive-dialectical-fibre-join-boundary
    true true true false false false false false
