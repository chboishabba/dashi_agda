module DASHI.Foundations.Base369SymmetryWaveRound9Validation where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Base369 using (TriTruth; tri-low; tri-mid; tri-high)

import DASHI.Foundations.Base369SignedMembershipExact as Signed
import DASHI.Foundations.Base369LayeredAttractorAndCoarseFineExact as Layered
import DASHI.Foundations.Base369AddressSymmetryAndBranchGeometryExact as Geometry
import DASHI.Foundations.Base369ProcessBranchAttractorExact as Branch
import DASHI.Foundations.Base369StepStateSymmetryQuotientExact as Step
import DASHI.Foundations.Base369WaveContinuousSymbolicCodingExact as Wave

booleanProjectionCollapsesInverseAndExterior :
  Signed.isGood Signed.memberOfInverse ≡ Signed.isGood Signed.notMemberOfEither
booleanProjectionCollapsesInverseAndExterior = Signed.isGoodCollapsesInverseAndExterior

coarseFineHasElevenCoordinates : Layered.coarseFineCoordinateCount ≡ 11
coarseFineHasElevenCoordinates = Layered.coarseFineCoordinateCountIs11

localCompletionLeavesSixOpen :
  Layered.complete6 Layered.localOnlyCompletion ≡ Layered.horizonOpen
localCompletionLeavesSixOpen = Layered.localOnlyRemainsOpenAt6

localCompletionLeavesNineOpen :
  Layered.complete9 Layered.localOnlyCompletion ≡ Layered.horizonOpen
localCompletionLeavesNineOpen = Layered.localOnlyRemainsOpenAt9

attractiveDeadEndStartsPositive :
  Layered.project9To3 Layered.attractiveDeadEnd369 ≡ Layered.positiveHorizon
attractiveDeadEndStartsPositive = Layered.attractiveDeadEndImmediate

attractiveDeadEndEndsAdverse :
  Layered.long Layered.attractiveDeadEnd369 ≡ Layered.adverseHorizon
attractiveDeadEndEndsAdverse = Layered.attractiveDeadEndLong

prefixDepthIsSelfDepth :
  {n : Nat} → (address : Geometry.TritPath n) →
  Geometry.sharedPrefixDepth address address ≡ n
prefixDepthIsSelfDepth = Geometry.sharedPrefixDepthSelf

braidRelationValidated :
  {A : Set} → (x : Geometry.Triple A) →
  Geometry.sigma₁ (Geometry.sigma₂ (Geometry.sigma₁ x))
  ≡ Geometry.sigma₂ (Geometry.sigma₁ (Geometry.sigma₂ x))
braidRelationValidated = Geometry.threeStrandBraidRelation

diamondHistoriesConverge :
  Geometry.diamondTarget Geometry.leftToJoin
  ≡ Geometry.diamondTarget Geometry.rightToJoin
diamondHistoriesConverge = Geometry.distinctHistoriesConverge

oneEffectiveDuplicateOrbit : Branch.effectiveDuplicateOrbitCount ≡ 1
oneEffectiveDuplicateOrbit = Branch.effectiveDuplicateOrbitCountIs1

twoOperationalDuplicateCopies : Branch.operationalDuplicateCopies ≡ 2
twoOperationalDuplicateCopies = refl

positiveMarginalSlackIsThree :
  Branch.margin Branch.beneficialBudgetExampleHasPositiveMargin ≡ 3
positiveMarginalSlackIsThree = refl

serviceablePairCanCancelDirection :
  Branch.netDirection Branch.serviceableButDirectionallyCancelled ≡ tri-mid
serviceablePairCanCancelDirection = Branch.serviceableDiffusionIsNeutral

sameTritProjectionCanHideDifferentCost :
  Step.projectTritTrajectory (Step.sameTritDifferentCostLeft Step.∷ Step.[])
  ≡ Step.projectTritTrajectory (Step.sameTritDifferentCostRight Step.∷ Step.[])
sameTritProjectionCanHideDifferentCost = Step.sameTritDifferentCostProjection

sameTritProjectionStillHasDiscrepancy :
  Step.trajectoryDiscrepancy
    (Step.sameTritDifferentCostLeft Step.∷ Step.[])
    (Step.sameTritDifferentCostRight Step.∷ Step.[])
  ≡ 1
sameTritProjectionStillHasDiscrepancy = Step.sameTritDifferentCostHasDiscrepancy

symbolicCodingRetainsExactCarrier :
  {Carrier : Set} → (coding : Wave.SymbolicCoding Carrier) → (x : Carrier) →
  Wave.decode (Wave.encode coding x) ≡ x
symbolicCodingRetainsExactCarrier = Wave.decodeAfterEncode

balancedTernaryHasThreeSlots : Wave.balancedOddSymbolCount 1 ≡ 3
balancedTernaryHasThreeSlots = Wave.balancedTernarySymbolCount

balancedQuinaryHasFiveSlots : Wave.balancedOddSymbolCount 2 ≡ 5
balancedQuinaryHasFiveSlots = Wave.balancedQuinarySymbolCount

balancedNonaryHasNineSlots : Wave.balancedOddSymbolCount 4 ≡ 9
balancedNonaryHasNineSlots = Wave.balancedNonarySymbolCount
