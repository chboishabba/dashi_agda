module DASHI.Foundations.Base369ProcessHyperfabricRound6Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)

open import Base369 using
  ( tri-low
  ; tri-mid
  ; tri-high
  )

open import DASHI.Foundations.Base369SignedMembershipExact
open import DASHI.Foundations.Base369LayeredAttractorAndCoarseFineExact
open import DASHI.Foundations.Base369AddressSymmetryAndBranchGeometryExact
open import DASHI.Foundations.Base369ProcessBranchAttractorExact

booleanGoodCollapsesOutsideAndInverse₁ :
  isGood notMemberOfEither ≡ false
booleanGoodCollapsesOutsideAndInverse₁ = refl

booleanGoodCollapsesOutsideAndInverse₂ :
  isGood memberOfInverse ≡ false
booleanGoodCollapsesOutsideAndInverse₂ = refl

inverseProbeSeparatesOutside :
  isInverse notMemberOfEither ≡ false
inverseProbeSeparatesOutside = refl

inverseProbeFindsInverse :
  isInverse memberOfInverse ≡ true
inverseProbeFindsInverse = refl

localSuccessGlobalTrap : HorizonDrift
localSuccessGlobalTrap = horizonDrift tri-high tri-low tri-low

localSuccessIsPositive :
  immediateDrift localSuccessGlobalTrap ≡ tri-high
localSuccessIsPositive = refl

longTransportIsAdverse :
  longDrift localSuccessGlobalTrap ≡ tri-low
longTransportIsAdverse = refl

sampleDepth9 : Depth9
sampleDepth9 =
  depth9
    (depth6
      (horizon3 tri-high tri-high tri-high)
      (horizon3 tri-mid tri-low tri-low))
    (horizon3 tri-low tri-mid tri-high)

projectDepth9ToImmediate :
  state (project9To3 sampleDepth9) ≡ tri-high
projectDepth9ToImmediate = refl

sampleTritPath : TritPath (suc (suc (suc zero)))
sampleTritPath = tri-high ∷ tri-mid ∷ tri-low ∷ []

searchingIsNotEmptyCarrier : GoalProcessState SignedMembership
searchingIsNotEmptyCarrier =
  goalProcessState outcomeSearching memberOfGood

explorationAndCirculationShareZeroOrientation :
  orientation exploratoryValue ≡ orientation circulatingValue
explorationAndCirculationShareZeroOrientation = refl
