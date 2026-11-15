module DASHI.Foundations.PolynomialNumerologyArithmeticAtlasExact where

------------------------------------------------------------------------
-- MAXIMAL *TYPED* NUMEROLOGY: EXACT IDENTITIES, NO CAUSAL PROMOTION.
--
-- Reuse actual 27 endomorphism/trialectic carrier, five-trit and three
-- five-mode code counts, the 120 ↔ 60x2 quintic root-label atlas, and
-- the separate Q8 central sign. Common cardinality is never treated as
-- group isomorphism, radical solvability, physics or Monster identity.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_; _∸_)
open import Data.List.Base using (length)
open import Data.Empty using (⊥)

import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Foundations.PolynomialMonodromyTernaryQuaternionBridgeExact as Core
import DASHI.Foundations.Polynomial369TrialecticTransportExact as Root369
import DASHI.Foundations.QuinticPermutationTripleOrientationAtlasExact as Five
import DASHI.Algebra.FiniteQuaternionDoubleCover as Q8

threePowerThreeIs27 : Tower.pow 3 3 ≡ 27
threePowerThreeIs27 = refl

threePowerFiveIsNineTimesTwentySeven :
  Core.fiveTritArithmeticCount ≡ 9 * 27
threePowerFiveIsNineTimesTwentySeven = refl

threePowerSixIsThreeTimes243 :
  Tower.pow 3 6 ≡ 3 * Core.fiveTritArithmeticCount
threePowerSixIsThreeTimes243 = refl

fivePowerThreeIsFiveTimesTwentyFive :
  Core.threeFiveModeArithmeticCount ≡ 5 * 25
fivePowerThreeIsFiveTimesTwentyFive = refl

difference243And125Is118 :
  Core.fiveTritArithmeticCount
    ∸ Core.threeFiveModeArithmeticCount ≡ 118
difference243And125Is118 = refl

-- The ordered *injective* three-root choices are 60, not 5^3=125.
fivePermutationAtlasFibreCount :
  length Five.allFivePermutations
  ≡ length Five.allDistinctTriples * 2
fivePermutationAtlasFibreCount = refl

evenPermutationsMatchInjectiveTriples :
  length Five.allEvenPermutationCodes
  ≡ length Five.allDistinctTriples
evenPermutationsMatchInjectiveTriples = refl

sixIsThreeFactorial :
  2 * 3 ≡ 6
sixIsThreeFactorial = refl

tripleRootChoicesAre5P3 :
  length Five.allDistinctTriples ≡ 5 * (4 * 3)
tripleRootChoicesAre5P3 = refl

-- The two orientation flags can be charted to the Q8 signs AS CARRIERS.
-- They do not have identical meanings: parity of a root-label permutation
-- is not the central sign of a spin lift, even though both have two states.
parityToQuaternionSign :
  Five.Orientation2 → Q8.Sign
parityToQuaternionSign Five.evenChoice = Q8.positiveSign
parityToQuaternionSign Five.oddChoice = Q8.negativeSign

quaternionSignToParity :
  Q8.Sign → Five.Orientation2
quaternionSignToParity Q8.positiveSign = Five.evenChoice
quaternionSignToParity Q8.negativeSign = Five.oddChoice

paritySignRoundTrip :
  (p : Five.Orientation2) →
  quaternionSignToParity (parityToQuaternionSign p) ≡ p
paritySignRoundTrip Five.evenChoice = refl
paritySignRoundTrip Five.oddChoice = refl

signParityRoundTrip :
  (s : Q8.Sign) →
  parityToQuaternionSign (quaternionSignToParity s) ≡ s
signParityRoundTrip Q8.positiveSign = refl
signParityRoundTrip Q8.negativeSign = refl

twentySevenSharedCarrierNotAQuinticTheorem :
  Tower.levelTwoCodeCount ≡ 27
twentySevenSharedCarrierNotAQuinticTheorem =
  Tower.levelTwoCodeCountIsTwentySeven

root27SynthesisCarrierChart :
  Tower.levelTwoCodeCount
  ≡ 27
root27SynthesisCarrierChart =
  Root369.sameCarrierCountDifferentSemantics

-- The previous two equations have equal target 27. They do not identify
-- an arbitrary quintic's roots with 27 cells or with a Monster module.
data MatchingFiniteCountsConstructMonsterRepresentation : Set where

countingDoesNotPromoteMonsterObject :
  MatchingFiniteCountsConstructMonsterRepresentation → ⊥
countingDoesNotPromoteMonsterObject ()
