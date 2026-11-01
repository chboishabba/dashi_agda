module DASHI.Physics.YangMills.BalabanTopDownPositiveCoercivityBudgetExact where

------------------------------------------------------------------------
-- ROUND79: CLAY-TOP-DOWN COERCIVITY BUDGET
--
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- DASHI CONTRIBUTION
--
-- The existing P33 path-four certificate has an exact reference Hessian floor
-- 1/16 and selected the symmetric split
--
--     physical floor = 1/32,    signed-remainder budget = 1/32.
--
-- That split is convenient but is NOT a Clay requirement.  For the eventual
-- mass-gap route we only need a strictly positive physical coercivity floor.
-- Algebraically, for every norm square N >= 0,
--
--   f + r <= h0,
--   h0 N <= E0,
--   -(r N) <= R
--
-- imply
--
--   f N <= E0 + R.
--
-- Therefore ANY f>0 may be used, with the rest of the reference floor assigned
-- to the signed remainder.  With h0=1/16, the concrete choice
--
--     f = 1/64,     r = 3/64
--
-- leaves a positive physical floor while enlarging the admissible remainder by
-- 50% compared with the old 1/32 budget.  Since the currently configured local
-- remainder estimate is linear in the selected radius with coefficient 256,
-- the corresponding arithmetic radius target becomes
--
--     rho = (3/64)/256 = 3/16384,
--
-- also 50% larger than 1/8192.  This module proves ONLY the exact ordered-ring
-- implication and arithmetic.  Re-establishing every source-native local
-- background/FP/Wilson estimate on the enlarged region remains physical work.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _<_; _/_; -_; Positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanPath4GeneratedLDLCertificate as LDL
import DASHI.Physics.YangMills.BalabanClayT3ConfiguredGeometricConstantsExact as Constants
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as Old

record PositiveCoercivityBudget : Set where
  field
    referenceFloor physicalFloor remainderBudget : ℚ
    physicalFloorPositive : 0ℚ < physicalFloor
    floorAndRemainderFit : physicalFloor + remainderBudget ≤ referenceFloor

open PositiveCoercivityBudget public

positiveFloorFromAllocatedSignedRemainder :
  (budget : PositiveCoercivityBudget) →
  ∀ normSq referenceEnergy signedRemainder →
  0ℚ ≤ normSq →
  referenceFloor budget * normSq ≤ referenceEnergy →
  - (remainderBudget budget * normSq) ≤ signedRemainder →
  physicalFloor budget * normSq ≤ referenceEnergy + signedRemainder
positiveFloorFromAllocatedSignedRemainder budget normSq referenceEnergy signedRemainder
    normNonnegative referenceLower remainderLower =
  let
    scaled0 = Norm.scaleNonnegative normSq normNonnegative
      (floorAndRemainderFit budget)

    scaled :
      (physicalFloor budget + remainderBudget budget) * normSq
      ≤ referenceFloor budget * normSq
    scaled = subst
      (λ lower → lower ≤ referenceFloor budget * normSq)
      (ℚRing.solve-∀ normSq
        (physicalFloor budget) (remainderBudget budget))
      (subst
        (λ upper →
          normSq * (physicalFloor budget + remainderBudget budget) ≤ upper)
        (ℚRing.solve-∀ normSq (referenceFloor budget))
        scaled0)

    allocatedBelowReference :
      physicalFloor budget * normSq + remainderBudget budget * normSq
      ≤ referenceEnergy
    allocatedBelowReference =
      ℚP.≤-trans
        (subst
          (λ left → left ≤ referenceFloor budget * normSq)
          (ℚRing.solve-∀
            (physicalFloor budget) (remainderBudget budget) normSq)
          scaled)
        referenceLower

    summed = ℚP.+-mono-≤ allocatedBelowReference remainderLower
  in
  subst
    (λ lower → lower ≤ referenceEnergy + signedRemainder)
    (ℚRing.solve-∀
      (physicalFloor budget) (remainderBudget budget) normSq)
    summed

------------------------------------------------------------------------
-- Concrete top-down relaxation of the current half-floor split.
------------------------------------------------------------------------

oneSixtyFourth threeSixtyFourths enlargedRadius : ℚ
oneSixtyFourth = + 1 / 64
threeSixtyFourths = + 3 / 64
enlargedRadius = + 3 / 16384

oneSixtyFourthPositive : 0ℚ < oneSixtyFourth
oneSixtyFourthPositive =
  let
    instance
      selectedPositive : Positive oneSixtyFourth
      selectedPositive = ℚP.normalize-pos 1 64
  in
  ℚP.positive⁻¹ oneSixtyFourth

oneSixtyFourthPlusThreeSixtyFourthsIsReference :
  oneSixtyFourth + threeSixtyFourths ≡ LDL.oneSixteenth
oneSixtyFourthPlusThreeSixtyFourthsIsReference = ℚRing.solve []

topDownOneSixtyFourthBudget : PositiveCoercivityBudget
topDownOneSixtyFourthBudget = record
  { referenceFloor = LDL.oneSixteenth
  ; physicalFloor = oneSixtyFourth
  ; remainderBudget = threeSixtyFourths
  ; physicalFloorPositive = oneSixtyFourthPositive
  ; floorAndRemainderFit =
      subst
        (λ selected → selected ≤ LDL.oneSixteenth)
        oneSixtyFourthPlusThreeSixtyFourthsIsReference
        ℚP.≤-refl
  }

oldRemainderBudgetPlusExtraIsNewBudget :
  Old.p33PhysicalFloor + oneSixtyFourth ≡ threeSixtyFourths
oldRemainderBudgetPlusExtraIsNewBudget = ℚRing.solve []

newRemainderIsThreeHalvesOld :
  threeSixtyFourths ≡ (+ 3 / 2) * Old.p33PhysicalFloor
newRemainderIsThreeHalvesOld = ℚRing.solve []

enlargedRadiusSpendsNewRemainderBudget :
  Constants.configuredTotalCoefficient * enlargedRadius ≡ threeSixtyFourths
enlargedRadiusSpendsNewRemainderBudget = ℚRing.solve []

enlargedRadiusIsThreeHalvesOld :
  enlargedRadius ≡ (+ 3 / 2) * Old.p33SmallFieldRadius
enlargedRadiusIsThreeHalvesOld = ℚRing.solve []

topDownPositiveCoercivityBudgetLevel : ProofLevel
topDownPositiveCoercivityBudgetLevel = machineChecked

topDownEnlargedRadiusArithmeticLevel : ProofLevel
topDownEnlargedRadiusArithmeticLevel = machineChecked

physicalSourceNativeEnlargedRegionLevel : ProofLevel
physicalSourceNativeEnlargedRegionLevel = conditional
