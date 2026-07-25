module DASHI.Physics.YangMills.BalabanPath4AxisAverageExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanFourDimensionalHaloOverlapExact using
  (lengthAllCyclicIndices)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
open import DASHI.Physics.YangMills.BalabanFourAxisMartingaleExact

------------------------------------------------------------------------
-- Literal normalized axis averages on the side-four physical block.
------------------------------------------------------------------------

side4 : Nat
side4 = four

quarter : ℚ
quarter = + 1 / 4

axisAverage4 : SiteField side4 → Axis4 → SiteField side4
axisAverage4 siteF axis site =
  quarter * physicalFibreSum siteF axis (axisTransverse axis site)

axisCentering4 : SiteField side4 → Axis4 → SiteField side4
axisCentering4 siteF axis site = siteF site - axisAverage4 siteF axis site

axisAverage4ConstantOnFibre :
  ∀ siteF axis transverse coordinate →
  axisAverage4 siteF axis (insertAxis axis coordinate transverse)
  ≡ quarter * physicalFibreSum siteF axis transverse
axisAverage4ConstantOnFibre siteF axis transverse coordinate
  rewrite extractInsertTransverse axis coordinate transverse = refl

axisCentering4OnFibre :
  ∀ siteF axis transverse coordinate →
  axisCentering4 siteF axis (insertAxis axis coordinate transverse)
  ≡ siteF (insertAxis axis coordinate transverse)
    - quarter * physicalFibreSum siteF axis transverse
axisCentering4OnFibre siteF axis transverse coordinate
  rewrite axisAverage4ConstantOnFibre siteF axis transverse coordinate = refl

postulate
  axisAverage4Idempotent : ∀ siteF axis site →
    axisAverage4 (axisAverage4 siteF axis) axis site
    ≡ axisAverage4 siteF axis site

  axisAverage4Commutes : ∀ left right siteF site →
    axisAverage4 (axisAverage4 siteF left) right site
    ≡ axisAverage4 (axisAverage4 siteF right) left site

postulate
  axisCentering4DirectFibreSumZero : ∀ siteF axis transverse →
    sumRational (allCyclicIndices side4)
      (λ coordinate →
        siteF (insertAxis axis coordinate transverse)
        - quarter * physicalFibreSum siteF axis transverse)
    ≡ 0ℚ

  axisCentering4FibreSumZero : ∀ siteF axis transverse →
    sumRational (allCyclicIndices side4)
      (λ coordinate →
        axisCentering4 siteF axis (insertAxis axis coordinate transverse))
    ≡ 0ℚ

------------------------------------------------------------------------
-- Literal four-axis martingale fields.
------------------------------------------------------------------------

average0 average01 average012 average0123 :
  SiteField side4 → SiteField side4
average0 siteF = axisAverage4 siteF zeroᵢ
average01 siteF = axisAverage4 (average0 siteF) (sucᵢ zeroᵢ)
average012 siteF = axisAverage4 (average01 siteF) (sucᵢ (sucᵢ zeroᵢ))
average0123 siteF =
  axisAverage4 (average012 siteF) (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))

martingaleField0 martingaleField1 martingaleField2 martingaleField3 :
  SiteField side4 → SiteField side4
martingaleField0 siteF site = siteF site - average0 siteF site
martingaleField1 siteF site = average0 siteF site - average01 siteF site
martingaleField2 siteF site = average01 siteF site - average012 siteF site
martingaleField3 siteF site = average012 siteF site - average0123 siteF site

fourAxisPhysicalMartingaleDecomposition :
  ∀ siteF site →
  average0123 siteF site ≡ 0ℚ →
  martingaleField0 siteF site
    + (martingaleField1 siteF site
    + (martingaleField2 siteF site
    + martingaleField3 siteF site))
  ≡ siteF site
fourAxisPhysicalMartingaleDecomposition siteF site globalMeanZero =
  fourAxisMartingaleDecomposition
    (siteF site)
    (average0 siteF site)
    (average01 siteF site)
    (average012 siteF site)
    (average0123 siteF site)
    globalMeanZero

path4AxisAverageIdempotenceLevel : ProofLevel
path4AxisAverageIdempotenceLevel = computed

path4DistinctAxisAverageCommutationLevel : ProofLevel
path4DistinctAxisAverageCommutationLevel = computed

path4AxisCenteringMeanZeroLevel : ProofLevel
path4AxisCenteringMeanZeroLevel = machineChecked

path4PhysicalMartingaleDecompositionLevel : ProofLevel
path4PhysicalMartingaleDecompositionLevel = machineChecked

path4PhysicalMartingaleOrthogonalityLevel : ProofLevel
path4PhysicalMartingaleOrthogonalityLevel = conditional
