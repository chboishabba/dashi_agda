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
axisAverage4 field axis site =
  quarter * physicalFibreSum field axis (axisTransverse axis site)

axisCentering4 : SiteField side4 → Axis4 → SiteField side4
axisCentering4 field axis site = field site - axisAverage4 field axis site

axisAverage4ConstantOnFibre :
  ∀ field axis transverse coordinate →
  axisAverage4 field axis (insertAxis axis coordinate transverse)
  ≡ quarter * physicalFibreSum field axis transverse
axisAverage4ConstantOnFibre field axis transverse coordinate
  rewrite extractInsertTransverse axis coordinate transverse = refl

axisCentering4OnFibre :
  ∀ field axis transverse coordinate →
  axisCentering4 field axis (insertAxis axis coordinate transverse)
  ≡ field (insertAxis axis coordinate transverse)
    - quarter * physicalFibreSum field axis transverse
axisCentering4OnFibre field axis transverse coordinate
  rewrite axisAverage4ConstantOnFibre field axis transverse coordinate = refl

axisAverage4Idempotent : ∀ field axis site →
  axisAverage4 (axisAverage4 field axis) axis site
  ≡ axisAverage4 field axis site
axisAverage4Idempotent field zeroᵢ
  (pair (pair x0 x1) (pair x2 x3)) = ℚRing.solve-∀
axisAverage4Idempotent field (sucᵢ zeroᵢ)
  (pair (pair x0 x1) (pair x2 x3)) = ℚRing.solve-∀
axisAverage4Idempotent field (sucᵢ (sucᵢ zeroᵢ))
  (pair (pair x0 x1) (pair x2 x3)) = ℚRing.solve-∀
axisAverage4Idempotent field (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (pair (pair x0 x1) (pair x2 x3)) = ℚRing.solve-∀

axisAverage4Commutes : ∀ left right field site →
  axisAverage4 (axisAverage4 field left) right site
  ≡ axisAverage4 (axisAverage4 field right) left site
axisAverage4Commutes zeroᵢ zeroᵢ field site =
  trans (axisAverage4Idempotent field zeroᵢ site)
        (sym (axisAverage4Idempotent field zeroᵢ site))
axisAverage4Commutes zeroᵢ (sucᵢ zeroᵢ) field
  (pair (pair x0 x1) (pair x2 x3)) = ℚRing.solve-∀
axisAverage4Commutes zeroᵢ (sucᵢ (sucᵢ zeroᵢ)) field
  (pair (pair x0 x1) (pair x2 x3)) = ℚRing.solve-∀
axisAverage4Commutes zeroᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) field
  (pair (pair x0 x1) (pair x2 x3)) = ℚRing.solve-∀
axisAverage4Commutes (sucᵢ zeroᵢ) zeroᵢ field site =
  sym (axisAverage4Commutes zeroᵢ (sucᵢ zeroᵢ) field site)
axisAverage4Commutes (sucᵢ zeroᵢ) (sucᵢ zeroᵢ) field site =
  trans (axisAverage4Idempotent field (sucᵢ zeroᵢ) site)
        (sym (axisAverage4Idempotent field (sucᵢ zeroᵢ) site))
axisAverage4Commutes (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ)) field
  (pair (pair x0 x1) (pair x2 x3)) = ℚRing.solve-∀
axisAverage4Commutes (sucᵢ zeroᵢ)
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) field
  (pair (pair x0 x1) (pair x2 x3)) = ℚRing.solve-∀
axisAverage4Commutes (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ field site =
  sym (axisAverage4Commutes zeroᵢ (sucᵢ (sucᵢ zeroᵢ)) field site)
axisAverage4Commutes (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ zeroᵢ) field site =
  sym (axisAverage4Commutes (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ)) field site)
axisAverage4Commutes (sucᵢ (sucᵢ zeroᵢ))
  (sucᵢ (sucᵢ zeroᵢ)) field site =
  trans (axisAverage4Idempotent field (sucᵢ (sucᵢ zeroᵢ)) site)
        (sym (axisAverage4Idempotent field (sucᵢ (sucᵢ zeroᵢ)) site))
axisAverage4Commutes (sucᵢ (sucᵢ zeroᵢ))
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) field
  (pair (pair x0 x1) (pair x2 x3)) = ℚRing.solve-∀
axisAverage4Commutes (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) zeroᵢ field site =
  sym (axisAverage4Commutes zeroᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) field site)
axisAverage4Commutes (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ zeroᵢ) field site =
  sym (axisAverage4Commutes (sucᵢ zeroᵢ)
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) field site)
axisAverage4Commutes (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ (sucᵢ zeroᵢ)) field site =
  sym (axisAverage4Commutes (sucᵢ (sucᵢ zeroᵢ))
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) field site)
axisAverage4Commutes (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) field site =
  trans
    (axisAverage4Idempotent field (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site)
    (sym (axisAverage4Idempotent field (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site))

axisCentering4DirectFibreSumZero : ∀ field axis transverse →
  sumRational (allCyclicIndices side4)
    (λ coordinate →
      field (insertAxis axis coordinate transverse)
      - quarter * physicalFibreSum field axis transverse)
  ≡ 0ℚ
axisCentering4DirectFibreSumZero field axis transverse
  rewrite sumScaledDifferenceFormula
    1ℚ
    (quarter * physicalFibreSum field axis transverse)
    (allCyclicIndices side4)
    (λ coordinate → field (insertAxis axis coordinate transverse))
  | lengthAllCyclicIndices side4 = ℚRing.solve-∀

axisCentering4FibreSumZero : ∀ field axis transverse →
  sumRational (allCyclicIndices side4)
    (λ coordinate →
      axisCentering4 field axis (insertAxis axis coordinate transverse))
  ≡ 0ℚ
axisCentering4FibreSumZero field axis transverse =
  trans
    (sumRationalCong
      (allCyclicIndices side4)
      (λ coordinate →
        axisCentering4 field axis (insertAxis axis coordinate transverse))
      (λ coordinate →
        field (insertAxis axis coordinate transverse)
        - quarter * physicalFibreSum field axis transverse)
      (axisCentering4OnFibre field axis transverse))
    (axisCentering4DirectFibreSumZero field axis transverse)

------------------------------------------------------------------------
-- Literal four-axis martingale fields.
------------------------------------------------------------------------

average0 average01 average012 average0123 :
  SiteField side4 → SiteField side4
average0 field = axisAverage4 field zeroᵢ
average01 field = axisAverage4 (average0 field) (sucᵢ zeroᵢ)
average012 field = axisAverage4 (average01 field) (sucᵢ (sucᵢ zeroᵢ))
average0123 field =
  axisAverage4 (average012 field) (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))

martingaleField0 martingaleField1 martingaleField2 martingaleField3 :
  SiteField side4 → SiteField side4
martingaleField0 field site = field site - average0 field site
martingaleField1 field site = average0 field site - average01 field site
martingaleField2 field site = average01 field site - average012 field site
martingaleField3 field site = average012 field site - average0123 field site

fourAxisPhysicalMartingaleDecomposition :
  ∀ field site →
  average0123 field site ≡ 0ℚ →
  martingaleField0 field site
    + (martingaleField1 field site
    + (martingaleField2 field site
    + martingaleField3 field site))
  ≡ field site
fourAxisPhysicalMartingaleDecomposition field site globalMeanZero =
  fourAxisMartingaleDecomposition
    (field site)
    (average0 field site)
    (average01 field site)
    (average012 field site)
    (average0123 field site)
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
