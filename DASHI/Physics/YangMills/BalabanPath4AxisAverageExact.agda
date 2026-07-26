module DASHI.Physics.YangMills.BalabanPath4AxisAverageExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (length)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanFourDimensionalHaloOverlapExact using
  (lengthAllCyclicIndices)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
open import DASHI.Physics.YangMills.BalabanFiniteFibreAverageExact using
  (sumRationalConstant)
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact using
  (sumSwap)
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

------------------------------------------------------------------------
-- The side-four normalization and finite double-sum swap.
------------------------------------------------------------------------

side4AverageOfConstant : ∀ value →
  quarter * sumRational (allCyclicIndices side4) (λ _ → value) ≡ value
side4AverageOfConstant value
  rewrite sumRationalConstant (allCyclicIndices side4) value
        | lengthAllCyclicIndices side4 =
  ℚRing.solve-∀ value

quarterDoubleSumSwap :
  ∀ {A B : Set} (left : List A) (right : List B)
    (term : A → B → ℚ) →
  quarter * sumRational left
    (λ leftValue → quarter * sumRational right (term leftValue))
  ≡ quarter * sumRational right
    (λ rightValue → quarter * sumRational left
      (λ leftValue → term leftValue rightValue))
quarterDoubleSumSwap left right term =
  trans
    (cong (quarter *_)
      (sumRationalScale quarter left
        (λ leftValue → sumRational right (term leftValue))))
    (trans
      (cong (λ value → quarter * (quarter * value))
        (sumSwap left right term))
      (cong (quarter *_)
        (sym
          (sumRationalScale quarter right
            (λ rightValue →
              sumRational left (λ leftValue → term leftValue rightValue))))))

axisAverage4Idempotent : ∀ siteF axis site →
  axisAverage4 (axisAverage4 siteF axis) axis site
  ≡ axisAverage4 siteF axis site
axisAverage4Idempotent siteF axis site =
  trans
    (cong (quarter *_)
      (sumRationalCong
        (allCyclicIndices side4)
        (λ coordinate →
          axisAverage4 siteF axis
            (insertAxis axis coordinate (axisTransverse axis site)))
        (λ _ →
          quarter * physicalFibreSum siteF axis (axisTransverse axis site))
        (λ coordinate →
          axisAverage4ConstantOnFibre
            siteF axis (axisTransverse axis site) coordinate)))
    (side4AverageOfConstant
      (quarter * physicalFibreSum siteF axis (axisTransverse axis site)))

------------------------------------------------------------------------
-- Coordinate conditional expectations commute.  The twelve distinct-axis
-- cases are finite Fubini; the four diagonal cases are definitional.
------------------------------------------------------------------------

axisAverage4Commutes : ∀ left right siteF site →
  axisAverage4 (axisAverage4 siteF left) right site
  ≡ axisAverage4 (axisAverage4 siteF right) left site
axisAverage4Commutes zeroᵢ zeroᵢ siteF site = refl
axisAverage4Commutes zeroᵢ (sucᵢ zeroᵢ) siteF
  (pair (pair x0 x1) (pair x2 x3)) =
  quarterDoubleSumSwap
    (allCyclicIndices side4) (allCyclicIndices side4)
    (λ moving fixed → siteF (pair (pair fixed moving) (pair x2 x3)))
axisAverage4Commutes zeroᵢ (sucᵢ (sucᵢ zeroᵢ)) siteF
  (pair (pair x0 x1) (pair x2 x3)) =
  quarterDoubleSumSwap
    (allCyclicIndices side4) (allCyclicIndices side4)
    (λ moving fixed → siteF (pair (pair fixed x1) (pair moving x3)))
axisAverage4Commutes zeroᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) siteF
  (pair (pair x0 x1) (pair x2 x3)) =
  quarterDoubleSumSwap
    (allCyclicIndices side4) (allCyclicIndices side4)
    (λ moving fixed → siteF (pair (pair fixed x1) (pair x2 moving)))
axisAverage4Commutes (sucᵢ zeroᵢ) zeroᵢ siteF
  (pair (pair x0 x1) (pair x2 x3)) =
  quarterDoubleSumSwap
    (allCyclicIndices side4) (allCyclicIndices side4)
    (λ moving fixed → siteF (pair (pair moving fixed) (pair x2 x3)))
axisAverage4Commutes (sucᵢ zeroᵢ) (sucᵢ zeroᵢ) siteF site = refl
axisAverage4Commutes (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ)) siteF
  (pair (pair x0 x1) (pair x2 x3)) =
  quarterDoubleSumSwap
    (allCyclicIndices side4) (allCyclicIndices side4)
    (λ moving fixed → siteF (pair (pair x0 fixed) (pair moving x3)))
axisAverage4Commutes (sucᵢ zeroᵢ)
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) siteF
  (pair (pair x0 x1) (pair x2 x3)) =
  quarterDoubleSumSwap
    (allCyclicIndices side4) (allCyclicIndices side4)
    (λ moving fixed → siteF (pair (pair x0 fixed) (pair x2 moving)))
axisAverage4Commutes (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ siteF
  (pair (pair x0 x1) (pair x2 x3)) =
  quarterDoubleSumSwap
    (allCyclicIndices side4) (allCyclicIndices side4)
    (λ moving fixed → siteF (pair (pair moving x1) (pair fixed x3)))
axisAverage4Commutes (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ zeroᵢ) siteF
  (pair (pair x0 x1) (pair x2 x3)) =
  quarterDoubleSumSwap
    (allCyclicIndices side4) (allCyclicIndices side4)
    (λ moving fixed → siteF (pair (pair x0 moving) (pair fixed x3)))
axisAverage4Commutes (sucᵢ (sucᵢ zeroᵢ))
  (sucᵢ (sucᵢ zeroᵢ)) siteF site = refl
axisAverage4Commutes (sucᵢ (sucᵢ zeroᵢ))
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) siteF
  (pair (pair x0 x1) (pair x2 x3)) =
  quarterDoubleSumSwap
    (allCyclicIndices side4) (allCyclicIndices side4)
    (λ moving fixed → siteF (pair (pair x0 x1) (pair fixed moving)))
axisAverage4Commutes (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) zeroᵢ siteF
  (pair (pair x0 x1) (pair x2 x3)) =
  quarterDoubleSumSwap
    (allCyclicIndices side4) (allCyclicIndices side4)
    (λ moving fixed → siteF (pair (pair moving x1) (pair x2 fixed)))
axisAverage4Commutes (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ zeroᵢ) siteF (pair (pair x0 x1) (pair x2 x3)) =
  quarterDoubleSumSwap
    (allCyclicIndices side4) (allCyclicIndices side4)
    (λ moving fixed → siteF (pair (pair x0 moving) (pair x2 fixed)))
axisAverage4Commutes (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ (sucᵢ zeroᵢ)) siteF (pair (pair x0 x1) (pair x2 x3)) =
  quarterDoubleSumSwap
    (allCyclicIndices side4) (allCyclicIndices side4)
    (λ moving fixed → siteF (pair (pair x0 x1) (pair moving fixed)))
axisAverage4Commutes (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) siteF site = refl

------------------------------------------------------------------------
-- Centering has exactly zero fibre sum.
------------------------------------------------------------------------

side4CenteredTotalZero : ∀ total →
  1ℚ * total
    - natAsRational (length (allCyclicIndices side4)) * (quarter * total)
  ≡ 0ℚ
side4CenteredTotalZero total
  rewrite lengthAllCyclicIndices side4 = ℚRing.solve-∀ total

axisCentering4DirectFibreSumZero : ∀ siteF axis transverse →
  sumRational (allCyclicIndices side4)
    (λ coordinate →
      siteF (insertAxis axis coordinate transverse)
      - quarter * physicalFibreSum siteF axis transverse)
  ≡ 0ℚ
axisCentering4DirectFibreSumZero siteF axis transverse =
  trans
    (sumRationalCong
      (allCyclicIndices side4)
      (λ coordinate →
        siteF (insertAxis axis coordinate transverse)
        - quarter * physicalFibreSum siteF axis transverse)
      (λ coordinate →
        1ℚ * siteF (insertAxis axis coordinate transverse)
        - quarter * physicalFibreSum siteF axis transverse)
      (λ coordinate →
        ℚRing.solve-∀
          (siteF (insertAxis axis coordinate transverse))
          (physicalFibreSum siteF axis transverse)))
    (trans
      (sumScaledDifferenceFormula
        1ℚ
        (quarter * physicalFibreSum siteF axis transverse)
        (allCyclicIndices side4)
        (λ coordinate → siteF (insertAxis axis coordinate transverse)))
      (side4CenteredTotalZero (physicalFibreSum siteF axis transverse)))

axisCentering4FibreSumZero : ∀ siteF axis transverse →
  sumRational (allCyclicIndices side4)
    (λ coordinate →
      axisCentering4 siteF axis (insertAxis axis coordinate transverse))
  ≡ 0ℚ
axisCentering4FibreSumZero siteF axis transverse =
  trans
    (sumRationalCong
      (allCyclicIndices side4)
      (λ coordinate →
        axisCentering4 siteF axis (insertAxis axis coordinate transverse))
      (λ coordinate →
        siteF (insertAxis axis coordinate transverse)
        - quarter * physicalFibreSum siteF axis transverse)
      (axisCentering4OnFibre siteF axis transverse))
    (axisCentering4DirectFibreSumZero siteF axis transverse)

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
path4AxisAverageIdempotenceLevel = machineChecked

path4DistinctAxisAverageCommutationLevel : ProofLevel
path4DistinctAxisAverageCommutationLevel = machineChecked

path4AxisCenteringMeanZeroLevel : ProofLevel
path4AxisCenteringMeanZeroLevel = machineChecked

path4PhysicalMartingaleDecompositionLevel : ProofLevel
path4PhysicalMartingaleDecompositionLevel = machineChecked

path4PhysicalMartingaleOrthogonalityLevel : ProofLevel
path4PhysicalMartingaleOrthogonalityLevel = machineChecked
