module DASHI.Physics.YangMills.BalabanSelectedBlockAverageSectionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Franco Brezzi,
-- "On the Existence, Uniqueness and Approximation of Saddle-Point Problems
-- Arising from Lagrangian Multipliers",
-- RAIRO Analyse Numerique 8 (1974), 129--151.
-- No DOI was assigned to the cited article.
--
-- Roger A. Horn; Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Construct an exact right inverse of the literal side-four P33 block-average
-- constraint.  Each requested Lie-coordinate/direction average is spread
-- uniformly over the 256 physical sites with coefficient 1/256.  The finite
-- sum then recovers the requested multiplier value exactly.  This proves the
-- twelve average rows are genuinely independent before they are coupled to
-- the gauge rows; no rank claim is inferred from dimensions alone.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (length)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanP33LiteralResidualKernelNumericalCalibrationExact as Count
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanSelectedBackgroundBlockAverageConstraintMatrixExact as Average

oneOverSiteCount : ℚ
oneOverSiteCount = + 1 / 256

siteCount : ℚ
siteCount = + 256 / 1

sumConstantAsLength :
  ∀ {A : Set} (values : List A) constant →
  Sums.sumRational values (λ _ → constant)
  ≡ Sums.natAsRational (length values) * constant
sumConstantAsLength [] constant =
  ℚRing.solve-∀ constant
sumConstantAsLength (_ ∷ values) constant
  rewrite sumConstantAsLength values constant =
  ℚRing.solve-∀ constant (Sums.natAsRational (length values))

sideFourSumConstantExact : ∀ constant →
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ _ → constant)
  ≡ siteCount * constant
sideFourSumConstantExact constant =
  trans
    (sumConstantAsLength
      (Block.physicalBlockSites Path4.side4) constant)
    (cong (_* constant)
      (trans
        (cong Sums.natAsRational Count.periodicSide4SiteCount)
        refl))

selectedBlockAverageSection :
  (Average.SelectedBlockAverageRow4 → ℚ) → KKT.StateVector
selectedBlockAverageSection multiplier
    (pair coordinate (pair axis site)) =
  oneOverSiteCount * multiplier (pair coordinate axis)

selectedBlockAverageSectionExact :
  ∀ multiplier row →
  Average.selectedBackgroundBlockAverageConstraintApply
    (selectedBlockAverageSection multiplier) row
  ≡ multiplier row
selectedBlockAverageSectionExact multiplier (pair coordinate axis) =
  trans
    (Average.selectedBackgroundBlockAverageConstraintMatrixApplyExact
      (selectedBlockAverageSection multiplier)
      (pair coordinate axis))
    (trans
      (sideFourSumConstantExact
        (oneOverSiteCount * multiplier (pair coordinate axis)))
      (ℚRing.solve-∀ (multiplier (pair coordinate axis))))

record SelectedBlockAveragePreimage
    (multiplier : Average.SelectedBlockAverageRow4 → ℚ) : Set where
  field
    state : KKT.StateVector
    mapsExactly : ∀ row →
      Average.selectedBackgroundBlockAverageConstraintApply state row
      ≡ multiplier row
open SelectedBlockAveragePreimage public

selectedBlockAverageConstraintSurjective :
  ∀ multiplier → SelectedBlockAveragePreimage multiplier
selectedBlockAverageConstraintSurjective multiplier = record
  { state = selectedBlockAverageSection multiplier
  ; mapsExactly = selectedBlockAverageSectionExact multiplier
  }

record SelectedBlockAverageRowRelation
    (coefficients : Average.SelectedBlockAverageRow4 → ℚ) : Set where
  field
    annihilatesAllStates : ∀ state →
      Sums.sumRational Average.selectedBlockAverageRows4
        (λ row → coefficients row
          * Average.selectedBackgroundBlockAverageConstraintApply state row)
      ≡ 0ℚ
open SelectedBlockAverageRowRelation public

-- The section is the constructive rank certificate needed downstream.  A
-- separate finite-row delta carrier can turn this into the customary statement
-- that every annihilating coefficient is zero pointwise; no such carrier is
-- assumed here merely from the count twelve.

selectedBlockAverageSectionLevel : ProofLevel
selectedBlockAverageSectionLevel = machineChecked

selectedBlockAverageRowIndependenceProducerLevel : ProofLevel
selectedBlockAverageRowIndependenceProducerLevel = machineChecked
