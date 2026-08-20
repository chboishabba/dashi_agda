module DASHI.Physics.YangMills.BalabanCMP109SelectedKernelVectorIntegratesExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Wojciech Dybalski, Alexander Stottmeister, Yoh Tanimoto,
-- "The Bałaban variational problem in the non-linear sigma model",
-- arXiv:2403.09800 (2024).
--
-- DASHI CONTRIBUTION
--
-- Quantitative form of the canonical tangent-curve step.  If a kernel-line
-- constraint residual is epsilon-small relative to |t| and the unique reopened
-- normal correction obeys the already-proved 4/3 bound, then the correction
-- term in
--
--   gamma_h(t) = A + t h + N_A c_h(t)
--
-- is (4/3 epsilon)|t|-small.  Thus gamma_h(t)=A+t h+o(t) once the physical
-- printed-map remainder is little-o.  This keeps the tangent argument strictly
-- first-order and does not shortcut the Wilson Hessian through an o(t) curve.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

fourThirds : ℚ
fourThirds = + 4 / 3

record CanonicalKernelCurveEstimate
    (timeMagnitude residualMagnitude correctionMagnitude epsilon : ℚ) : Set where
  field
    timeNonnegative : 0ℚ ≤ timeMagnitude
    residualNonnegative : 0ℚ ≤ residualMagnitude
    correctionNonnegative : 0ℚ ≤ correctionMagnitude
    residualLittleOAtScale : residualMagnitude ≤ epsilon * timeMagnitude
    canonicalCorrectionFourThirds :
      correctionMagnitude ≤ fourThirds * residualMagnitude

open CanonicalKernelCurveEstimate public

canonicalKernelCurveCorrectionLittleO :
  ∀ timeMagnitude residualMagnitude correctionMagnitude epsilon →
  CanonicalKernelCurveEstimate
    timeMagnitude residualMagnitude correctionMagnitude epsilon →
  correctionMagnitude ≤ (fourThirds * epsilon) * timeMagnitude
canonicalKernelCurveCorrectionLittleO
    timeMagnitude residualMagnitude correctionMagnitude epsilon data =
  let
    scaled = Norm.scaleNonnegative fourThirds
      (ℚP.nonNegative⁻¹ fourThirds)
      (residualLittleOAtScale data)
    chained = ℚP.≤-trans (canonicalCorrectionFourThirds data) scaled
  in
  subst
    (λ upper → correctionMagnitude ≤ upper)
    (ℚRing.solve-∀ epsilon timeMagnitude)
    chained

selectedKernelVectorIntegratesFirstOrderLevel : ProofLevel
selectedKernelVectorIntegratesFirstOrderLevel = machineChecked
