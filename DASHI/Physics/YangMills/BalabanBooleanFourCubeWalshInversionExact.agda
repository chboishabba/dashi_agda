module DASHI.Physics.YangMills.BalabanBooleanFourCubeWalshInversionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre, "Linear Representations of Finite Groups",
-- Springer, 1977. DOI: 10.1007/978-1-4684-9458-7.
--
-- Máté Matolcsi,
-- "A Walsh-Fourier Approach to the Circulant Hadamard Conjecture",
-- in Algebraic Design Theory and Hadamard Matrices,
-- Springer Proceedings in Mathematics & Statistics 133 (2015), 201--208.
-- DOI: 10.1007/978-3-319-17729-8_16.
--
-- DASHI CONTRIBUTION
--
-- Upgrade the Round60 character-cancellation layer from the special
-- "nontrivial characters kill constants" lemma to a complete finite Fourier
-- theorem on the SAME sixteen-element Subset4 carrier.
--
-- For f : (C2)^4 -> Q, with unnormalised Walsh coefficients
--
--   fhat(A) = sum_e chi_A(e) f(e),
--
-- prove the exact inversion formula
--
--   f(e) = (1/16) sum_A chi_A(e) fhat(A).
--
-- Consequently the full sixteen Walsh coefficients determine the source
-- function uniquely.  This matters for the YM use: character projection is a
-- lossless basis change before selected sectors are killed by physical
-- symmetry; it is not another quotient or interval enclosure.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanBooleanFourCubeWalshCharacterExact as Walsh

oneSixteenth : ℚ
oneSixteenth = + 1 / 16

walshReconstruct :
  (Cube.Subset4 → ℚ) → Cube.Subset4 → ℚ
walshReconstruct value signMask =
  oneSixteenth *
    Sums.sumRational Cube.allSubsets4
      (λ character →
        Walsh.walshCharacter character signMask
          * Walsh.walshCoefficient value character)

------------------------------------------------------------------------
-- Exact Walsh-Hadamard inversion.  The carrier has only sixteen points, so
-- each row is reduced directly by the rational ring solver against the same
-- sixteen symbolic source values.  No floating matrix calculation enters.
------------------------------------------------------------------------

walshReconstructionExact :
  (value : Cube.Subset4 → ℚ) →
  (signMask : Cube.Subset4) →
  walshReconstruct value signMask ≡ value signMask
walshReconstructionExact value Cube.empty =
  ℚRing.solve-∀
    (value Cube.empty)
    (value Cube.s0) (value Cube.s1) (value Cube.s2) (value Cube.s3)
    (value Cube.s01) (value Cube.s02) (value Cube.s03)
    (value Cube.s12) (value Cube.s13) (value Cube.s23)
    (value Cube.s012) (value Cube.s013) (value Cube.s023) (value Cube.s123)
    (value Cube.s0123)
walshReconstructionExact value Cube.s0 =
  ℚRing.solve-∀
    (value Cube.empty)
    (value Cube.s0) (value Cube.s1) (value Cube.s2) (value Cube.s3)
    (value Cube.s01) (value Cube.s02) (value Cube.s03)
    (value Cube.s12) (value Cube.s13) (value Cube.s23)
    (value Cube.s012) (value Cube.s013) (value Cube.s023) (value Cube.s123)
    (value Cube.s0123)
walshReconstructionExact value Cube.s1 =
  ℚRing.solve-∀
    (value Cube.empty)
    (value Cube.s0) (value Cube.s1) (value Cube.s2) (value Cube.s3)
    (value Cube.s01) (value Cube.s02) (value Cube.s03)
    (value Cube.s12) (value Cube.s13) (value Cube.s23)
    (value Cube.s012) (value Cube.s013) (value Cube.s023) (value Cube.s123)
    (value Cube.s0123)
walshReconstructionExact value Cube.s2 =
  ℚRing.solve-∀
    (value Cube.empty)
    (value Cube.s0) (value Cube.s1) (value Cube.s2) (value Cube.s3)
    (value Cube.s01) (value Cube.s02) (value Cube.s03)
    (value Cube.s12) (value Cube.s13) (value Cube.s23)
    (value Cube.s012) (value Cube.s013) (value Cube.s023) (value Cube.s123)
    (value Cube.s0123)
walshReconstructionExact value Cube.s3 =
  ℚRing.solve-∀
    (value Cube.empty)
    (value Cube.s0) (value Cube.s1) (value Cube.s2) (value Cube.s3)
    (value Cube.s01) (value Cube.s02) (value Cube.s03)
    (value Cube.s12) (value Cube.s13) (value Cube.s23)
    (value Cube.s012) (value Cube.s013) (value Cube.s023) (value Cube.s123)
    (value Cube.s0123)
walshReconstructionExact value Cube.s01 =
  ℚRing.solve-∀
    (value Cube.empty)
    (value Cube.s0) (value Cube.s1) (value Cube.s2) (value Cube.s3)
    (value Cube.s01) (value Cube.s02) (value Cube.s03)
    (value Cube.s12) (value Cube.s13) (value Cube.s23)
    (value Cube.s012) (value Cube.s013) (value Cube.s023) (value Cube.s123)
    (value Cube.s0123)
walshReconstructionExact value Cube.s02 =
  ℚRing.solve-∀
    (value Cube.empty)
    (value Cube.s0) (value Cube.s1) (value Cube.s2) (value Cube.s3)
    (value Cube.s01) (value Cube.s02) (value Cube.s03)
    (value Cube.s12) (value Cube.s13) (value Cube.s23)
    (value Cube.s012) (value Cube.s013) (value Cube.s023) (value Cube.s123)
    (value Cube.s0123)
walshReconstructionExact value Cube.s03 =
  ℚRing.solve-∀
    (value Cube.empty)
    (value Cube.s0) (value Cube.s1) (value Cube.s2) (value Cube.s3)
    (value Cube.s01) (value Cube.s02) (value Cube.s03)
    (value Cube.s12) (value Cube.s13) (value Cube.s23)
    (value Cube.s012) (value Cube.s013) (value Cube.s023) (value Cube.s123)
    (value Cube.s0123)
walshReconstructionExact value Cube.s12 =
  ℚRing.solve-∀
    (value Cube.empty)
    (value Cube.s0) (value Cube.s1) (value Cube.s2) (value Cube.s3)
    (value Cube.s01) (value Cube.s02) (value Cube.s03)
    (value Cube.s12) (value Cube.s13) (value Cube.s23)
    (value Cube.s012) (value Cube.s013) (value Cube.s023) (value Cube.s123)
    (value Cube.s0123)
walshReconstructionExact value Cube.s13 =
  ℚRing.solve-∀
    (value Cube.empty)
    (value Cube.s0) (value Cube.s1) (value Cube.s2) (value Cube.s3)
    (value Cube.s01) (value Cube.s02) (value Cube.s03)
    (value Cube.s12) (value Cube.s13) (value Cube.s23)
    (value Cube.s012) (value Cube.s013) (value Cube.s023) (value Cube.s123)
    (value Cube.s0123)
walshReconstructionExact value Cube.s23 =
  ℚRing.solve-∀
    (value Cube.empty)
    (value Cube.s0) (value Cube.s1) (value Cube.s2) (value Cube.s3)
    (value Cube.s01) (value Cube.s02) (value Cube.s03)
    (value Cube.s12) (value Cube.s13) (value Cube.s23)
    (value Cube.s012) (value Cube.s013) (value Cube.s023) (value Cube.s123)
    (value Cube.s0123)
walshReconstructionExact value Cube.s012 =
  ℚRing.solve-∀
    (value Cube.empty)
    (value Cube.s0) (value Cube.s1) (value Cube.s2) (value Cube.s3)
    (value Cube.s01) (value Cube.s02) (value Cube.s03)
    (value Cube.s12) (value Cube.s13) (value Cube.s23)
    (value Cube.s012) (value Cube.s013) (value Cube.s023) (value Cube.s123)
    (value Cube.s0123)
walshReconstructionExact value Cube.s013 =
  ℚRing.solve-∀
    (value Cube.empty)
    (value Cube.s0) (value Cube.s1) (value Cube.s2) (value Cube.s3)
    (value Cube.s01) (value Cube.s02) (value Cube.s03)
    (value Cube.s12) (value Cube.s13) (value Cube.s23)
    (value Cube.s012) (value Cube.s013) (value Cube.s023) (value Cube.s123)
    (value Cube.s0123)
walshReconstructionExact value Cube.s023 =
  ℚRing.solve-∀
    (value Cube.empty)
    (value Cube.s0) (value Cube.s1) (value Cube.s2) (value Cube.s3)
    (value Cube.s01) (value Cube.s02) (value Cube.s03)
    (value Cube.s12) (value Cube.s13) (value Cube.s23)
    (value Cube.s012) (value Cube.s013) (value Cube.s023) (value Cube.s123)
    (value Cube.s0123)
walshReconstructionExact value Cube.s123 =
  ℚRing.solve-∀
    (value Cube.empty)
    (value Cube.s0) (value Cube.s1) (value Cube.s2) (value Cube.s3)
    (value Cube.s01) (value Cube.s02) (value Cube.s03)
    (value Cube.s12) (value Cube.s13) (value Cube.s23)
    (value Cube.s012) (value Cube.s013) (value Cube.s023) (value Cube.s123)
    (value Cube.s0123)
walshReconstructionExact value Cube.s0123 =
  ℚRing.solve-∀
    (value Cube.empty)
    (value Cube.s0) (value Cube.s1) (value Cube.s2) (value Cube.s3)
    (value Cube.s01) (value Cube.s02) (value Cube.s03)
    (value Cube.s12) (value Cube.s13) (value Cube.s23)
    (value Cube.s012) (value Cube.s013) (value Cube.s023) (value Cube.s123)
    (value Cube.s0123)

------------------------------------------------------------------------
-- Equal character data imply equal fine functions.  The Walsh transform is
-- therefore a basis change, not a quotient.
------------------------------------------------------------------------

walshReconstructCong :
  (left right : Cube.Subset4 → ℚ) →
  ((character : Cube.Subset4) →
    Walsh.walshCoefficient left character
      ≡ Walsh.walshCoefficient right character) →
  (signMask : Cube.Subset4) →
  walshReconstruct left signMask ≡ walshReconstruct right signMask
walshReconstructCong left right coefficientsEqual signMask =
  cong (λ total → oneSixteenth * total)
    (Sums.sumRationalCong
      Cube.allSubsets4
      (λ character →
        Walsh.walshCharacter character signMask
          * Walsh.walshCoefficient left character)
      (λ character →
        Walsh.walshCharacter character signMask
          * Walsh.walshCoefficient right character)
      (λ character →
        cong
          (λ coefficient →
            Walsh.walshCharacter character signMask * coefficient)
          (coefficientsEqual character)))

walshTransformInjective :
  (left right : Cube.Subset4 → ℚ) →
  ((character : Cube.Subset4) →
    Walsh.walshCoefficient left character
      ≡ Walsh.walshCoefficient right character) →
  (signMask : Cube.Subset4) →
  left signMask ≡ right signMask
walshTransformInjective left right coefficientsEqual signMask =
  trans
    (sym (walshReconstructionExact left signMask))
    (trans
      (walshReconstructCong left right coefficientsEqual signMask)
      (walshReconstructionExact right signMask))

booleanFourCubeWalshInversionLevel : ProofLevel
booleanFourCubeWalshInversionLevel = machineChecked

booleanFourCubeWalshInjectivityLevel : ProofLevel
booleanFourCubeWalshInjectivityLevel = machineChecked
