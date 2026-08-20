module DASHI.Physics.YangMills.BalabanBooleanFourCubeWalshProjectorDecompositionExact where

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
-- Turn the complete Round60 Walsh transform into explicit normalized character
-- sectors.  This is the exact finite analogue of the intended physical
-- pipeline:
--
--   fine integrand -> character sectors -> kill forbidden sectors -> retain
--   trivial sector -> orbit quotient -> interval enclosure.
--
-- The decomposition itself is lossless; information is discarded only when a
-- physical symmetry theorem proves selected sector coefficients vanish.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanBooleanFourCubeWalshCharacterExact as Walsh
import DASHI.Physics.YangMills.BalabanBooleanFourCubeWalshInversionExact as Inverse

characterSector :
  (Cube.Subset4 → ℚ) → Cube.Subset4 → Cube.Subset4 → ℚ
characterSector value character signMask =
  Inverse.oneSixteenth
    * Walsh.walshCharacter character signMask
    * Walsh.walshCoefficient value character

sumCharacterSectors :
  (Cube.Subset4 → ℚ) → Cube.Subset4 → ℚ
sumCharacterSectors value signMask =
  Sums.sumRational Cube.allSubsets4
    (λ character → characterSector value character signMask)

------------------------------------------------------------------------
-- The normalized sectors reconstruct every fine function exactly.
------------------------------------------------------------------------

characterSectorReconstruction :
  (value : Cube.Subset4 → ℚ) →
  (signMask : Cube.Subset4) →
  sumCharacterSectors value signMask ≡ value signMask
characterSectorReconstruction value signMask =
  trans
    (Sums.sumRationalScale
      Inverse.oneSixteenth
      Cube.allSubsets4
      (λ character →
        Walsh.walshCharacter character signMask
          * Walsh.walshCoefficient value character))
    (Inverse.walshReconstructionExact value signMask)

------------------------------------------------------------------------
-- Constant functions occupy only the trivial character sector.
------------------------------------------------------------------------

nontrivialCharacterSectorOfConstantZero :
  ∀ {character} →
  Walsh.NontrivialWalshCharacter character →
  (constant : ℚ) →
  (signMask : Cube.Subset4) →
  characterSector (Walsh.constantFunction constant) character signMask ≡ 0ℚ
nontrivialCharacterSectorOfConstantZero {character} nontrivial constant signMask
  rewrite Walsh.nontrivialWalshKillsConstant nontrivial constant =
  ℚRing.solve-∀ (Walsh.walshCharacter character signMask)

trivialCharacterSectorOfConstantExact :
  (constant : ℚ) →
  (signMask : Cube.Subset4) →
  characterSector (Walsh.constantFunction constant) Cube.empty signMask
    ≡ constant
trivialCharacterSectorOfConstantExact constant signMask
  rewrite Walsh.trivialWalshConstantIsSixteen constant =
  ℚRing.solve-∀ constant

------------------------------------------------------------------------
-- Semantic boundary: the equations above prove that the Walsh layer is a
-- lossless decomposition.  No theorem here deletes a nontrivial sector.
-- Sector deletion must come from the separate physical reflection/equivariance
-- theorem in BalabanCMP109WalshCharacterOrbitCancellationExact.
------------------------------------------------------------------------

booleanFourCubeWalshProjectorDecompositionLevel : ProofLevel
booleanFourCubeWalshProjectorDecompositionLevel = machineChecked
