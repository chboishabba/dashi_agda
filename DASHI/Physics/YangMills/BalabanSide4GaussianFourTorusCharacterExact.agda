module DASHI.Physics.YangMills.BalabanSide4GaussianFourTorusCharacterExact where

------------------------------------------------------------------------
-- EXACT Z4^4 CHARACTER LAWS ON THE LITERAL SIDE-FOUR TORUS
--
-- PRIMARY SOURCE
--
-- Walter Rudin, "Fourier Analysis on Groups", Wiley, 1962.
-- No DOI was assigned to this monograph.
--
-- DASHI CONTRIBUTION
--
-- Tensor the exhaustive C4 Gaussian-rational character laws to the actual
-- fourfold periodic carrier used by the side-four Green kernel:
--
--   chi(k+l,x) = chi(k,x) chi(l,x),
--   conjugate(chi(k,x)) = chi(-k,x).
--
-- The proof is exact rational algebra; it does not assume character
-- orthogonality, an analytic Fourier transform, or a continuum momentum
-- convention. This is the algebraic predecessor of the finite orthogonality
-- and inversion computation needed by literal plane-wave contractions.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (Product; pair)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
  using (PhysicalBlockL)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)
import DASHI.Physics.YangMills.BalabanSide4TranslationDifferenceExact as C4
import DASHI.Physics.YangMills.BalabanSide4ScalarGreenKernelComputed as Green
import DASHI.Physics.YangMills.BalabanSide4GaussianCharacterCoreExact as Core

Gaussianℚ : Set
Gaussianℚ = Green.Gaussianℚ

fourProductInterchange :
  ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  Green.multiplyGaussian
    (Green.multiplyGaussian a0 b0)
    (Green.multiplyGaussian
      (Green.multiplyGaussian a1 b1)
      (Green.multiplyGaussian
        (Green.multiplyGaussian a2 b2)
        (Green.multiplyGaussian a3 b3)))
  ≡
  Green.multiplyGaussian
    (Green.multiplyGaussian a0
      (Green.multiplyGaussian a1
        (Green.multiplyGaussian a2 a3)))
    (Green.multiplyGaussian b0
      (Green.multiplyGaussian b1
        (Green.multiplyGaussian b2 b3)))
fourProductInterchange
  (pair a0r a0i) (pair a1r a1i) (pair a2r a2i) (pair a3r a3i)
  (pair b0r b0i) (pair b1r b1i) (pair b2r b2i) (pair b3r b3i) =
  Core.gaussianExt
    (ℚRing.solve-∀ a0r a0i a1r a1i a2r a2i a3r a3i
      b0r b0i b1r b1i b2r b2i b3r b3i)
    (ℚRing.solve-∀ a0r a0i a1r a1i a2r a2i a3r a3i
      b0r b0i b1r b1i b2r b2i b3r b3i)

gaussianConjugateFourProduct :
  ∀ a0 a1 a2 a3 →
  Core.gaussianConjugate
    (Green.multiplyGaussian a0
      (Green.multiplyGaussian a1
        (Green.multiplyGaussian a2 a3)))
  ≡
  Green.multiplyGaussian (Core.gaussianConjugate a0)
    (Green.multiplyGaussian (Core.gaussianConjugate a1)
      (Green.multiplyGaussian (Core.gaussianConjugate a2)
        (Core.gaussianConjugate a3)))
gaussianConjugateFourProduct
  (pair a0r a0i) (pair a1r a1i) (pair a2r a2i) (pair a3r a3i) =
  Core.gaussianExt
    (ℚRing.solve-∀ a0r a0i a1r a1i a2r a2i a3r a3i)
    (ℚRing.solve-∀ a0r a0i a1r a1i a2r a2i a3r a3i)

character4AddExact :
  ∀ momentum shift site →
  Green.character4 (C4.translateSite4 momentum shift) site
  ≡ Green.multiplyGaussian
      (Green.character4 momentum site)
      (Green.character4 shift site)
character4AddExact
  (pair (pair k0 k1) (pair k2 k3))
  (pair (pair l0 l1) (pair l2 l3))
  (pair (pair x0 x1) (pair x2 x3))
  rewrite Core.character1AddExact k0 l0 x0
        | Core.character1AddExact k1 l1 x1
        | Core.character1AddExact k2 l2 x2
        | Core.character1AddExact k3 l3 x3 =
  fourProductInterchange
    (Green.character1 k0 x0) (Green.character1 k1 x1)
    (Green.character1 k2 x2) (Green.character1 k3 x3)
    (Green.character1 l0 x0) (Green.character1 l1 x1)
    (Green.character1 l2 x2) (Green.character1 l3 x3)

character4ConjugateExact :
  ∀ momentum site →
  Core.gaussianConjugate (Green.character4 momentum site)
  ≡ Green.character4 (C4.negateSite4 momentum) site
character4ConjugateExact
  (pair (pair k0 k1) (pair k2 k3))
  (pair (pair x0 x1) (pair x2 x3))
  rewrite gaussianConjugateFourProduct
    (Green.character1 k0 x0) (Green.character1 k1 x1)
    (Green.character1 k2 x2) (Green.character1 k3 x3)
        | Core.character1ConjugateExact k0 x0
        | Core.character1ConjugateExact k1 x1
        | Core.character1ConjugateExact k2 x2
        | Core.character1ConjugateExact k3 x3 = refl

side4GaussianFourTorusCharacterLevel : ProofLevel
side4GaussianFourTorusCharacterLevel = conditional

-- Remaining exact finite Fourier work: character orthogonality, inversion,
-- Parseval, and their normalization against the literal bond-coordinate
-- carrier. No physical beta conclusion is asserted here.
side4GaussianFourTorusFourierAuthorityLevel : ProofLevel
side4GaussianFourTorusFourierAuthorityLevel = conditional
