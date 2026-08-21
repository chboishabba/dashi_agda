module DASHI.Physics.YangMills.BalabanSide4GaussianCharacterOrthogonalityExact where

------------------------------------------------------------------------
-- EXACT C4 CHARACTER ORTHOGONALITY OVER GAUSSIAN RATIONALS
--
-- PRIMARY SOURCE
--
-- Walter Rudin, "Fourier Analysis on Groups", Wiley, 1962.
-- No DOI was assigned to this monograph.
--
-- DASHI CONTRIBUTION
--
-- Evaluate the literal four-point character inner product exactly:
--
--   sum_x chi(k,x) conjugate(chi(l,x)) = 4 delta_(k,l).
--
-- This is a finite rational calculation on the same C4 table used by the
-- side-four Green kernel. It is the one-dimensional factor for the Z4^4
-- orthogonality and inversion theorem; no analytic Fourier theorem is used.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (CyclicIndex; zeroᵢ; sucᵢ; four; Product; pair)
import DASHI.Physics.YangMills.BalabanSide4ScalarGreenKernelComputed as Green
import DASHI.Physics.YangMills.BalabanSide4GaussianCharacterCoreExact as Core

Gaussianℚ : Set
Gaussianℚ = Green.Gaussianℚ

zeroGaussian oneGaussian : Gaussianℚ
zeroGaussian = pair 0ℚ 0ℚ
oneGaussian = pair 1ℚ 0ℚ

gaussianAdd : Gaussianℚ → Gaussianℚ → Gaussianℚ
gaussianAdd (pair leftReal leftImaginary) (pair rightReal rightImaginary) =
  pair (leftReal + rightReal) (leftImaginary + rightImaginary)

fourGaussian : Gaussianℚ
fourGaussian =
  gaussianAdd oneGaussian
    (gaussianAdd oneGaussian (gaussianAdd oneGaussian oneGaussian))

characterInner1 : CyclicIndex four → CyclicIndex four → Gaussianℚ
characterInner1 k l =
  gaussianAdd
    (Green.multiplyGaussian (Green.character1 k zeroᵢ)
      (Core.gaussianConjugate (Green.character1 l zeroᵢ)))
    (gaussianAdd
      (Green.multiplyGaussian (Green.character1 k (sucᵢ zeroᵢ))
        (Core.gaussianConjugate
          (Green.character1 l (sucᵢ zeroᵢ))))
      (gaussianAdd
        (Green.multiplyGaussian
          (Green.character1 k (sucᵢ (sucᵢ zeroᵢ)))
          (Core.gaussianConjugate
            (Green.character1 l (sucᵢ (sucᵢ zeroᵢ)))))
        (Green.multiplyGaussian
          (Green.character1 k (sucᵢ (sucᵢ (sucᵢ zeroᵢ))))
          (Core.gaussianConjugate
            (Green.character1 l (sucᵢ (sucᵢ (sucᵢ zeroᵢ))))))))

c4Kronecker : CyclicIndex four → CyclicIndex four → Gaussianℚ
c4Kronecker zeroᵢ zeroᵢ = fourGaussian
c4Kronecker zeroᵢ sucᵢ zeroᵢ = zeroGaussian
c4Kronecker zeroᵢ sucᵢ (sucᵢ zeroᵢ) = zeroGaussian
c4Kronecker zeroᵢ sucᵢ (sucᵢ (sucᵢ zeroᵢ)) = zeroGaussian
c4Kronecker sucᵢ zeroᵢ zeroᵢ = zeroGaussian
c4Kronecker sucᵢ zeroᵢ sucᵢ zeroᵢ = fourGaussian
c4Kronecker sucᵢ zeroᵢ sucᵢ (sucᵢ zeroᵢ) = zeroGaussian
c4Kronecker sucᵢ zeroᵢ sucᵢ (sucᵢ (sucᵢ zeroᵢ)) = zeroGaussian
c4Kronecker sucᵢ (sucᵢ zeroᵢ) zeroᵢ = zeroGaussian
c4Kronecker sucᵢ (sucᵢ zeroᵢ) sucᵢ zeroᵢ = zeroGaussian
c4Kronecker sucᵢ (sucᵢ zeroᵢ) sucᵢ (sucᵢ zeroᵢ) = fourGaussian
c4Kronecker sucᵢ (sucᵢ zeroᵢ) sucᵢ (sucᵢ (sucᵢ zeroᵢ)) = zeroGaussian
c4Kronecker sucᵢ (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ = zeroGaussian
c4Kronecker sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ zeroᵢ = zeroGaussian
c4Kronecker sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ (sucᵢ zeroᵢ) = zeroGaussian
c4Kronecker sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ (sucᵢ (sucᵢ zeroᵢ)) = fourGaussian

character1OrthogonalityExact : ∀ k l →
  characterInner1 k l ≡ c4Kronecker k l
character1OrthogonalityExact zeroᵢ zeroᵢ =
  Core.gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1OrthogonalityExact zeroᵢ sucᵢ zeroᵢ =
  Core.gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1OrthogonalityExact zeroᵢ sucᵢ (sucᵢ zeroᵢ) =
  Core.gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1OrthogonalityExact zeroᵢ sucᵢ (sucᵢ (sucᵢ zeroᵢ)) =
  Core.gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1OrthogonalityExact sucᵢ zeroᵢ zeroᵢ =
  Core.gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1OrthogonalityExact sucᵢ zeroᵢ sucᵢ zeroᵢ =
  Core.gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1OrthogonalityExact sucᵢ zeroᵢ sucᵢ (sucᵢ zeroᵢ) =
  Core.gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1OrthogonalityExact sucᵢ zeroᵢ sucᵢ (sucᵢ (sucᵢ zeroᵢ)) =
  Core.gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1OrthogonalityExact sucᵢ (sucᵢ zeroᵢ) zeroᵢ =
  Core.gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1OrthogonalityExact sucᵢ (sucᵢ zeroᵢ) sucᵢ zeroᵢ =
  Core.gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1OrthogonalityExact sucᵢ (sucᵢ zeroᵢ) sucᵢ (sucᵢ zeroᵢ) =
  Core.gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1OrthogonalityExact sucᵢ (sucᵢ zeroᵢ) sucᵢ (sucᵢ (sucᵢ zeroᵢ)) =
  Core.gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1OrthogonalityExact sucᵢ (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ =
  Core.gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1OrthogonalityExact sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ zeroᵢ =
  Core.gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1OrthogonalityExact sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ (sucᵢ zeroᵢ) =
  Core.gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1OrthogonalityExact sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ (sucᵢ (sucᵢ zeroᵢ)) =
  Core.gaussianExt (ℚRing.solve []) (ℚRing.solve [])

side4GaussianCharacterC4OrthogonalityLevel : ProofLevel
side4GaussianCharacterC4OrthogonalityLevel = conditional

-- The remaining Fourier step is tensoring this exact identity over four
-- coordinates and deriving inversion/Parseval with the literal 1/256 factor.
side4GaussianCharacterFourTorusOrthogonalityLevel : ProofLevel
side4GaussianCharacterFourTorusOrthogonalityLevel = conditional
