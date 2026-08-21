module DASHI.Physics.YangMills.BalabanSide4GaussianCharacterCoreExact where

------------------------------------------------------------------------
-- EXACT C4 CHARACTER CORE FOR THE LITERAL SIDE-FOUR FOURIER CARRIER
--
-- PRIMARY SOURCE
--
-- Walter Rudin, "Fourier Analysis on Groups", Wiley, 1962.
-- No DOI was assigned to this monograph.
--
-- DASHI CONTRIBUTION
--
-- The computed side-four Green kernel already defines the literal
-- Gaussian-rational character table
--
--     chi(k,x) = exp(2 pi i kx / 4)
--
-- as a finite Q[i] table. This file proves the two one-dimensional character
-- laws by complete rational normalization:
--
--     chi(k+l,x) = chi(k,x) chi(l,x),
--     conjugate(chi(k,x)) = chi(-k,x).
--
-- It is the finite algebraic core needed before the table can inhabit the
-- generic Fourier-authority surface. No continuum period, numerical
-- trigonometry, or imported complex-analysis theorem appears here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _-_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (CyclicIndex; zeroᵢ; sucᵢ; four; Product; pair; first; second)
import DASHI.Physics.YangMills.BalabanSide4TranslationDifferenceExact as C4
import DASHI.Physics.YangMills.BalabanSide4ScalarGreenKernelComputed as Green

Gaussianℚ : Set
Gaussianℚ = Green.Gaussianℚ

gaussianConjugate : Gaussianℚ → Gaussianℚ
gaussianConjugate (pair real imaginary) = pair real (- imaginary)

gaussianExt : ∀ {left right : Gaussianℚ} →
  Green.realPart left ≡ Green.realPart right →
  Green.imaginaryPart left ≡ Green.imaginaryPart right →
  left ≡ right
gaussianExt {pair leftReal leftImaginary} {pair rightReal rightImaginary}
  refl refl = refl

character1AddExact : ∀ k l x →
  Green.character1 (C4.add4 k l) x
  ≡ Green.multiplyGaussian (Green.character1 k x) (Green.character1 l x)
character1AddExact zeroᵢ zeroᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact zeroᵢ zeroᵢ sucᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact zeroᵢ zeroᵢ sucᵢ (sucᵢ zeroᵢ) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact zeroᵢ zeroᵢ sucᵢ (sucᵢ (sucᵢ zeroᵢ)) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact zeroᵢ sucᵢ zeroᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact zeroᵢ sucᵢ zeroᵢ sucᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact zeroᵢ sucᵢ zeroᵢ sucᵢ (sucᵢ zeroᵢ) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact zeroᵢ sucᵢ zeroᵢ sucᵢ (sucᵢ (sucᵢ zeroᵢ)) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact zeroᵢ sucᵢ (sucᵢ zeroᵢ) zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact zeroᵢ sucᵢ (sucᵢ zeroᵢ) sucᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact zeroᵢ sucᵢ (sucᵢ zeroᵢ) sucᵢ (sucᵢ zeroᵢ) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact zeroᵢ sucᵢ (sucᵢ zeroᵢ) sucᵢ (sucᵢ (sucᵢ zeroᵢ)) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact zeroᵢ sucᵢ (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact zeroᵢ sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact zeroᵢ sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ (sucᵢ zeroᵢ) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact zeroᵢ sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ (sucᵢ (sucᵢ zeroᵢ)) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ zeroᵢ zeroᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ zeroᵢ zeroᵢ sucᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ zeroᵢ zeroᵢ sucᵢ (sucᵢ zeroᵢ) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ zeroᵢ zeroᵢ sucᵢ (sucᵢ (sucᵢ zeroᵢ)) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ zeroᵢ sucᵢ zeroᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ zeroᵢ sucᵢ zeroᵢ sucᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ zeroᵢ sucᵢ zeroᵢ sucᵢ (sucᵢ zeroᵢ) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ zeroᵢ sucᵢ zeroᵢ sucᵢ (sucᵢ (sucᵢ zeroᵢ)) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ zeroᵢ sucᵢ (sucᵢ zeroᵢ) zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ zeroᵢ sucᵢ (sucᵢ zeroᵢ) sucᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ zeroᵢ sucᵢ (sucᵢ zeroᵢ) sucᵢ (sucᵢ zeroᵢ) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ zeroᵢ sucᵢ (sucᵢ zeroᵢ) sucᵢ (sucᵢ (sucᵢ zeroᵢ)) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ zeroᵢ sucᵢ (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ zeroᵢ sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ zeroᵢ sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ (sucᵢ zeroᵢ) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ zeroᵢ sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ (sucᵢ (sucᵢ zeroᵢ)) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ zeroᵢ) zeroᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ zeroᵢ) zeroᵢ sucᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ zeroᵢ) zeroᵢ sucᵢ (sucᵢ zeroᵢ) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ zeroᵢ) zeroᵢ sucᵢ (sucᵢ (sucᵢ zeroᵢ)) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ zeroᵢ) sucᵢ zeroᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ zeroᵢ) sucᵢ zeroᵢ sucᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ zeroᵢ) sucᵢ zeroᵢ sucᵢ (sucᵢ zeroᵢ) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ zeroᵢ) sucᵢ zeroᵢ sucᵢ (sucᵢ (sucᵢ zeroᵢ)) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ zeroᵢ) sucᵢ (sucᵢ zeroᵢ) zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ zeroᵢ) sucᵢ (sucᵢ zeroᵢ) sucᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ zeroᵢ) sucᵢ (sucᵢ zeroᵢ) sucᵢ (sucᵢ zeroᵢ) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ zeroᵢ) sucᵢ (sucᵢ zeroᵢ) sucᵢ (sucᵢ (sucᵢ zeroᵢ)) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ zeroᵢ) sucᵢ (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ zeroᵢ) sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ zeroᵢ) sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ (sucᵢ zeroᵢ) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ zeroᵢ) sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ (sucᵢ (sucᵢ zeroᵢ)) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ sucᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ sucᵢ (sucᵢ zeroᵢ) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ sucᵢ (sucᵢ (sucᵢ zeroᵢ)) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ zeroᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ zeroᵢ sucᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ zeroᵢ sucᵢ (sucᵢ zeroᵢ) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ zeroᵢ sucᵢ (sucᵢ (sucᵢ zeroᵢ)) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ (sucᵢ zeroᵢ) zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ (sucᵢ zeroᵢ) sucᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ (sucᵢ zeroᵢ) sucᵢ (sucᵢ zeroᵢ) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ (sucᵢ zeroᵢ) sucᵢ (sucᵢ (sucᵢ zeroᵢ)) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ (sucᵢ zeroᵢ) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1AddExact sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ (sucᵢ (sucᵢ zeroᵢ)) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])

character1ConjugateExact : ∀ k x →
  gaussianConjugate (Green.character1 k x)
  ≡ Green.character1 (C4.negate4 k) x
character1ConjugateExact zeroᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1ConjugateExact zeroᵢ sucᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1ConjugateExact zeroᵢ sucᵢ (sucᵢ zeroᵢ) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1ConjugateExact zeroᵢ sucᵢ (sucᵢ (sucᵢ zeroᵢ)) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1ConjugateExact sucᵢ zeroᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1ConjugateExact sucᵢ zeroᵢ sucᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1ConjugateExact sucᵢ zeroᵢ sucᵢ (sucᵢ zeroᵢ) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1ConjugateExact sucᵢ zeroᵢ sucᵢ (sucᵢ (sucᵢ zeroᵢ)) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1ConjugateExact sucᵢ (sucᵢ zeroᵢ) zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1ConjugateExact sucᵢ (sucᵢ zeroᵢ) sucᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1ConjugateExact sucᵢ (sucᵢ zeroᵢ) sucᵢ (sucᵢ zeroᵢ) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1ConjugateExact sucᵢ (sucᵢ zeroᵢ) sucᵢ (sucᵢ (sucᵢ zeroᵢ)) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1ConjugateExact sucᵢ (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1ConjugateExact sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ zeroᵢ =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1ConjugateExact sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ (sucᵢ zeroᵢ) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])
character1ConjugateExact sucᵢ (sucᵢ (sucᵢ zeroᵢ)) sucᵢ (sucᵢ (sucᵢ zeroᵢ)) =
  gaussianExt (ℚRing.solve []) (ℚRing.solve [])

side4GaussianCharacterC4CoreLevel : ProofLevel
side4GaussianCharacterC4CoreLevel = conditional

-- Remaining physical Fourier work: tensor these laws to the literal
-- four-torus, prove finite character orthogonality/inversion with the same
-- normalization, then use that authority in the Wilson/FP/Haar plane-wave
-- contraction. None of those steps is asserted here.
side4GaussianCharacterFourTorusOrthogonalityLevel : ProofLevel
side4GaussianCharacterFourTorusOrthogonalityLevel = conditional
