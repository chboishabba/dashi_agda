module DASHI.Moonshine.Monster3BZetaSuzukiDiagonalNormCutsetExact where

------------------------------------------------------------------------
-- ZETA SOURCE-IDENTITY CUTSET: 12 + Sym²(12) VS 12 + Sym²(12)*.
--
-- This does not create a new cyclotomic algebra. It CONSUMES the existing
-- Q(zeta_3) algebra/trace/norm owner and the original exact diagonal-kernel
-- ownership. Source roots:
--   Barraclough--Wilson, LMS J. Comput. Math. 10 (2007),
--       DOI 10.1112/S1461157000001352;
--   Gabriele Nebe, Symmetrizations of quadratic and Hermitian forms
--       J. Alg. Combin. 61 (2025), DOI 10.1007/s10801-025-01399-2.
--
-- Fundamental conditional requirement: if 729⊗12 and 729⊗78 use the
-- SAME extended H729 representation, and the SAME diagonal C3 kernel
-- acts trivially on both, the two Suzuki-side central C3 scalars
-- must be equal. This hypothesis is a typed argument below, NOT an
-- assertion that an actual Monster normalizer intertwiner exists.
--
-- The paper/source kernel subgroup is paid up to central orientation;
-- absolute ζ vs ζ² labels are a gauge. Consequently the conditional
-- viable central fingerprint is pure 90ζ or pure 90ζ². Mixed cases
-- have cyclotomic norm 5292 vs pure cases 8100; the norm is invariant
-- under the unresolved ζ <-> ζ² choice.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BCyclotomicLinearAlgebraExact as Lin
import DASHI.Moonshine.Monster3BCyclotomicNormSeparationExact as Norm
import DASHI.Wikimedia.IbrahimMonster3BDiagonalKernelPaidSignGaugeCorrectionExact as Kernel
import DASHI.Wikimedia.IbrahimMonster3BPhaseOrientationGaugeSnowballExact as Gauge
import DASHI.Moonshine.Monster3BJFineNineCellSymmetricSquareD4Exact as Nine

data SuzukiCentralPhase : Set where
  phaseZeta phaseZetaSquared : SuzukiCentralPhase

data SuzukiSeventyEight : Set where
  directSymmetricSquare dualSymmetricSquare : SuzukiSeventyEight

phaseOfSeventyEight :
  SuzukiCentralPhase → SuzukiSeventyEight → SuzukiCentralPhase
phaseOfSeventyEight phaseZeta directSymmetricSquare = phaseZetaSquared
phaseOfSeventyEight phaseZetaSquared directSymmetricSquare = phaseZeta
phaseOfSeventyEight phaseZeta dualSymmetricSquare = phaseZeta
phaseOfSeventyEight phaseZetaSquared dualSymmetricSquare = phaseZetaSquared

-- This equality is the necessary central-scalar consequence of one
-- common 729 extension and one common diagonal quotient kernel.
CommonH729DiagonalPhase :
  SuzukiCentralPhase → SuzukiSeventyEight → Set
CommonH729DiagonalPhase p v = p ≡ phaseOfSeventyEight p v

directSym2NeverHasCommonDiagonalPhase :
  (p : SuzukiCentralPhase) →
  CommonH729DiagonalPhase p directSymmetricSquare → ⊥
directSym2NeverHasCommonDiagonalPhase phaseZeta ()
directSym2NeverHasCommonDiagonalPhase phaseZetaSquared ()

dualSym2AlwaysHasCommonDiagonalPhase :
  (p : SuzukiCentralPhase) →
  CommonH729DiagonalPhase p dualSymmetricSquare
dualSym2AlwaysHasCommonDiagonalPhase phaseZeta = refl
dualSym2AlwaysHasCommonDiagonalPhase phaseZetaSquared = refl

-- Four original central-C3 fingerprints using existing Q(zeta_3) values,
-- with 12+78 coefficients, rather than repeated cyclotomic operations.
centreFingerprint :
  SuzukiCentralPhase → SuzukiSeventyEight → C3.Cyclotomic3
centreFingerprint phaseZeta directSymmetricSquare =
  Lin.add (Lin.scale 12 C3.zeta) (Lin.scale 78 C3.zetaSquared)
centreFingerprint phaseZeta dualSymmetricSquare =
  Lin.add (Lin.scale 12 C3.zeta) (Lin.scale 78 C3.zeta)
centreFingerprint phaseZetaSquared directSymmetricSquare =
  Lin.add (Lin.scale 12 C3.zetaSquared) (Lin.scale 78 C3.zeta)
centreFingerprint phaseZetaSquared dualSymmetricSquare =
  Lin.add (Lin.scale 12 C3.zetaSquared) (Lin.scale 78 C3.zetaSquared)

-- Galois TRACE is -90 in all four cases. It CANNOT distinguish
-- source-compatible from incompatible central actions.
allFourGaloisTracesAreMinusNinety :
  (p : SuzukiCentralPhase) → (v : SuzukiSeventyEight) →
  C3.trace (centreFingerprint p v) ≡ - (90 * 1ℚ)
allFourGaloisTracesAreMinusNinety phaseZeta directSymmetricSquare = solve []
allFourGaloisTracesAreMinusNinety phaseZeta dualSymmetricSquare = solve []
allFourGaloisTracesAreMinusNinety phaseZetaSquared directSymmetricSquare = solve []
allFourGaloisTracesAreMinusNinety phaseZetaSquared dualSymmetricSquare = solve []

-- N(a+bζ) = a²-ab+b² is already proved in the C3 source owner;
-- it is Galois/conjugation invariant.
mixedNormZeta :
  C3.norm (centreFingerprint phaseZeta directSymmetricSquare) ≡ 5292
mixedNormZeta = solve []

mixedNormZetaSquared :
  C3.norm (centreFingerprint phaseZetaSquared directSymmetricSquare) ≡ 5292
mixedNormZetaSquared = solve []

pureNormZeta :
  C3.norm (centreFingerprint phaseZeta dualSymmetricSquare) ≡ 8100
pureNormZeta = solve []

pureNormZetaSquared :
  C3.norm (centreFingerprint phaseZetaSquared dualSymmetricSquare) ≡ 8100
pureNormZetaSquared = solve []

-- A source-independent exact sign/kern obstruction is already owned
-- by the nine-cell D4 bridge; we route to that owner instead of
-- duplicating the central involution argument.
symmetricSquareCentralInvolutionPlus =
  Nine.faithfulCentralMinusSquaresToPlus

-- Also route to the already-identified historical quotient subgroup.
sameObjectPaidDiagonalKernel : Kernel.PaidMonsterDiagonalKernel
sameObjectPaidDiagonalKernel = Kernel.canonicalPaidMonsterDiagonalKernel

-- The quotient sign t1*t2^(+/-1) is not an additional semantic theorem:
-- inverted names are gauge-equivalent unless source coordinates fix t2.
-- NOTHING here identifies the actual selected 78 character or W_zeta.
