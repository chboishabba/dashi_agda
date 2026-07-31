module DASHI.Physics.YangMills.BalabanClayGate4BetaMonteCarloConventionAuditExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4BetaNormalizationConventionExact as Beta

------------------------------------------------------------------------
-- Empirical convention audit.
--
-- M. Nauenberg, T. Schalk, and R. Brower,
-- "Finite-size scaling and asymptotic freedom of the SU(2) lattice gauge
-- model", Physical Review D 24 (1981), 548--551.
-- DOI: 10.1103/PhysRevD.24.548.
--
-- The paper compares its fitted gamma_0 = 0.041 with the convention
-- gamma_0 = 11/(24 pi^2).  DASHI's inverse-coupling derivative coefficient is
-- 11 C_A/(24 pi^2); at C_A = 2 it is 11/(12 pi^2).  The rational theorem below
-- records the exact factor of two rather than incorrectly identifying the two
-- conventions.
------------------------------------------------------------------------

su2AdjointCasimir : ℚ
su2AdjointCasimir = + 2 / 1

nauenbergGammaRationalCoefficient : ℚ
nauenbergGammaRationalCoefficient = + 11 / 24

su2InverseCouplingRationalCoefficient : ℚ
su2InverseCouplingRationalCoefficient =
  Beta.pureYMInverseCouplingCoefficient su2AdjointCasimir

su2InverseCouplingCoefficientIsElevenOverTwelve :
  su2InverseCouplingRationalCoefficient ≡ + 11 / 12
su2InverseCouplingCoefficientIsElevenOverTwelve = ℚRing.solve-∀

twiceNauenbergGammaEqualsSU2InverseCouplingCoefficient :
  (+ 2 / 1) * nauenbergGammaRationalCoefficient
  ≡ su2InverseCouplingRationalCoefficient
twiceNauenbergGammaEqualsSU2InverseCouplingCoefficient = ℚRing.solve-∀

nauenbergGammaMetadataLevel : ProofLevel
nauenbergGammaMetadataLevel = standardImported

nauenbergGammaConventionFactorLevel : ProofLevel
nauenbergGammaConventionFactorLevel = machineChecked

nauenbergNumericalFitProvesBalabanLocalizedCoefficient : ProofLevel
nauenbergNumericalFitProvesBalabanLocalizedCoefficient = conjectural

physicalMonteCarloToInverseCouplingConventionMapInputsLevel : ProofLevel
physicalMonteCarloToInverseCouplingConventionMapInputsLevel = conditional
