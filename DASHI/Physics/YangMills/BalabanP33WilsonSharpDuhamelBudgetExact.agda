module DASHI.Physics.YangMills.BalabanP33WilsonSharpDuhamelBudgetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- The previous conservative diagonal allocation used the admissible but loose
-- constant 6 and spent rho/4 across four D^2 exp atoms.  The ordered-simplex
-- telescope has scalar constant 1, so once the physical Duhamel identification
-- is supplied the four diagonal atoms spend only rho/24.  Together with the
-- already literal 48-occurrence cross budget rho/2, all sixteen Wilson atoms
-- spend 13 rho/24 and retain 11 rho/24 of Wilson slack.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel

rho : ℚ
rho = + 1 / 8192

crossBudget : ℚ
crossBudget = rho * (+ 1 / 2)

sharpDiagonalBudget : ℚ
sharpDiagonalBudget = rho * (+ 1 / 24)

sharpSixteenAtomBudget : ℚ
sharpSixteenAtomBudget = crossBudget + sharpDiagonalBudget

sharpSixteenAtomBudgetExact :
  sharpSixteenAtomBudget ≡ rho * (+ 13 / 24)
sharpSixteenAtomBudgetExact = ℚRing.solve []

sharpWilsonSlack : ℚ
sharpWilsonSlack = rho * (+ 11 / 24)

sharpBudgetPlusSlackIsRadius :
  sharpSixteenAtomBudget + sharpWilsonSlack ≡ rho
sharpBudgetPlusSlackIsRadius = ℚRing.solve []

conservativeDiagonalBudget : ℚ
conservativeDiagonalBudget = rho * (+ 1 / 4)

releasedDiagonalSlack : ℚ
releasedDiagonalSlack = conservativeDiagonalBudget - sharpDiagonalBudget

releasedDiagonalSlackExact :
  releasedDiagonalSlack ≡ rho * (+ 5 / 24)
releasedDiagonalSlackExact = ℚRing.solve []

sharpWilsonSixteenAtomArithmeticLevel : ProofLevel
sharpWilsonSixteenAtomArithmeticLevel = machineChecked

physicalSharpDuhamelWilsonIdentificationLevel : ProofLevel
physicalSharpDuhamelWilsonIdentificationLevel = conditional
