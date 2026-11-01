module DASHI.Physics.YangMills.BalabanPath13SelectedNormalInverseArithmeticExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- DASHI CONTRIBUTION
--
-- Expose the exact reciprocal of the selected source-scale combined normal
-- floor.  The previously proved coercivity constant is
--
--   gamma_13 = 130991 / 3145728.
--
-- Its exact reciprocal is
--
--   gamma_13^-1 = 3145728 / 130991.
--
-- Keeping this number named avoids repeatedly falling back to the legacy
-- 1024/29 side-four inverse constant when estimating source-scale Newton and
-- tangent corrections.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPath13PreconditionedSelectedCombinedFloorExact as Floor

selectedCombinedNormalInverseCoefficient13 : ℚ
selectedCombinedNormalInverseCoefficient13 = + 3145728 / 130991

selectedCombinedFloorTimesInverseExact :
  Floor.selectedCombinedFloor13 * selectedCombinedNormalInverseCoefficient13
  ≡ 1ℚ
selectedCombinedFloorTimesInverseExact = ℚRing.solve []

selectedCombinedInverseTimesFloorExact :
  selectedCombinedNormalInverseCoefficient13 * Floor.selectedCombinedFloor13
  ≡ 1ℚ
selectedCombinedInverseTimesFloorExact = ℚRing.solve []

path13SelectedCombinedNormalInverseArithmeticLevel : ProofLevel
path13SelectedCombinedNormalInverseArithmeticLevel = machineChecked
