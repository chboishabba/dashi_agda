module DASHI.Mathematics.Symmetry.Punctured27NineSheetBridgeExact where

-- Imports the exact original 27 cube and punctured-nine owner.
-- Puncturing the entire cube removes only the central sheet's origin;
-- it does NOT puncture the two outer nine-sheets.
-- Classical finite decomposition; no claim of a topological puncture
-- equivalence or physical lattice gluing.
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Moonshine.OggSSPP2BalancedTernaryPuncturedPlaneExact as P9

data Punctured27Chart : Set where
  middleNonzero : P9.PuncturedNineSheet → Punctured27Chart
  lowerSheet : SSP.SSPTrit → SSP.SSPTrit → Punctured27Chart
  upperSheet : SSP.SSPTrit → SSP.SSPTrit → Punctured27Chart

toCube : Punctured27Chart → Cube.Ternary27Point
toCube (middleNonzero P9.negativeFirstAxis) =
  Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero
toCube (middleNonzero P9.positiveFirstAxis) =
  Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero
toCube (middleNonzero P9.negativeSecondAxis) =
  Cube.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspZero
toCube (middleNonzero P9.positiveSecondAxis) =
  Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero
toCube (middleNonzero P9.negativeEqualDiagonal) =
  Cube.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspZero
toCube (middleNonzero P9.positiveEqualDiagonal) =
  Cube.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspZero
toCube (middleNonzero P9.negativeOppositeDiagonal) =
  Cube.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspZero
toCube (middleNonzero P9.positiveOppositeDiagonal) =
  Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspZero
toCube (lowerSheet x y) =
  Cube.ternary27Point x y SSP.sspNegOne
toCube (upperSheet x y) =
  Cube.ternary27Point x y SSP.sspPosOne

-- A finite sum with 8 + 9 + 9 = 26 points; converse requires
-- excluding exactly Cube.origin and case-splitting the middle sheet.
-- The six outer-centre signs / antipodal seam relations must not
-- be identified by a zero-stalk collapse.
