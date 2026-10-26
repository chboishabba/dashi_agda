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

-- A partial inverse on all 27 native points. Failure occurs only
-- at the global origin. This preserves the absent-site residual.
open import Agda.Builtin.Maybe using (Maybe; just; nothing)

fromCube : Cube.Ternary27Point → Maybe Punctured27Chart
fromCube (Cube.ternary27Point x y SSP.sspNegOne) =
  just (lowerSheet x y)
fromCube (Cube.ternary27Point x y SSP.sspPosOne) =
  just (upperSheet x y)
fromCube (Cube.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspZero) = just (middleNonzero P9.negativeEqualDiagonal)
fromCube (Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero) = just (middleNonzero P9.negativeFirstAxis)
fromCube (Cube.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspZero) = just (middleNonzero P9.negativeOppositeDiagonal)
fromCube (Cube.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspZero) = just (middleNonzero P9.negativeSecondAxis)
fromCube (Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspZero) = nothing
fromCube (Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero) = just (middleNonzero P9.positiveSecondAxis)
fromCube (Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspZero) = just (middleNonzero P9.positiveOppositeDiagonal)
fromCube (Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero) = just (middleNonzero P9.positiveFirstAxis)
fromCube (Cube.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspZero) = just (middleNonzero P9.positiveEqualDiagonal)

fromToCube : (p : Punctured27Chart) →
  fromCube (toCube p) ≡ just p
fromToCube (middleNonzero P9.negativeEqualDiagonal) = refl
fromToCube (middleNonzero P9.negativeFirstAxis) = refl
fromToCube (middleNonzero P9.negativeOppositeDiagonal) = refl
fromToCube (middleNonzero P9.negativeSecondAxis) = refl
fromToCube (middleNonzero P9.positiveSecondAxis) = refl
fromToCube (middleNonzero P9.positiveOppositeDiagonal) = refl
fromToCube (middleNonzero P9.positiveFirstAxis) = refl
fromToCube (middleNonzero P9.positiveEqualDiagonal) = refl
fromToCube (lowerSheet x y) = refl
fromToCube (upperSheet x y) = refl

originExcluded : fromCube Cube.origin ≡ nothing
originExcluded = refl

-- Right inverse, conditional on a successfully decoded punctured point.
-- Unlike a total 27-point inverse, this preserves the global missing site.
toFromCube :
  (p : Cube.Ternary27Point) (c : Punctured27Chart) →
  fromCube p ≡ just c → toCube c ≡ p
toFromCube (Cube.ternary27Point x y SSP.sspNegOne) c refl = refl
toFromCube (Cube.ternary27Point x y SSP.sspPosOne) c refl = refl
toFromCube (Cube.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspZero) c refl = refl
toFromCube (Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero) c refl = refl
toFromCube (Cube.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspZero) c refl = refl
toFromCube (Cube.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspZero) c refl = refl
toFromCube (Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspZero) c ()
toFromCube (Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero) c refl = refl
toFromCube (Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspZero) c refl = refl
toFromCube (Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero) c refl = refl
toFromCube (Cube.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspZero) c refl = refl
