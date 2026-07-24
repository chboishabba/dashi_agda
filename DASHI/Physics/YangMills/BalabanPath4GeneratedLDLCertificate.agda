module DASHI.Physics.YangMills.BalabanPath4GeneratedLDLCertificate where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Rational using
  (ℚ; 0ℚ; _+_; _*_; -_; _≤_; _/_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (sq; sqDiff)
open import DASHI.Physics.YangMills.BalabanRationalLDLCertificate

------------------------------------------------------------------------
-- Generated exact LDL^T certificate for the mean-zero path P4.
--
-- The independent coordinates represent
--
--   f = (y0 , y1 , y2 , -(y0 + y1 + y2)).
--
-- The generator decomposes
--
--   E(f) - (1/16) ||f||^2 = L D L^T
--
-- with the three positive pivots below.  The polynomial reconstruction is
-- checked by the rational ring solver and consumed by the generic LDL theorem.
------------------------------------------------------------------------

record Path4Coordinates : Set where
  constructor path4Coordinates
  field
    y0 y1 y2 : ℚ

open Path4Coordinates public

lastCoordinate : Path4Coordinates → ℚ
lastCoordinate coordinate =
  - (y0 coordinate + (y1 coordinate + y2 coordinate))

path4NormSq : Path4Coordinates → ℚ
path4NormSq coordinate =
  sq (y0 coordinate)
  + (sq (y1 coordinate)
  + (sq (y2 coordinate) + sq (lastCoordinate coordinate)))

path4Energy : Path4Coordinates → ℚ
path4Energy coordinate =
  sqDiff (y1 coordinate) (y0 coordinate)
  + (sqDiff (y2 coordinate) (y1 coordinate)
  + sqDiff (lastCoordinate coordinate) (y2 coordinate))

oneSixteenth : ℚ
oneSixteenth = + 1 / 16

pivot0 pivot1 pivot2 : ℚ
pivot0 = + 15 / 8
pivot1 = + 1379 / 480
pivot2 = + 13919 / 5516

minusOneThirtieth thirtyOneThirtieth fourHundredEightyOneOver1379 : ℚ
minusOneThirtieth = - (+ 1 / 30)
thirtyOneThirtieth = + 31 / 30
fourHundredEightyOneOver1379 = + 481 / 1379

form0 form1 form2 : Path4Coordinates → ℚ
form0 coordinate =
  y0 coordinate
  + (minusOneThirtieth * y1 coordinate
  + thirtyOneThirtieth * y2 coordinate)
form1 coordinate =
  y1 coordinate + fourHundredEightyOneOver1379 * y2 coordinate
form2 coordinate = y2 coordinate

nonnegativeFraction :
  ∀ (numerator denominator : ℕ) {{_ : ℕ.NonZero denominator}} →
  0ℚ ≤ (+ numerator / denominator)
nonnegativeFraction numerator denominator =
  let
    instance
      fractionNonnegative : NonNegative (+ numerator / denominator)
      fractionNonnegative = ℚP.normalize-nonNeg numerator denominator
  in
  ℚP.nonNegative⁻¹ (+ numerator / denominator)

path4Terms : List (LDLTerm Path4Coordinates)
path4Terms =
  ldlTerm pivot0 form0 (nonnegativeFraction 15 8)
  ∷ ldlTerm pivot1 form1 (nonnegativeFraction 1379 480)
  ∷ ldlTerm pivot2 form2 (nonnegativeFraction 13919 5516)
  ∷ []

path4LDLDecompositionRaw : ∀ a b c →
  path4Energy (path4Coordinates a b c)
  ≡ oneSixteenth * path4NormSq (path4Coordinates a b c)
    + sumTermValues path4Terms (path4Coordinates a b c)
path4LDLDecompositionRaw = ℚRing.solve-∀

path4LDLDecomposition : ∀ coordinate →
  path4Energy coordinate
  ≡ oneSixteenth * path4NormSq coordinate
    + sumTermValues path4Terms coordinate
path4LDLDecomposition (path4Coordinates a b c) =
  path4LDLDecompositionRaw a b c

path4LDLCertificate : RationalLDLCertificate Path4Coordinates
path4LDLCertificate = record
  { normSq = path4NormSq
  ; energy = path4Energy
  ; coercivityConstant = oneSixteenth
  ; terms = path4Terms
  ; decomposition = path4LDLDecomposition
  }

path4Poincare : ∀ coordinate →
  oneSixteenth * path4NormSq coordinate ≤ path4Energy coordinate
path4Poincare = ldlCertificatePoincare path4LDLCertificate

path4GeneratedLDLReconstructionLevel : ProofLevel
path4GeneratedLDLReconstructionLevel = computed

path4GeneratedLDLConsumptionLevel : ProofLevel
path4GeneratedLDLConsumptionLevel = machineChecked
