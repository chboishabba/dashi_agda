module DASHI.Physics.YangMills.BalabanPath13GeneratedLDLCertificate where

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
-- PRIMARY SOURCES
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Exact rational LDL^T certificate for the mean-zero open path of length 13,
-- the minimal source-admissible CMP109 blocking side.  The independent
-- coordinates are y0,...,y11 and
--
--   y12 = -(y0+...+y11).
--
-- The generated certificate reconstructs exactly
--
--   E_13 - (1/18) ||y||^2 = sum_j d_j (ell_j y)^2
--
-- with twelve strictly positive rational pivots.  Since 1/18 is below the
-- true first nonzero Neumann path eigenvalue, this gives a source-scale local
-- Poincare floor without diagonalising a 342732-dimensional Gate-I matrix.
-- The generator is not trusted at theorem use: Agda's rational ring solver
-- checks the full twelve-variable polynomial identity.
------------------------------------------------------------------------

record Path13Coordinates : Set where
  constructor path13Coordinates
  field
    y0 : ℚ
    y1 : ℚ
    y2 : ℚ
    y3 : ℚ
    y4 : ℚ
    y5 : ℚ
    y6 : ℚ
    y7 : ℚ
    y8 : ℚ
    y9 : ℚ
    y10 : ℚ
    y11 : ℚ
open Path13Coordinates public

lastCoordinate : Path13Coordinates → ℚ
lastCoordinate coordinate =
  - (y0 coordinate + (y1 coordinate + (y2 coordinate + (y3 coordinate + (y4 coordinate + (y5 coordinate + (y6 coordinate + (y7 coordinate + (y8 coordinate + (y9 coordinate + (y10 coordinate + (y11 coordinate + (0ℚ)))))))))))))

path13NormSq : Path13Coordinates → ℚ
path13NormSq coordinate =
  sq (y0 coordinate) + (sq (y1 coordinate) + (sq (y2 coordinate) + (sq (y3 coordinate) + (sq (y4 coordinate) + (sq (y5 coordinate) + (sq (y6 coordinate) + (sq (y7 coordinate) + (sq (y8 coordinate) + (sq (y9 coordinate) + (sq (y10 coordinate) + (sq (y11 coordinate) + (sq (lastCoordinate coordinate) + (0ℚ)))))))))))))

path13Energy : Path13Coordinates → ℚ
path13Energy coordinate =
  sqDiff (y1 coordinate) (y0 coordinate) + (sqDiff (y2 coordinate) (y1 coordinate) + (sqDiff (y3 coordinate) (y2 coordinate) + (sqDiff (y4 coordinate) (y3 coordinate) + (sqDiff (y5 coordinate) (y4 coordinate) + (sqDiff (y6 coordinate) (y5 coordinate) + (sqDiff (y7 coordinate) (y6 coordinate) + (sqDiff (y8 coordinate) (y7 coordinate) + (sqDiff (y9 coordinate) (y8 coordinate) + (sqDiff (y10 coordinate) (y9 coordinate) + (sqDiff (y11 coordinate) (y10 coordinate) + (sqDiff (lastCoordinate coordinate) (y11 coordinate) + (0ℚ))))))))))))

oneEighteenth : ℚ
oneEighteenth = + 1 / 18

pivot0 : ℚ
pivot0 = + 17 / 9

pivot1 : ℚ
pivot1 = + 589 / 204

pivot2 : ℚ
pivot2 = + 38428 / 15903

pivot3 : ℚ
pivot3 = + 2736473 / 1383408

pivot4 : ℚ
pivot4 = + 14018033 / 8209419

pivot5 : ℚ
pivot5 = + 2319761419 / 1513947564

pivot6 : ℚ
pivot6 = + 29421908330 / 20877852771

pivot7 : ℚ
pivot7 = + 30988088209 / 23537526664

pivot8 : ℚ
pivot8 = + 820548843259 / 660535564455

pivot9 : ℚ
pivot9 = + 661887395501231 / 561255408789156

pivot10 : ℚ
pivot10 = + 2229938107229224 / 1985662186503693

pivot11 : ℚ
pivot11 = + 4514842591049713 / 240833315580756192

form0 : Path13Coordinates → ℚ
form0 coordinate =
  y0 coordinate + ((- (+ 1 / 34)) * y1 coordinate + ((+ 1 / 2) * y2 coordinate + ((+ 1 / 2) * y3 coordinate + ((+ 1 / 2) * y4 coordinate + ((+ 1 / 2) * y5 coordinate + ((+ 1 / 2) * y6 coordinate + ((+ 1 / 2) * y7 coordinate + ((+ 1 / 2) * y8 coordinate + ((+ 1 / 2) * y9 coordinate + ((+ 1 / 2) * y10 coordinate + ((+ 35 / 34) * y11 coordinate + (0ℚ))))))))))))

form1 : Path13Coordinates → ℚ
form1 coordinate =
  y1 coordinate + ((- (+ 17 / 1767)) * y2 coordinate + ((+ 595 / 1767) * y3 coordinate + ((+ 595 / 1767) * y4 coordinate + ((+ 595 / 1767) * y5 coordinate + ((+ 595 / 1767) * y6 coordinate + ((+ 595 / 1767) * y7 coordinate + ((+ 595 / 1767) * y8 coordinate + ((+ 595 / 1767) * y9 coordinate + ((+ 595 / 1767) * y10 coordinate + ((+ 1225 / 1767) * y11 coordinate + (0ℚ)))))))))))

form2 : Path13Coordinates → ℚ
form2 coordinate =
  y2 coordinate + ((- (+ 16489 / 76856)) * y3 coordinate + ((+ 15317 / 76856) * y4 coordinate + ((+ 15317 / 76856) * y5 coordinate + ((+ 15317 / 76856) * y6 coordinate + ((+ 15317 / 76856) * y7 coordinate + ((+ 15317 / 76856) * y8 coordinate + ((+ 15317 / 76856) * y9 coordinate + ((+ 15317 / 76856) * y10 coordinate + ((+ 31535 / 76856) * y11 coordinate + (0ℚ))))))))))

form3 : Path13Coordinates → ℚ
form3 coordinate =
  y3 coordinate + ((- (+ 1040093 / 2736473)) * y4 coordinate + ((+ 20195 / 160969) * y5 coordinate + ((+ 20195 / 160969) * y6 coordinate + ((+ 20195 / 160969) * y7 coordinate + ((+ 20195 / 160969) * y8 coordinate + ((+ 20195 / 160969) * y9 coordinate + ((+ 20195 / 160969) * y10 coordinate + ((+ 706825 / 2736473) * y11 coordinate + (0ℚ)))))))))

form4 : Path13Coordinates → ℚ
form4 coordinate =
  y4 coordinate + ((- (+ 42203197 / 84108198)) * y5 coordinate + ((+ 7053317 / 84108198) * y6 coordinate + ((+ 7053317 / 84108198) * y7 coordinate + ((+ 7053317 / 84108198) * y8 coordinate + ((+ 7053317 / 84108198) * y9 coordinate + ((+ 7053317 / 84108198) * y10 coordinate + ((+ 14521535 / 84108198) * y11 coordinate + (0ℚ))))))))

form5 : Path13Coordinates → ℚ
form5 coordinate =
  y5 coordinate + ((- (+ 1378315529 / 2319761419)) * y6 coordinate + ((+ 135632035 / 2319761419) * y7 coordinate + ((+ 135632035 / 2319761419) * y8 coordinate + ((+ 135632035 / 2319761419) * y9 coordinate + ((+ 135632035 / 2319761419) * y10 coordinate + ((+ 279242425 / 2319761419) * y11 coordinate + (0ℚ)))))))

form6 : Path13Coordinates → ℚ
form6 coordinate =
  y6 coordinate + ((- (+ 7858771805 / 11768763332)) * y7 coordinate + ((+ 144814501 / 3461400980) * y8 coordinate + ((+ 144814501 / 3461400980) * y9 coordinate + ((+ 144814501 / 3461400980) * y10 coordinate + ((+ 1013701507 / 11768763332) * y11 coordinate + (0ℚ))))))

form7 : Path13Coordinates → ℚ
form7 coordinate =
  y7 coordinate + ((- (+ 10704935275 / 14678568099)) * y8 coordinate + ((+ 8443969751 / 278892793881) * y9 coordinate + ((+ 8443969751 / 278892793881) * y10 coordinate + ((+ 17384643605 / 278892793881) * y11 coordinate + (0ℚ)))))

form8 : Path13Coordinates → ℚ
form8 coordinate =
  y8 coordinate + ((- (+ 1285278684967 / 1641097686518)) * y9 coordinate + ((+ 35792443943 / 1641097686518) * y10 coordinate + ((+ 73690325765 / 1641097686518) * y11 coordinate + (0ℚ))))

form9 : Path13Coordinates → ℚ
form9 coordinate =
  y9 coordinate + ((- (+ 551132664563681 / 661887395501231)) * y10 coordinate + ((+ 20840943993625 / 661887395501231) * y11 coordinate + (0ℚ)))

form10 : Path13Coordinates → ℚ
form10 coordinate =
  y10 coordinate + ((- (+ 11638177724654623 / 13379628643375344)) * y11 coordinate + (0ℚ))

form11 : Path13Coordinates → ℚ
form11 coordinate =
  y11 coordinate + (0ℚ)

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

path13Terms : List (LDLTerm Path13Coordinates)
path13Terms =
  ldlTerm pivot0 form0 (nonnegativeFraction 17 9)
  ∷ ldlTerm pivot1 form1 (nonnegativeFraction 589 204)
  ∷ ldlTerm pivot2 form2 (nonnegativeFraction 38428 15903)
  ∷ ldlTerm pivot3 form3 (nonnegativeFraction 2736473 1383408)
  ∷ ldlTerm pivot4 form4 (nonnegativeFraction 14018033 8209419)
  ∷ ldlTerm pivot5 form5 (nonnegativeFraction 2319761419 1513947564)
  ∷ ldlTerm pivot6 form6 (nonnegativeFraction 29421908330 20877852771)
  ∷ ldlTerm pivot7 form7 (nonnegativeFraction 30988088209 23537526664)
  ∷ ldlTerm pivot8 form8 (nonnegativeFraction 820548843259 660535564455)
  ∷ ldlTerm pivot9 form9 (nonnegativeFraction 661887395501231 561255408789156)
  ∷ ldlTerm pivot10 form10 (nonnegativeFraction 2229938107229224 1985662186503693)
  ∷ ldlTerm pivot11 form11 (nonnegativeFraction 4514842591049713 240833315580756192)
  ∷ []

path13LDLDecompositionRaw : ∀ a b c d e f g h i j k l →
  path13Energy (path13Coordinates a b c d e f g h i j k l)
  ≡ oneEighteenth * path13NormSq (path13Coordinates a b c d e f g h i j k l)
    + sumTermValues path13Terms (path13Coordinates a b c d e f g h i j k l)
path13LDLDecompositionRaw = ℚRing.solve-∀

path13LDLDecomposition : ∀ coordinate →
  path13Energy coordinate
  ≡ oneEighteenth * path13NormSq coordinate
    + sumTermValues path13Terms coordinate
path13LDLDecomposition (path13Coordinates a b c d e f g h i j k l) =
  path13LDLDecompositionRaw a b c d e f g h i j k l

path13LDLCertificate : RationalLDLCertificate Path13Coordinates
path13LDLCertificate = record
  { normSq = path13NormSq
  ; energy = path13Energy
  ; coercivityConstant = oneEighteenth
  ; terms = path13Terms
  ; decomposition = path13LDLDecomposition
  }

path13Poincare : ∀ coordinate →
  oneEighteenth * path13NormSq coordinate ≤ path13Energy coordinate
path13Poincare = ldlCertificatePoincare path13LDLCertificate

path13GeneratedLDLReconstructionLevel : ProofLevel
path13GeneratedLDLReconstructionLevel = machineChecked

path13GeneratedLDLConsumptionLevel : ProofLevel
path13GeneratedLDLConsumptionLevel = machineChecked