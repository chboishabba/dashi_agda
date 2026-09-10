module DASHI.Physics.YangMills.BalabanPath13GeneratedLDLCoefficientProofExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _-_; -_; _≤_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (sq; sqDiff; sumQ)
open import DASHI.Physics.YangMills.BalabanRationalLDLCertificate
open import DASHI.Physics.YangMills.BalabanPath13GeneratedLDLDataExact public
import DASHI.Physics.YangMills.BalabanQuadraticListExpansionExact as Expand

------------------------------------------------------------------------
-- Path-13 exact LDL reconstruction without a dense 12-variable square solve.
-- Long linear squares are expanded structurally first.  The final reflected
-- equality therefore performs coefficient collection on explicit monomials
-- rather than multiplying dense twelve-variable Horner trees.
------------------------------------------------------------------------

edgeTerms : ℚ → ℚ → List ℚ
edgeTerms x y = x ∷ (- y) ∷ []

edgeDifferenceAsSum : ∀ x y → x - y ≡ sumQ (edgeTerms x y)
edgeDifferenceAsSum = ℚRing.solve-∀

edgeSquareExpansion : ∀ x y →
  sqDiff x y ≡ Expand.squareExpansion (edgeTerms x y)
edgeSquareExpansion x y =
  trans (cong sq (edgeDifferenceAsSum x y))
        (Expand.squareSumExpansion (edgeTerms x y))

lastTerms : Path13Coordinates → List ℚ
lastTerms coordinate =
  (- y0 coordinate) ∷ (- y1 coordinate) ∷ (- y2 coordinate) ∷
  (- y3 coordinate) ∷ (- y4 coordinate) ∷ (- y5 coordinate) ∷
  (- y6 coordinate) ∷ (- y7 coordinate) ∷ (- y8 coordinate) ∷
  (- y9 coordinate) ∷ (- y10 coordinate) ∷ (- y11 coordinate) ∷ []

lastCoordinateAsTermSum : ∀ coordinate →
  lastCoordinate coordinate ≡ sumQ (lastTerms coordinate)
lastCoordinateAsTermSum (path13Coordinates a b c d e f g h i j k l) =
  ℚRing.solve-∀

lastSquareExpansion : ∀ coordinate →
  sq (lastCoordinate coordinate) ≡ Expand.squareExpansion (lastTerms coordinate)
lastSquareExpansion coordinate =
  trans (cong sq (lastCoordinateAsTermSum coordinate))
        (Expand.squareSumExpansion (lastTerms coordinate))

lastEdgeTerms : Path13Coordinates → List ℚ
lastEdgeTerms coordinate =
  (- y0 coordinate) ∷ (- y1 coordinate) ∷ (- y2 coordinate) ∷
  (- y3 coordinate) ∷ (- y4 coordinate) ∷ (- y5 coordinate) ∷
  (- y6 coordinate) ∷ (- y7 coordinate) ∷ (- y8 coordinate) ∷
  (- y9 coordinate) ∷ (- y10 coordinate) ∷ (- y11 coordinate) ∷
  (- y11 coordinate) ∷ []

lastEdgeDifferenceAsTermSum : ∀ coordinate →
  lastCoordinate coordinate - y11 coordinate ≡ sumQ (lastEdgeTerms coordinate)
lastEdgeDifferenceAsTermSum (path13Coordinates a b c d e f g h i j k l) =
  ℚRing.solve-∀

lastEdgeSquareExpansion : ∀ coordinate →
  sqDiff (lastCoordinate coordinate) (y11 coordinate)
  ≡ Expand.squareExpansion (lastEdgeTerms coordinate)
lastEdgeSquareExpansion coordinate =
  trans (cong sq (lastEdgeDifferenceAsTermSum coordinate))
        (Expand.squareSumExpansion (lastEdgeTerms coordinate))

expandedEnergy : Path13Coordinates → ℚ
expandedEnergy coordinate =
  Expand.squareExpansion (edgeTerms (y1 coordinate) (y0 coordinate)) +
  (Expand.squareExpansion (edgeTerms (y2 coordinate) (y1 coordinate)) +
  (Expand.squareExpansion (edgeTerms (y3 coordinate) (y2 coordinate)) +
  (Expand.squareExpansion (edgeTerms (y4 coordinate) (y3 coordinate)) +
  (Expand.squareExpansion (edgeTerms (y5 coordinate) (y4 coordinate)) +
  (Expand.squareExpansion (edgeTerms (y6 coordinate) (y5 coordinate)) +
  (Expand.squareExpansion (edgeTerms (y7 coordinate) (y6 coordinate)) +
  (Expand.squareExpansion (edgeTerms (y8 coordinate) (y7 coordinate)) +
  (Expand.squareExpansion (edgeTerms (y9 coordinate) (y8 coordinate)) +
  (Expand.squareExpansion (edgeTerms (y10 coordinate) (y9 coordinate)) +
  (Expand.squareExpansion (edgeTerms (y11 coordinate) (y10 coordinate)) +
   Expand.squareExpansion (lastEdgeTerms coordinate)))))))))))

path13EnergyExpanded : ∀ coordinate → path13Energy coordinate ≡ expandedEnergy coordinate
path13EnergyExpanded coordinate
  rewrite edgeSquareExpansion (y1 coordinate) (y0 coordinate)
        | edgeSquareExpansion (y2 coordinate) (y1 coordinate)
        | edgeSquareExpansion (y3 coordinate) (y2 coordinate)
        | edgeSquareExpansion (y4 coordinate) (y3 coordinate)
        | edgeSquareExpansion (y5 coordinate) (y4 coordinate)
        | edgeSquareExpansion (y6 coordinate) (y5 coordinate)
        | edgeSquareExpansion (y7 coordinate) (y6 coordinate)
        | edgeSquareExpansion (y8 coordinate) (y7 coordinate)
        | edgeSquareExpansion (y9 coordinate) (y8 coordinate)
        | edgeSquareExpansion (y10 coordinate) (y9 coordinate)
        | edgeSquareExpansion (y11 coordinate) (y10 coordinate)
        | lastEdgeSquareExpansion coordinate
  = refl

expandedNormSq : Path13Coordinates → ℚ
expandedNormSq coordinate =
  sq (y0 coordinate) + (sq (y1 coordinate) + (sq (y2 coordinate) +
  (sq (y3 coordinate) + (sq (y4 coordinate) + (sq (y5 coordinate) +
  (sq (y6 coordinate) + (sq (y7 coordinate) + (sq (y8 coordinate) +
  (sq (y9 coordinate) + (sq (y10 coordinate) + (sq (y11 coordinate) +
   Expand.squareExpansion (lastTerms coordinate))))))))))))

path13NormSqExpanded : ∀ coordinate → path13NormSq coordinate ≡ expandedNormSq coordinate
path13NormSqExpanded coordinate rewrite lastSquareExpansion coordinate = refl

form0Terms form1Terms form2Terms form3Terms form4Terms form5Terms :
  Path13Coordinates → List ℚ
form6Terms form7Terms form8Terms form9Terms form10Terms form11Terms :
  Path13Coordinates → List ℚ

form0Terms c = y0 c ∷ (- (+ 1 / 34)) * y1 c ∷ (+ 1 / 2) * y2 c ∷ (+ 1 / 2) * y3 c ∷ (+ 1 / 2) * y4 c ∷ (+ 1 / 2) * y5 c ∷ (+ 1 / 2) * y6 c ∷ (+ 1 / 2) * y7 c ∷ (+ 1 / 2) * y8 c ∷ (+ 1 / 2) * y9 c ∷ (+ 1 / 2) * y10 c ∷ (+ 35 / 34) * y11 c ∷ []
form1Terms c = y1 c ∷ (- (+ 17 / 1767)) * y2 c ∷ (+ 595 / 1767) * y3 c ∷ (+ 595 / 1767) * y4 c ∷ (+ 595 / 1767) * y5 c ∷ (+ 595 / 1767) * y6 c ∷ (+ 595 / 1767) * y7 c ∷ (+ 595 / 1767) * y8 c ∷ (+ 595 / 1767) * y9 c ∷ (+ 595 / 1767) * y10 c ∷ (+ 1225 / 1767) * y11 c ∷ []
form2Terms c = y2 c ∷ (- (+ 16489 / 76856)) * y3 c ∷ (+ 15317 / 76856) * y4 c ∷ (+ 15317 / 76856) * y5 c ∷ (+ 15317 / 76856) * y6 c ∷ (+ 15317 / 76856) * y7 c ∷ (+ 15317 / 76856) * y8 c ∷ (+ 15317 / 76856) * y9 c ∷ (+ 15317 / 76856) * y10 c ∷ (+ 31535 / 76856) * y11 c ∷ []
form3Terms c = y3 c ∷ (- (+ 1040093 / 2736473)) * y4 c ∷ (+ 20195 / 160969) * y5 c ∷ (+ 20195 / 160969) * y6 c ∷ (+ 20195 / 160969) * y7 c ∷ (+ 20195 / 160969) * y8 c ∷ (+ 20195 / 160969) * y9 c ∷ (+ 20195 / 160969) * y10 c ∷ (+ 706825 / 2736473) * y11 c ∷ []
form4Terms c = y4 c ∷ (- (+ 42203197 / 84108198)) * y5 c ∷ (+ 7053317 / 84108198) * y6 c ∷ (+ 7053317 / 84108198) * y7 c ∷ (+ 7053317 / 84108198) * y8 c ∷ (+ 7053317 / 84108198) * y9 c ∷ (+ 7053317 / 84108198) * y10 c ∷ (+ 14521535 / 84108198) * y11 c ∷ []
form5Terms c = y5 c ∷ (- (+ 1378315529 / 2319761419)) * y6 c ∷ (+ 135632035 / 2319761419) * y7 c ∷ (+ 135632035 / 2319761419) * y8 c ∷ (+ 135632035 / 2319761419) * y9 c ∷ (+ 135632035 / 2319761419) * y10 c ∷ (+ 279242425 / 2319761419) * y11 c ∷ []
form6Terms c = y6 c ∷ (- (+ 7858771805 / 11768763332)) * y7 c ∷ (+ 144814501 / 3461400980) * y8 c ∷ (+ 144814501 / 3461400980) * y9 c ∷ (+ 144814501 / 3461400980) * y10 c ∷ (+ 1013701507 / 11768763332) * y11 c ∷ []
form7Terms c = y7 c ∷ (- (+ 10704935275 / 14678568099)) * y8 c ∷ (+ 8443969751 / 278892793881) * y9 c ∷ (+ 8443969751 / 278892793881) * y10 c ∷ (+ 17384643605 / 278892793881) * y11 c ∷ []
form8Terms c = y8 c ∷ (- (+ 1285278684967 / 1641097686518)) * y9 c ∷ (+ 35792443943 / 1641097686518) * y10 c ∷ (+ 73690325765 / 1641097686518) * y11 c ∷ []
form9Terms c = y9 c ∷ (- (+ 551132664563681 / 661887395501231)) * y10 c ∷ (+ 20840943993625 / 661887395501231) * y11 c ∷ []
form10Terms c = y10 c ∷ (- (+ 11638177724654623 / 13379628643375344)) * y11 c ∷ []
form11Terms c = y11 c ∷ []

form0AsTermSum : ∀ c → form0 c ≡ sumQ (form0Terms c)
form1AsTermSum : ∀ c → form1 c ≡ sumQ (form1Terms c)
form2AsTermSum : ∀ c → form2 c ≡ sumQ (form2Terms c)
form3AsTermSum : ∀ c → form3 c ≡ sumQ (form3Terms c)
form4AsTermSum : ∀ c → form4 c ≡ sumQ (form4Terms c)
form5AsTermSum : ∀ c → form5 c ≡ sumQ (form5Terms c)
form6AsTermSum : ∀ c → form6 c ≡ sumQ (form6Terms c)
form7AsTermSum : ∀ c → form7 c ≡ sumQ (form7Terms c)
form8AsTermSum : ∀ c → form8 c ≡ sumQ (form8Terms c)
form9AsTermSum : ∀ c → form9 c ≡ sumQ (form9Terms c)
form10AsTermSum : ∀ c → form10 c ≡ sumQ (form10Terms c)
form11AsTermSum : ∀ c → form11 c ≡ sumQ (form11Terms c)
form0AsTermSum (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
form1AsTermSum (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
form2AsTermSum (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
form3AsTermSum (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
form4AsTermSum (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
form5AsTermSum (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
form6AsTermSum (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
form7AsTermSum (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
form8AsTermSum (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
form9AsTermSum (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
form10AsTermSum (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
form11AsTermSum (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀

form0SquareExpansion form1SquareExpansion form2SquareExpansion : ∀ c → ℚ
form0SquareExpansion c = Expand.squareExpansion (form0Terms c)
form1SquareExpansion c = Expand.squareExpansion (form1Terms c)
form2SquareExpansion c = Expand.squareExpansion (form2Terms c)

formSquare0 : ∀ c → sq (form0 c) ≡ Expand.squareExpansion (form0Terms c)
formSquare1 : ∀ c → sq (form1 c) ≡ Expand.squareExpansion (form1Terms c)
formSquare2 : ∀ c → sq (form2 c) ≡ Expand.squareExpansion (form2Terms c)
formSquare3 : ∀ c → sq (form3 c) ≡ Expand.squareExpansion (form3Terms c)
formSquare4 : ∀ c → sq (form4 c) ≡ Expand.squareExpansion (form4Terms c)
formSquare5 : ∀ c → sq (form5 c) ≡ Expand.squareExpansion (form5Terms c)
formSquare6 : ∀ c → sq (form6 c) ≡ Expand.squareExpansion (form6Terms c)
formSquare7 : ∀ c → sq (form7 c) ≡ Expand.squareExpansion (form7Terms c)
formSquare8 : ∀ c → sq (form8 c) ≡ Expand.squareExpansion (form8Terms c)
formSquare9 : ∀ c → sq (form9 c) ≡ Expand.squareExpansion (form9Terms c)
formSquare10 : ∀ c → sq (form10 c) ≡ Expand.squareExpansion (form10Terms c)
formSquare11 : ∀ c → sq (form11 c) ≡ Expand.squareExpansion (form11Terms c)
formSquare0 c = trans (cong sq (form0AsTermSum c)) (Expand.squareSumExpansion (form0Terms c))
formSquare1 c = trans (cong sq (form1AsTermSum c)) (Expand.squareSumExpansion (form1Terms c))
formSquare2 c = trans (cong sq (form2AsTermSum c)) (Expand.squareSumExpansion (form2Terms c))
formSquare3 c = trans (cong sq (form3AsTermSum c)) (Expand.squareSumExpansion (form3Terms c))
formSquare4 c = trans (cong sq (form4AsTermSum c)) (Expand.squareSumExpansion (form4Terms c))
formSquare5 c = trans (cong sq (form5AsTermSum c)) (Expand.squareSumExpansion (form5Terms c))
formSquare6 c = trans (cong sq (form6AsTermSum c)) (Expand.squareSumExpansion (form6Terms c))
formSquare7 c = trans (cong sq (form7AsTermSum c)) (Expand.squareSumExpansion (form7Terms c))
formSquare8 c = trans (cong sq (form8AsTermSum c)) (Expand.squareSumExpansion (form8Terms c))
formSquare9 c = trans (cong sq (form9AsTermSum c)) (Expand.squareSumExpansion (form9Terms c))
formSquare10 c = trans (cong sq (form10AsTermSum c)) (Expand.squareSumExpansion (form10Terms c))
formSquare11 c = trans (cong sq (form11AsTermSum c)) (Expand.squareSumExpansion (form11Terms c))

expandedLDL : Path13Coordinates → ℚ
expandedLDL c =
  pivot0 * Expand.squareExpansion (form0Terms c) +
  (pivot1 * Expand.squareExpansion (form1Terms c) +
  (pivot2 * Expand.squareExpansion (form2Terms c) +
  (pivot3 * Expand.squareExpansion (form3Terms c) +
  (pivot4 * Expand.squareExpansion (form4Terms c) +
  (pivot5 * Expand.squareExpansion (form5Terms c) +
  (pivot6 * Expand.squareExpansion (form6Terms c) +
  (pivot7 * Expand.squareExpansion (form7Terms c) +
  (pivot8 * Expand.squareExpansion (form8Terms c) +
  (pivot9 * Expand.squareExpansion (form9Terms c) +
  (pivot10 * Expand.squareExpansion (form10Terms c) +
  (pivot11 * Expand.squareExpansion (form11Terms c) + 0ℚ))))))))))))

expandedLDLMatchesTerms : ∀ c → expandedLDL c ≡ sumTermValues path13Terms c
expandedLDLMatchesTerms c
  rewrite formSquare0 c | formSquare1 c | formSquare2 c | formSquare3 c
        | formSquare4 c | formSquare5 c | formSquare6 c | formSquare7 c
        | formSquare8 c | formSquare9 c | formSquare10 c | formSquare11 c
  = refl

expandedGap : Path13Coordinates → ℚ
expandedGap c = expandedEnergy c - oneEighteenth * expandedNormSq c

path13GapExpanded : ∀ c →
  path13Energy c - oneEighteenth * path13NormSq c ≡ expandedGap c
path13GapExpanded c rewrite path13EnergyExpanded c | path13NormSqExpanded c = refl

expandedCoefficientEqualityRaw : ∀ a b c d e f g h i j k l →
  expandedGap (path13Coordinates a b c d e f g h i j k l)
  ≡ expandedLDL (path13Coordinates a b c d e f g h i j k l)
expandedCoefficientEqualityRaw = ℚRing.solve-∀

expandedCoefficientEquality : ∀ c → expandedGap c ≡ expandedLDL c
expandedCoefficientEquality (path13Coordinates a b c d e f g h i j k l) =
  expandedCoefficientEqualityRaw a b c d e f g h i j k l

path13GapToTerms : ∀ c →
  path13Energy c - oneEighteenth * path13NormSq c ≡ sumTermValues path13Terms c
path13GapToTerms c =
  trans (path13GapExpanded c)
    (trans (expandedCoefficientEquality c) (expandedLDLMatchesTerms c))

recomposeIdentity : ∀ energyValue normValue constant →
  energyValue ≡ constant * normValue + (energyValue - constant * normValue)
recomposeIdentity = ℚRing.solve-∀

path13LDLDecomposition : ∀ c →
  path13Energy c ≡ oneEighteenth * path13NormSq c + sumTermValues path13Terms c
path13LDLDecomposition c =
  trans
    (recomposeIdentity (path13Energy c) (path13NormSq c) oneEighteenth)
    (cong (λ remainder → oneEighteenth * path13NormSq c + remainder)
          (path13GapToTerms c))

path13LDLCertificate : RationalLDLCertificate Path13Coordinates
path13LDLCertificate = record
  { normSq = path13NormSq
  ; energy = path13Energy
  ; coercivityConstant = oneEighteenth
  ; terms = path13Terms
  ; decomposition = path13LDLDecomposition
  }

path13Poincare : ∀ c → oneEighteenth * path13NormSq c ≤ path13Energy c
path13Poincare = ldlCertificatePoincare path13LDLCertificate

path13ExpandedCoefficientReconstructionLevel : ProofLevel
path13ExpandedCoefficientReconstructionLevel = machineChecked

path13GeneratedLDLConsumptionLevel : ProofLevel
path13GeneratedLDLConsumptionLevel = machineChecked
