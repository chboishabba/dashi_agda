module DASHI.Physics.YangMills.BalabanPath13GeneratedLDLCoefficientProofExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _-_; -_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq; sqDiff)
open import DASHI.Physics.YangMills.BalabanRationalLDLCertificate
open import DASHI.Physics.YangMills.BalabanPath13QuadraticCoefficientDataExact public
import DASHI.Physics.YangMills.BalabanTriangularQuadraticCertificateExact as Quad

------------------------------------------------------------------------
-- Literal linear carriers.
--
-- These are the only Path13 reflection calls that see all twelve coordinates.
-- They are linear equalities only; no square or quadratic polynomial is sent
-- to the ring solver.
------------------------------------------------------------------------

energyLinear0 : ∀ c → Quad.dot energy0Coefficients (coordinates c) ≡ y1 c - y0 c
energyLinear0 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
energyLinear1 : ∀ c → Quad.dot energy1Coefficients (coordinates c) ≡ y2 c - y1 c
energyLinear1 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
energyLinear2 : ∀ c → Quad.dot energy2Coefficients (coordinates c) ≡ y3 c - y2 c
energyLinear2 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
energyLinear3 : ∀ c → Quad.dot energy3Coefficients (coordinates c) ≡ y4 c - y3 c
energyLinear3 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
energyLinear4 : ∀ c → Quad.dot energy4Coefficients (coordinates c) ≡ y5 c - y4 c
energyLinear4 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
energyLinear5 : ∀ c → Quad.dot energy5Coefficients (coordinates c) ≡ y6 c - y5 c
energyLinear5 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
energyLinear6 : ∀ c → Quad.dot energy6Coefficients (coordinates c) ≡ y7 c - y6 c
energyLinear6 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
energyLinear7 : ∀ c → Quad.dot energy7Coefficients (coordinates c) ≡ y8 c - y7 c
energyLinear7 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
energyLinear8 : ∀ c → Quad.dot energy8Coefficients (coordinates c) ≡ y9 c - y8 c
energyLinear8 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
energyLinear9 : ∀ c → Quad.dot energy9Coefficients (coordinates c) ≡ y10 c - y9 c
energyLinear9 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
energyLinear10 : ∀ c → Quad.dot energy10Coefficients (coordinates c) ≡ y11 c - y10 c
energyLinear10 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
energyLinear11 : ∀ c → Quad.dot energy11Coefficients (coordinates c) ≡ lastCoordinate c - y11 c
energyLinear11 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀

normLinear0 : ∀ c → Quad.dot norm0Coefficients (coordinates c) ≡ y0 c
normLinear0 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
normLinear1 : ∀ c → Quad.dot norm1Coefficients (coordinates c) ≡ y1 c
normLinear1 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
normLinear2 : ∀ c → Quad.dot norm2Coefficients (coordinates c) ≡ y2 c
normLinear2 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
normLinear3 : ∀ c → Quad.dot norm3Coefficients (coordinates c) ≡ y3 c
normLinear3 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
normLinear4 : ∀ c → Quad.dot norm4Coefficients (coordinates c) ≡ y4 c
normLinear4 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
normLinear5 : ∀ c → Quad.dot norm5Coefficients (coordinates c) ≡ y5 c
normLinear5 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
normLinear6 : ∀ c → Quad.dot norm6Coefficients (coordinates c) ≡ y6 c
normLinear6 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
normLinear7 : ∀ c → Quad.dot norm7Coefficients (coordinates c) ≡ y7 c
normLinear7 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
normLinear8 : ∀ c → Quad.dot norm8Coefficients (coordinates c) ≡ y8 c
normLinear8 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
normLinear9 : ∀ c → Quad.dot norm9Coefficients (coordinates c) ≡ y9 c
normLinear9 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
normLinear10 : ∀ c → Quad.dot norm10Coefficients (coordinates c) ≡ y10 c
normLinear10 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
normLinear11 : ∀ c → Quad.dot norm11Coefficients (coordinates c) ≡ y11 c
normLinear11 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
normLinear12 : ∀ c → Quad.dot norm12Coefficients (coordinates c) ≡ lastCoordinate c
normLinear12 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀

formLinear0 : ∀ c → Quad.dot form0Coefficients (coordinates c) ≡ form0 c
formLinear0 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
formLinear1 : ∀ c → Quad.dot form1Coefficients (coordinates c) ≡ form1 c
formLinear1 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
formLinear2 : ∀ c → Quad.dot form2Coefficients (coordinates c) ≡ form2 c
formLinear2 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
formLinear3 : ∀ c → Quad.dot form3Coefficients (coordinates c) ≡ form3 c
formLinear3 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
formLinear4 : ∀ c → Quad.dot form4Coefficients (coordinates c) ≡ form4 c
formLinear4 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
formLinear5 : ∀ c → Quad.dot form5Coefficients (coordinates c) ≡ form5 c
formLinear5 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
formLinear6 : ∀ c → Quad.dot form6Coefficients (coordinates c) ≡ form6 c
formLinear6 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
formLinear7 : ∀ c → Quad.dot form7Coefficients (coordinates c) ≡ form7 c
formLinear7 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
formLinear8 : ∀ c → Quad.dot form8Coefficients (coordinates c) ≡ form8 c
formLinear8 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
formLinear9 : ∀ c → Quad.dot form9Coefficients (coordinates c) ≡ form9 c
formLinear9 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
formLinear10 : ∀ c → Quad.dot form10Coefficients (coordinates c) ≡ form10 c
formLinear10 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
formLinear11 : ∀ c → Quad.dot form11Coefficients (coordinates c) ≡ form11 c
formLinear11 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀

------------------------------------------------------------------------
-- Structural compiler attachments.
------------------------------------------------------------------------

dropTrailingZero12 : ∀ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 →
  v0 + (v1 + (v2 + (v3 + (v4 + (v5 + (v6 + (v7 + (v8 + (v9 + (v10 + (v11 + 0ℚ)))))))))))
  ≡ v0 + (v1 + (v2 + (v3 + (v4 + (v5 + (v6 + (v7 + (v8 + (v9 + (v10 + v11))))))))))
dropTrailingZero12 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  rewrite ℚP.+-identityʳ v11 = refl

dropTrailingZero13 : ∀ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 →
  v0 + (v1 + (v2 + (v3 + (v4 + (v5 + (v6 + (v7 + (v8 + (v9 + (v10 + (v11 + (v12 + 0ℚ))))))))))))
  ≡ v0 + (v1 + (v2 + (v3 + (v4 + (v5 + (v6 + (v7 + (v8 + (v9 + (v10 + (v11 + v12)))))))))))
dropTrailingZero13 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  rewrite ℚP.+-identityʳ v12 = refl

energyValuesMatch : ∀ c → Quad.sumSquareValues energyFamilies (coordinates c) ≡ path13Energy c
energyValuesMatch c
  rewrite energyLinear0 c | energyLinear1 c | energyLinear2 c | energyLinear3 c
        | energyLinear4 c | energyLinear5 c | energyLinear6 c | energyLinear7 c
        | energyLinear8 c | energyLinear9 c | energyLinear10 c | energyLinear11 c
  = dropTrailingZero12
      (sqDiff (y1 c) (y0 c)) (sqDiff (y2 c) (y1 c))
      (sqDiff (y3 c) (y2 c)) (sqDiff (y4 c) (y3 c))
      (sqDiff (y5 c) (y4 c)) (sqDiff (y6 c) (y5 c))
      (sqDiff (y7 c) (y6 c)) (sqDiff (y8 c) (y7 c))
      (sqDiff (y9 c) (y8 c)) (sqDiff (y10 c) (y9 c))
      (sqDiff (y11 c) (y10 c)) (sqDiff (lastCoordinate c) (y11 c))

normValuesMatch : ∀ c → Quad.sumSquareValues normFamilies (coordinates c) ≡ path13NormSq c
normValuesMatch c
  rewrite normLinear0 c | normLinear1 c | normLinear2 c | normLinear3 c
        | normLinear4 c | normLinear5 c | normLinear6 c | normLinear7 c
        | normLinear8 c | normLinear9 c | normLinear10 c | normLinear11 c
        | normLinear12 c
  = dropTrailingZero13
      (sq (y0 c)) (sq (y1 c)) (sq (y2 c)) (sq (y3 c)) (sq (y4 c))
      (sq (y5 c)) (sq (y6 c)) (sq (y7 c)) (sq (y8 c)) (sq (y9 c))
      (sq (y10 c)) (sq (y11 c)) (sq (lastCoordinate c))

ldlValuesMatch : ∀ c →
  Quad.sumWeightedSquareValues ldlFamilies (coordinates c)
  ≡ sumTermValues path13Terms c
ldlValuesMatch c
  rewrite formLinear0 c | formLinear1 c | formLinear2 c | formLinear3 c
        | formLinear4 c | formLinear5 c | formLinear6 c | formLinear7 c
        | formLinear8 c | formLinear9 c | formLinear10 c | formLinear11 c
  = refl

------------------------------------------------------------------------
-- Closed 78-coefficient payment, split into twelve triangular rows.
--
-- `gapTri` and `ldlTri` are computed only from closed rational coefficient
-- lists.  The row checks below contain no Path13 variables and no reflection.
-- A failing coefficient therefore localises to one finite row instead of
-- constructing a 1000-term symbolic polynomial AST.
------------------------------------------------------------------------

diagOf : Quad.TriQuadratic → ℚ
diagOf Quad.qnil = 0ℚ
diagOf (Quad.qcons diagonal row tail) = diagonal

rowOf : Quad.TriQuadratic → List ℚ
rowOf Quad.qnil = []
rowOf (Quad.qcons diagonal row tail) = row

tailOf : Quad.TriQuadratic → Quad.TriQuadratic
tailOf Quad.qnil = Quad.qnil
tailOf (Quad.qcons diagonal row tail) = tail

gapTail0 gapTail1 gapTail2 gapTail3 gapTail4 gapTail5 gapTail6 : Quad.TriQuadratic
gapTail7 gapTail8 gapTail9 gapTail10 gapTail11 gapTail12 : Quad.TriQuadratic
gapTail0 = gapTri
gapTail1 = tailOf gapTail0
gapTail2 = tailOf gapTail1
gapTail3 = tailOf gapTail2
gapTail4 = tailOf gapTail3
gapTail5 = tailOf gapTail4
gapTail6 = tailOf gapTail5
gapTail7 = tailOf gapTail6
gapTail8 = tailOf gapTail7
gapTail9 = tailOf gapTail8
gapTail10 = tailOf gapTail9
gapTail11 = tailOf gapTail10
gapTail12 = tailOf gapTail11

ldlTail0 ldlTail1 ldlTail2 ldlTail3 ldlTail4 ldlTail5 ldlTail6 : Quad.TriQuadratic
ldlTail7 ldlTail8 ldlTail9 ldlTail10 ldlTail11 ldlTail12 : Quad.TriQuadratic
ldlTail0 = ldlTri
ldlTail1 = tailOf ldlTail0
ldlTail2 = tailOf ldlTail1
ldlTail3 = tailOf ldlTail2
ldlTail4 = tailOf ldlTail3
ldlTail5 = tailOf ldlTail4
ldlTail6 = tailOf ldlTail5
ldlTail7 = tailOf ldlTail6
ldlTail8 = tailOf ldlTail7
ldlTail9 = tailOf ldlTail8
ldlTail10 = tailOf ldlTail9
ldlTail11 = tailOf ldlTail10
ldlTail12 = tailOf ldlTail11

row0Diag : diagOf gapTail0 ≡ diagOf ldlTail0
row0Diag = refl
row0Off : rowOf gapTail0 ≡ rowOf ldlTail0
row0Off = refl
row1Diag : diagOf gapTail1 ≡ diagOf ldlTail1
row1Diag = refl
row1Off : rowOf gapTail1 ≡ rowOf ldlTail1
row1Off = refl
row2Diag : diagOf gapTail2 ≡ diagOf ldlTail2
row2Diag = refl
row2Off : rowOf gapTail2 ≡ rowOf ldlTail2
row2Off = refl
row3Diag : diagOf gapTail3 ≡ diagOf ldlTail3
row3Diag = refl
row3Off : rowOf gapTail3 ≡ rowOf ldlTail3
row3Off = refl
row4Diag : diagOf gapTail4 ≡ diagOf ldlTail4
row4Diag = refl
row4Off : rowOf gapTail4 ≡ rowOf ldlTail4
row4Off = refl
row5Diag : diagOf gapTail5 ≡ diagOf ldlTail5
row5Diag = refl
row5Off : rowOf gapTail5 ≡ rowOf ldlTail5
row5Off = refl
row6Diag : diagOf gapTail6 ≡ diagOf ldlTail6
row6Diag = refl
row6Off : rowOf gapTail6 ≡ rowOf ldlTail6
row6Off = refl
row7Diag : diagOf gapTail7 ≡ diagOf ldlTail7
row7Diag = refl
row7Off : rowOf gapTail7 ≡ rowOf ldlTail7
row7Off = refl
row8Diag : diagOf gapTail8 ≡ diagOf ldlTail8
row8Diag = refl
row8Off : rowOf gapTail8 ≡ rowOf ldlTail8
row8Off = refl
row9Diag : diagOf gapTail9 ≡ diagOf ldlTail9
row9Diag = refl
row9Off : rowOf gapTail9 ≡ rowOf ldlTail9
row9Off = refl
row10Diag : diagOf gapTail10 ≡ diagOf ldlTail10
row10Diag = refl
row10Off : rowOf gapTail10 ≡ rowOf ldlTail10
row10Off = refl
row11Diag : diagOf gapTail11 ≡ diagOf ldlTail11
row11Diag = refl
row11Off : rowOf gapTail11 ≡ rowOf ldlTail11
row11Off = refl

gapTail12EqualsLDL : gapTail12 ≡ ldlTail12
gapTail12EqualsLDL = refl
gapTail11EqualsLDL : gapTail11 ≡ ldlTail11
gapTail11EqualsLDL = Quad.qconsCong row11Diag row11Off gapTail12EqualsLDL
gapTail10EqualsLDL : gapTail10 ≡ ldlTail10
gapTail10EqualsLDL = Quad.qconsCong row10Diag row10Off gapTail11EqualsLDL
gapTail9EqualsLDL : gapTail9 ≡ ldlTail9
gapTail9EqualsLDL = Quad.qconsCong row9Diag row9Off gapTail10EqualsLDL
gapTail8EqualsLDL : gapTail8 ≡ ldlTail8
gapTail8EqualsLDL = Quad.qconsCong row8Diag row8Off gapTail9EqualsLDL
gapTail7EqualsLDL : gapTail7 ≡ ldlTail7
gapTail7EqualsLDL = Quad.qconsCong row7Diag row7Off gapTail8EqualsLDL
gapTail6EqualsLDL : gapTail6 ≡ ldlTail6
gapTail6EqualsLDL = Quad.qconsCong row6Diag row6Off gapTail7EqualsLDL
gapTail5EqualsLDL : gapTail5 ≡ ldlTail5
gapTail5EqualsLDL = Quad.qconsCong row5Diag row5Off gapTail6EqualsLDL
gapTail4EqualsLDL : gapTail4 ≡ ldlTail4
gapTail4EqualsLDL = Quad.qconsCong row4Diag row4Off gapTail5EqualsLDL
gapTail3EqualsLDL : gapTail3 ≡ ldlTail3
gapTail3EqualsLDL = Quad.qconsCong row3Diag row3Off gapTail4EqualsLDL
gapTail2EqualsLDL : gapTail2 ≡ ldlTail2
gapTail2EqualsLDL = Quad.qconsCong row2Diag row2Off gapTail3EqualsLDL
gapTail1EqualsLDL : gapTail1 ≡ ldlTail1
gapTail1EqualsLDL = Quad.qconsCong row1Diag row1Off gapTail2EqualsLDL
gapTail0EqualsLDL : gapTail0 ≡ ldlTail0
gapTail0EqualsLDL = Quad.qconsCong row0Diag row0Off gapTail1EqualsLDL

gapTriEqualsLDLTri : gapTri ≡ ldlTri
gapTriEqualsLDLTri = gapTail0EqualsLDL

------------------------------------------------------------------------
-- Compiler output: coefficient payment -> literal LDL decomposition.
------------------------------------------------------------------------

energyTriValue : ∀ c → Quad.evalTri energyTri (coordinates c) ≡ path13Energy c
energyTriValue c =
  trans (Quad.sumSquareCompiler energyFamilies (coordinates c)) (energyValuesMatch c)

normTriValue : ∀ c → Quad.evalTri normTri (coordinates c) ≡ path13NormSq c
normTriValue c =
  trans (Quad.sumSquareCompiler normFamilies (coordinates c)) (normValuesMatch c)

ldlTriValue : ∀ c → Quad.evalTri ldlTri (coordinates c) ≡ sumTermValues path13Terms c
ldlTriValue c =
  trans (Quad.sumWeightedSquareCompiler ldlFamilies (coordinates c)) (ldlValuesMatch c)

gapArithmetic : ∀ energyValue normValue →
  energyValue + (- oneEighteenth) * normValue
  ≡ energyValue - oneEighteenth * normValue
gapArithmetic = ℚRing.solve-∀

gapTriValue : ∀ c →
  Quad.evalTri gapTri (coordinates c)
  ≡ path13Energy c - oneEighteenth * path13NormSq c
gapTriValue c =
  trans
    (Quad.evalAdd energyTri (Quad.scaleTri (- oneEighteenth) normTri) (coordinates c))
    (trans
      (cong (λ right → Quad.evalTri energyTri (coordinates c) + right)
        (Quad.evalScale (- oneEighteenth) normTri (coordinates c)))
      (trans
        (cong
          (λ energyValue → energyValue + (- oneEighteenth) * Quad.evalTri normTri (coordinates c))
          (energyTriValue c))
        (trans
          (cong
            (λ normValue → path13Energy c + (- oneEighteenth) * normValue)
            (normTriValue c))
          (gapArithmetic (path13Energy c) (path13NormSq c)))))

path13GapToTerms : ∀ c →
  path13Energy c - oneEighteenth * path13NormSq c
  ≡ sumTermValues path13Terms c
path13GapToTerms c =
  trans (sym (gapTriValue c))
    (trans
      (cong (λ quadratic → Quad.evalTri quadratic (coordinates c)) gapTriEqualsLDLTri)
      (ldlTriValue c))

recomposeIdentity : ∀ energyValue normValue constant →
  energyValue ≡ constant * normValue + (energyValue - constant * normValue)
recomposeIdentity = ℚRing.solve-∀

path13LDLDecomposition : ∀ c →
  path13Energy c
  ≡ oneEighteenth * path13NormSq c + sumTermValues path13Terms c
path13LDLDecomposition c =
  trans
    (recomposeIdentity (path13Energy c) (path13NormSq c) oneEighteenth)
    (cong
      (λ remainder → oneEighteenth * path13NormSq c + remainder)
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

path13CoefficientCertificateLevel : ProofLevel
path13CoefficientCertificateLevel = machineChecked
