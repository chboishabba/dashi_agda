module DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsPolarizedJordanExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Integer.Base using (+_)
open import Data.Rational using (_/_)
open import Data.Rational.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import DASHI.Core.Q using (ℚ; _+ℚ_; _*ℚ_)
import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsCarrierExact as R
import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsLawObligationsExact as Laws
import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsBasicLawWitnessesExact as Basic
import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsBilinearityWitnessExact as Bilinear

------------------------------------------------------------------------
-- POLARIZED JORDAN TERMINAL FRONTIER
--
-- For a commutative bilinear product the ordinary Jordan identity is cubic in
-- X.  Its full polarization in the X slot is the four-linear identity
--
--   ((A B)Y)C + ((A C)Y)B + ((B C)Y)A
--     = (A B)(Y C) + (A C)(Y B) + (B C)(Y A).
--
-- Setting A=B=C=X gives three copies of each side of the ordinary Jordan
-- identity.  Over Q, multiplication by 3 is cancellable.  This owner makes
-- that final implication literal on the repository carrier.
--
-- The independent exact-Fraction executable checks the polarized identity on
-- all 27^4 = 531441 coordinate-basis quadruples.  That computation is a LOCAL
-- RECEIPT only.  The remaining formal payment is a basis-span/multilinearity
-- compiler from those basis equalities to the all-elements proposition below.
------------------------------------------------------------------------

_prod_ : R.RationalFirstTits27 → R.RationalFirstTits27 → R.RationalFirstTits27
_prod_ = R.firstTitsJordanProduct

tripleJ : R.RationalFirstTits27 → R.RationalFirstTits27
tripleJ X = R.addJ X (R.addJ X X)

PolarizedJordanIdentity : Set
PolarizedJordanIdentity =
  (A B C Y : R.RationalFirstTits27) →
  R.addJ
    (((A prod B) prod Y) prod C)
    (R.addJ
      (((A prod C) prod Y) prod B)
      (((B prod C) prod Y) prod A))
  ≡
  R.addJ
    ((A prod B) prod (Y prod C))
    (R.addJ
      ((A prod C) prod (Y prod B))
      ((B prod C) prod (Y prod A)))

thirdℚ : ℚ
thirdℚ = + 1 / 3

thirdTripleM : (A : R.QMatrix3) →
  R.scaleM thirdℚ (R.addM A (R.addM A A)) ≡ A
thirdTripleM A =
  Basic.qmatrix3Ext
    (solve 1 (λ a → con thirdℚ :* (a :+ (a :+ a)) := a) refl (R.m00 A))
    (solve 1 (λ a → con thirdℚ :* (a :+ (a :+ a)) := a) refl (R.m01 A))
    (solve 1 (λ a → con thirdℚ :* (a :+ (a :+ a)) := a) refl (R.m02 A))
    (solve 1 (λ a → con thirdℚ :* (a :+ (a :+ a)) := a) refl (R.m10 A))
    (solve 1 (λ a → con thirdℚ :* (a :+ (a :+ a)) := a) refl (R.m11 A))
    (solve 1 (λ a → con thirdℚ :* (a :+ (a :+ a)) := a) refl (R.m12 A))
    (solve 1 (λ a → con thirdℚ :* (a :+ (a :+ a)) := a) refl (R.m20 A))
    (solve 1 (λ a → con thirdℚ :* (a :+ (a :+ a)) := a) refl (R.m21 A))
    (solve 1 (λ a → con thirdℚ :* (a :+ (a :+ a)) := a) refl (R.m22 A))

thirdTripleJ : (X : R.RationalFirstTits27) → R.scaleJ thirdℚ (tripleJ X) ≡ X
thirdTripleJ (R.rationalFirstTits27 A B C) =
  Basic.firstTits27Ext (thirdTripleM A) (thirdTripleM B) (thirdTripleM C)

tripleJCancel : {A B : R.RationalFirstTits27} → tripleJ A ≡ tripleJ B → A ≡ B
tripleJCancel {A} {B} equality =
  trans
    (sym (thirdTripleJ A))
    (trans
      (cong (R.scaleJ thirdℚ) equality)
      (thirdTripleJ B))

polarizedImpliesJordan : PolarizedJordanIdentity → Laws.JordanIdentity
polarizedImpliesJordan polarized X Y =
  tripleJCancel (polarized X X X Y)

record PolarizedJordanLocalReceipt : Set where
  constructor polarized-jordan-local-receipt
  field
    sameLiteralRationalFirstTitsProductUsed : Bool
    basisDimensionTwentySevenUsed : Bool
    exactFractionArithmeticUsed : Bool
    basisProductSupport414_291_24Reproduced : Bool
    basisQuadruplesChecked531441 : Bool
    allBasisPolarizedResiduesZero : Bool
    floatingPointUsedForIdentityCheck : Bool
    polarizedAllElementsImpliesJordanSourceWritten : Bool
    allElementsPolarizedIdentitySourceWritten : Bool
    basisSpanMultilinearCompilerPaid : Bool
    jordanIdentitySourceWritten : Bool
    exactHeadAgdaKernelReceiptPresent : Bool
    boundary : String
open PolarizedJordanLocalReceipt public

canonicalPolarizedJordanLocalReceipt : PolarizedJordanLocalReceipt
canonicalPolarizedJordanLocalReceipt =
  polarized-jordan-local-receipt
    true true true true true true false true
    false false false false
    "Exact Fraction arithmetic reproduces the 414/291/24 basis-product support census and checks all 27^4=531441 polarized Jordan basis quadruples with zero residue. The Agda owner source-writes the theorem that an all-elements polarized identity implies the ordinary Jordan identity by cancelling three over Q. The remaining formal wall is the basis-span/multilinearity compiler turning the exhaustive basis table into PolarizedJordanIdentity; neither the Python replay nor the source theorem alone inhabits JordanIdentity or supplies a kernel receipt."

bilinearityBoundary : Bilinear.BilinearityBoundary
bilinearityBoundary = Bilinear.canonicalBoundary
