module DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact where

------------------------------------------------------------------------
-- ROUND417 / ACTUAL R291 GRAM DERIVATIVE FROM ONE HERMITIAN PRODUCT RULE
--
-- The R291 algebraic tangent is already exactly
--
--   2 ( Re<dA,B> + Re<A,dB> ).
--
-- Therefore we do not need a bespoke derivative theorem for every R290 pair.
-- One real-Hermitian product rule for the repository's rational Complex3
-- derivative semantics is sufficient.  This round packages that closure law
-- and compiles it directly to the exact R291 gram/gramTangent curves.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _*_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291

F : C3.RealField _
F = Rational.rationalRealField

record HermitianDerivativeCalculus
    (Time : Set)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf :
      (Time → ℚ) →
      (Time → ℚ) → Set) : Set₁ where
  field
    realHermitianGramProductRule :
      ∀ {a b da db} →
      VectorDerivativeOf a da →
      VectorDerivativeOf b db →
      ScalarDerivativeOf
        (λ time →
          R291.two * R179.realHermitianCross (a time) (b time))
        (λ time →
          R291.two *
            (R179.realHermitianCross (da time) (b time)
              + R179.realHermitianCross (a time) (db time)))

open HermitianDerivativeCalculus public

record DampedCellPairCurve (Time : Set) : Set where
  field
    pairAt : Time → R291.DampedCellPair

open DampedCellPairCurve public

cellACurve : ∀ {Time} → DampedCellPairCurve Time → Time → C3.Complex3 F
cellACurve P time = R291.cellA (pairAt P time)

cellBCurve : ∀ {Time} → DampedCellPairCurve Time → Time → C3.Complex3 F
cellBCurve P time = R291.cellB (pairAt P time)

tangentACurve : ∀ {Time} → DampedCellPairCurve Time → Time → C3.Complex3 F
tangentACurve P time = R291.tangentA (pairAt P time)

tangentBCurve : ∀ {Time} → DampedCellPairCurve Time → Time → C3.Complex3 F
tangentBCurve P time = R291.tangentB (pairAt P time)

gramCurve : ∀ {Time} → DampedCellPairCurve Time → Time → ℚ
gramCurve P time = R291.gram (pairAt P time)

gramTangentCurve : ∀ {Time} → DampedCellPairCurve Time → Time → ℚ
gramTangentCurve P time = R291.gramTangent (pairAt P time)

module ActualGramDerivative
    (Time : Set)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf :
      (Time → ℚ) →
      (Time → ℚ) → Set)
    (C : HermitianDerivativeCalculus
      Time VectorDerivativeOf ScalarDerivativeOf) where

  cellDerivativesBuildExactR291GramDerivative :
    (P : DampedCellPairCurve Time) →
    VectorDerivativeOf (cellACurve P) (tangentACurve P) →
    VectorDerivativeOf (cellBCurve P) (tangentBCurve P) →
    ScalarDerivativeOf (gramCurve P) (gramTangentCurve P)
  cellDerivativesBuildExactR291GramDerivative P dA dB =
    realHermitianGramProductRule C dA dB

round417R291GramTangentDefinitionUsedLiterally : Bool
round417R291GramTangentDefinitionUsedLiterally = true

round417OnlyHermitianProductRuleNeededAfterCellDerivatives : Bool
round417OnlyHermitianProductRuleNeededAfterCellDerivatives = true

round417R291GramTangentDefinitionUsedLiterallyIsTrue :
  round417R291GramTangentDefinitionUsedLiterally ≡ true
round417R291GramTangentDefinitionUsedLiterallyIsTrue = refl
