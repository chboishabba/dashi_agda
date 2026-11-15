module DASHI.Physics.YangMills.BalabanClayT4LiteralFourOrbitErrorBudgetFoldExact where

-- Exact finite ERROR-ACCOUNTING for the ORIGINAL four selected source
-- quadrature receipts. The geometric weights 4,6,4,1 come from
-- original generated source cells. No phantom four integrals or
-- independently supplied rational substitute contributions.
--
-- Physical interval validity STILL requires the source's
-- hessianBoundValid / quadratureErrorFormulaValid /
-- trueIntegralInsideIntervalPlusError fields to be inhabited
-- by actual soundness proofs, not just Set-valued declarations.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_; _/_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4SemanticFourRepresentativeQuadratureExact as Four
import DASHI.Physics.YangMills.BalabanClayT4OriginalEvaluatorFourOrbitEndpointSumsExact as Source
import DASHI.Physics.YangMills.BalabanCMP109FourOrbitNormalizedQuadratureExact as Sums
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanCMP109VacuumPolarizationHypercubicSourceSymmetryExact as Sym

w1 w2 w3 w4 : ℚ
w1 = + 4 / 1
w2 = + 6 / 1
w3 = + 4 / 1
w4 = + 1 / 1

-- Each error is obtained from the ACTUAL quadrature at its ACTUAL
-- source representative, not a newly constructed numerical record.

fourErrorBudget :
  ∀ {expressions ward scalarData} →
  Four.LiteralSemanticFourQuadratureCut scalarData → ℚ
fourErrorBudget dataSet =
  w1 * Eval.errorBound (Four.quadrature1 dataSet)
  + w2 * Eval.errorBound (Four.quadrature2 dataSet)
  + w3 * Eval.errorBound (Four.quadrature3 dataSet)
  + Eval.errorBound (Four.quadrature4 dataSet)

-- Literal lower/upper endpoint sums from the same source-replayed
-- recursive evaluator, widened by the four source error values.
sourceLowerWithError :
  ∀ {expressions ward scalarData} →
  Four.LiteralSemanticFourQuadratureCut scalarData → ℚ
sourceLowerWithError dataSet =
  Sums.fourOrbitNormalizedValue
    (Source.sourceLower (Four.source dataSet))
  - fourErrorBudget dataSet

sourceUpperWithError :
  ∀ {expressions ward scalarData} →
  Four.LiteralSemanticFourQuadratureCut scalarData → ℚ
sourceUpperWithError dataSet =
  Sums.fourOrbitNormalizedValue
    (Source.sourceUpper (Four.source dataSet))
  + fourErrorBudget dataSet

-- These are bona fide source-identity equalities about the ACTUAL
-- 240-cell rational interval endpoint fold, with no independent
-- four-representative numerical inputs.

original240LowerFoldWithFourErrors :
  ∀ {expressions ward scalarData}
    (dataSet : Four.LiteralSemanticFourQuadratureCut scalarData) →
  Sums.normalizedRegularSum (Source.sourceLower (Four.source dataSet))
    - fourErrorBudget dataSet
  ≡ sourceLowerWithError dataSet
original240LowerFoldWithFourErrors dataSet =
  cong (λ v → v - fourErrorBudget dataSet)
    (Source.actualLowerEndpointNormalized240ToFour
      (Four.source dataSet) (Four.semantic dataSet))

original240UpperFoldWithFourErrors :
  ∀ {expressions ward scalarData}
    (dataSet : Four.LiteralSemanticFourQuadratureCut scalarData) →
  Sums.normalizedRegularSum (Source.sourceUpper (Four.source dataSet))
    + fourErrorBudget dataSet
  ≡ sourceUpperWithError dataSet
original240UpperFoldWithFourErrors dataSet =
  cong (λ v → v + fourErrorBudget dataSet)
    (Source.actualUpperEndpointNormalized240ToFour
      (Four.source dataSet) (Four.semantic dataSet))

-- Four actual error numbers remain symbols until the source's
-- CertifiedBoxQuadrature values are explicitly constructed.
-- The formula does not claim their signs, positivity or analytic truth.

-- Crucial additional physical cut: the source integrand evaluation
-- may be B4-invariant, but the quadrature RULE / discretisation and
-- ERROR BOUND are not thereby proved invariant. To legitimately
-- use four errors for ALL 240 cells, source error covariance MUST be
-- certified separately. This is not derivable from interval endpoints.

sourceError :
  ∀ {expressions ward scalarData} →
  Eval.LiteralGeneratedBoxEvaluator expressions ward scalarData →
  Grid.GridCell4 → ℚ
sourceError source cell =
  Eval.errorBound (Eval.quadrature source cell)

-- This equality is exactly conditional on the original error values
-- transforming covariantly under the seven source generators.
original240ErrorFoldIfSourceCovariant :
  ∀ {expressions ward scalarData}
    (dataSet : Four.LiteralSemanticFourQuadratureCut scalarData) →
    Sym.CMP109ScalarEuclideanSymmetry
      (sourceError (Four.source dataSet)) →
  Sums.normalizedRegularSum (sourceError (Four.source dataSet))
    ≡ fourErrorBudget dataSet
original240ErrorFoldIfSourceCovariant dataSet physicalErrorSymmetry =
  Sums.sourceSymmetryNormalizedQuadrature physicalErrorSymmetry

original240LowerWithActualSourceErrors :
  ∀ {expressions ward scalarData}
    (dataSet : Four.LiteralSemanticFourQuadratureCut scalarData) →
    Sym.CMP109ScalarEuclideanSymmetry
      (sourceError (Four.source dataSet)) →
  (Sums.normalizedRegularSum (Source.sourceLower (Four.source dataSet))
    - Sums.normalizedRegularSum (sourceError (Four.source dataSet)))
    ≡ sourceLowerWithError dataSet
original240LowerWithActualSourceErrors dataSet physicalErrorSymmetry =
  cong₂ _-_
    (Source.actualLowerEndpointNormalized240ToFour
      (Four.source dataSet) (Four.semantic dataSet))
    (original240ErrorFoldIfSourceCovariant dataSet physicalErrorSymmetry)

original240UpperWithActualSourceErrors :
  ∀ {expressions ward scalarData}
    (dataSet : Four.LiteralSemanticFourQuadratureCut scalarData) →
    Sym.CMP109ScalarEuclideanSymmetry
      (sourceError (Four.source dataSet)) →
  (Sums.normalizedRegularSum (Source.sourceUpper (Four.source dataSet))
    + Sums.normalizedRegularSum (sourceError (Four.source dataSet)))
    ≡ sourceUpperWithError dataSet
original240UpperWithActualSourceErrors dataSet physicalErrorSymmetry =
  cong₂ _+_
    (Source.actualUpperEndpointNormalized240ToFour
      (Four.source dataSet) (Four.semantic dataSet))
    (original240ErrorFoldIfSourceCovariant dataSet physicalErrorSymmetry)

-- Source-owned error covariance and numeric analytic validity remain OPEN,
-- independently of semantic equality of the original integrand intervals.
