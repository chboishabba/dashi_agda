module DASHI.Foundations.FinitePolydiscCauchyAxioms where

-- Narrow imported complex-analysis boundary for the finite multivariable
-- coefficient used in CMP 116 (1.23).  This contains no Yang--Mills names,
-- geometry, walks, domains, or decay parameters.  Complex pair arithmetic is
-- concrete in ComplexAxiomatic; contour integration and Cauchy's estimate are
-- deliberately imported because DASHI's real carrier is itself axiomatic.

open import Data.List.Base using (List)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; _-ℝ_ ; _*ℝ_ ; _≤ℝ_ )
open import DASHI.Foundations.ComplexAxiomatic using (ℂ)

record FinitePolydiscCauchyAxioms : Set₁ where
  field
    Index Value : Set

    Assignment : Set
    assignmentAt : Assignment → Index → ℂ

    Function : List Index → Set
    evaluate :
      ∀ {indices} →
      Function indices → Assignment → Value

    _-Value_ : Value → Value → Value
    normValue : Value → ℝ

    functionDifference :
      ∀ {indices} →
      Function indices → Function indices → Function indices

    evaluateDifference :
      ∀ {indices : List Index}
      (F G : Function indices)
      (s : Assignment) →
      evaluate (functionDifference F G) s
        ≡
      evaluate F s -Value evaluate G s

    coefficient :
      (indices : List Index) →
      Function indices →
      Value

    coefficientDifference :
      ∀ {indices : List Index}
      (F G : Function indices) →
      coefficient indices F -Value coefficient indices G
        ≡
      coefficient indices (functionDifference F G)

    BoundaryDifferenceBound :
      ∀ {indices} →
      Function indices → Function indices → ℝ → Set

    boundaryEnvelope :
      ∀ {indices : List Index}
      (F G : Function indices)
      (M : ℝ) →
      (∀ s →
        normValue (evaluate F s -Value evaluate G s) ≤ℝ M) →
      BoundaryDifferenceBound F G M

    coefficientBound :
      ∀ {indices : List Index}
      (F : Function indices)
      (M : ℝ) →
      BoundaryDifferenceBound F F M →
      normValue (coefficient indices F) ≤ℝ M

    coefficientDifferenceBound :
      ∀ {indices : List Index}
      (F G : Function indices)
      (M : ℝ) →
      BoundaryDifferenceBound F G M →
      normValue
        (coefficient indices F -Value coefficient indices G)
        ≤ℝ
      M

-- `coefficientDifferenceBound` is the finite-polydisc Cauchy estimate in the
-- exact form consumed downstream: a uniform boundary envelope controls the
-- extracted coefficient difference.  Its proof is external complex analysis,
-- but the boundary statement itself remains an ordinary, owned application
-- theorem in the Yang--Mills module.

open FinitePolydiscCauchyAxioms public
