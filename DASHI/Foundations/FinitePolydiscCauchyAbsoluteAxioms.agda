module DASHI.Foundations.FinitePolydiscCauchyAbsoluteAxioms where

-- Absolute companion to `FinitePolydiscCauchyAxioms`.
--
-- The historical authority is deliberately optimized for differences of two
-- analytic functions.  Its `BoundaryDifferenceBound F G M` is the correct ABI
-- for stability/comparison arguments, but an absolute coefficient estimate
-- must not be obtained by feeding the degenerate pair `(F , F)` to that
-- difference relation.
--
-- This sibling is indexed by the SAME finite-polydisc carrier.  It adds only
-- the standard absolute Cauchy boundary theorem:
--
--     sup_boundary ||F|| <= M  ->  ||coefficient F|| <= M.
--
-- There are no Yang--Mills names or decay assumptions here.  The complex
-- analytic theorem is an imported foundational authority, exactly like the
-- historical difference form; concrete boundary-value estimates remain owned
-- by the application.

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_)
open import DASHI.Foundations.FinitePolydiscCauchyAxioms as Cauchy

record FinitePolydiscCauchyAbsoluteAxioms
    (base : Cauchy.FinitePolydiscCauchyAxioms) : Set₁ where
  field
    BoundaryValueBound :
      ∀ {indices} →
      Cauchy.Function base indices → ℝ → Set

    boundaryValueEnvelope :
      ∀ {indices}
      (F : Cauchy.Function base indices)
      (M : ℝ) →
      (∀ (s : Cauchy.BoundaryAssignment base indices) →
        Cauchy.normValue base
          (Cauchy.evaluate base F (Cauchy.boundaryAssignment base s))
        ≤ℝ M) →
      BoundaryValueBound F M

    coefficientAbsoluteBound :
      ∀ {indices}
      (F : Cauchy.Function base indices)
      (M : ℝ) →
      BoundaryValueBound F M →
      Cauchy.normValue base (Cauchy.coefficient base indices F) ≤ℝ M

open FinitePolydiscCauchyAbsoluteAxioms public
