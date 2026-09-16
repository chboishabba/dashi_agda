module DASHI.Physics.YangMills.BalabanCMP116AbsoluteWalkResummationRound404Exact where

-- ROUND404 / ABSOLUTE SAME-Y WALK RESUMMATION
--
-- CMP116 (1.23)--(1.25) bounds individual differentiated localized terms and
-- then sums all terms carrying one common localization domain Y.  The existing
-- `BalabanMarkedPolarisationResummation` owns the required finite triangle and
-- monotonicity algebra, but its physical record is specialized to differences
-- of two domain sequences.
--
-- P0b is absolute.  This owner extracts only the generic same-Y summation step:
-- if the selected boundary integrand is a finite sum of walk terms, every walk
-- term is absolutely dominated by its source majorant, and those majorants sum
-- below the selected shell, then the complete boundary integrand is below that
-- shell.  No domain comparison, common-walk cancellation, Cauchy coefficient,
-- rooted-shell geometry, or spectral semantics enter here.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using (List)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; absℝ; _≤ℝ_; ≤ℝ-trans)
import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum

absoluteFiniteWalkResummation :
  ∀ {Walk : Set}
    (walks : List Walk)
    (contribution majorant : Walk → ℝ)
    (boundaryValue shellBound : ℝ) →
  boundaryValue ≡ Resum.sumℝ contribution walks →
  (∀ walk → absℝ (contribution walk) ≤ℝ majorant walk) →
  Resum.sumℝ majorant walks ≤ℝ shellBound →
  absℝ boundaryValue ≤ℝ shellBound
absoluteFiniteWalkResummation
    walks contribution majorant boundaryValue shellBound
    boundaryAsWalkSum termwise summable
  rewrite boundaryAsWalkSum =
  ≤ℝ-trans
    (Resum.absSumℝ≤sumAbsℝ contribution walks)
    (≤ℝ-trans
      (Resum.sumℝ-mono walks termwise)
      summable)

-- Source-shaped specialization: the names below correspond directly to the
-- CMP116 proof order rather than to a new receipt object.
--
--   differentiatedTerm          : one (1.23) contribution;
--   differentiatedTermMajorant  : its (1.24)+(1.25) bound;
--   commonYBoundaryIntegrand    : sum of all (1.23) terms with common Y;
--   commonYShell                : post-resummation shell majorant.
--
-- The theorem is deliberately parameterized by those literal functions instead
-- of storing the conclusion in another record.
cmp116CommonYAbsoluteBoundaryBound :
  ∀ {Term : Set}
    (termsWithCommonY : List Term)
    (differentiatedTerm differentiatedTermMajorant : Term → ℝ)
    (commonYBoundaryIntegrand commonYShell : ℝ) →
  commonYBoundaryIntegrand
    ≡ Resum.sumℝ differentiatedTerm termsWithCommonY →
  (∀ term →
    absℝ (differentiatedTerm term)
      ≤ℝ differentiatedTermMajorant term) →
  Resum.sumℝ differentiatedTermMajorant termsWithCommonY
    ≤ℝ commonYShell →
  absℝ commonYBoundaryIntegrand ≤ℝ commonYShell
cmp116CommonYAbsoluteBoundaryBound = absoluteFiniteWalkResummation
