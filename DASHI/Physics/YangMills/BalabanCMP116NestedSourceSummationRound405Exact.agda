module DASHI.Physics.YangMills.BalabanCMP116NestedSourceSummationRound405Exact where

-- ROUND405 / CMP116 NESTED SOURCE SUMMATION
--
-- R404 pays the absolute finite summation of differentiated walk terms carrying
-- one common localization domain Y.  CMP116 (1.26)--(1.29) then performs the
-- next positive summation over the admissible localization domains.  This owner
-- isolates exactly that compiler step.
--
-- The theorem does NOT prove the source-native generalized-walk estimate for an
-- individual differentiated term and does NOT manufacture admissibility of the
-- selected T5/RG source insertion.  Those remain the theorem-bearing P0a/P0b
-- input.  It only says that once each common-Y contribution is absolutely
-- controlled and the positive common-Y majorants sum below the selected shell,
-- the complete selected boundary integrand is below that shell.
--
-- No new source-direction carrier, Hessian comparison, Cauchy coefficient,
-- rooted-shell geometry, or spectral object is introduced.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using (List)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; absℝ; _≤ℝ_; ≤ℝ-trans)
import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum

-- Generic finite positive outer summation.  R404 supplies the intended
-- `commonYContributionBelowMajorant` witnesses on the preferred source route.
absoluteNestedSourceSummation :
  ∀ {Domain : Set}
    (domains : List Domain)
    (commonYContribution commonYMajorant : Domain → ℝ)
    (selectedBoundaryIntegrand selectedShell : ℝ) →
  selectedBoundaryIntegrand ≡ Resum.sumℝ commonYContribution domains →
  (∀ domain → absℝ (commonYContribution domain) ≤ℝ commonYMajorant domain) →
  Resum.sumℝ commonYMajorant domains ≤ℝ selectedShell →
  absℝ selectedBoundaryIntegrand ≤ℝ selectedShell
absoluteNestedSourceSummation
    domains commonYContribution commonYMajorant
    selectedBoundaryIntegrand selectedShell
    boundaryAsDomainSum commonYContributionBelowMajorant majorantsSumBelowShell
  rewrite boundaryAsDomainSum =
  ≤ℝ-trans
    (Resum.absSumℝ≤sumAbsℝ commonYContribution domains)
    (≤ℝ-trans
      (Resum.sumℝ-mono domains commonYContributionBelowMajorant)
      majorantsSumBelowShell)

-- Literal CMP116 reading of the generic theorem:
--
--   localizedDomains                 : the Y-family surviving the source cuts;
--   differentiatedCommonYContribution: the already-resummed R404 contribution
--                                       for one Y;
--   commonYTreeMajorant              : the positive (1.26)--(1.29) majorant;
--   selectedBoundaryIntegrand        : the full twice-varied boundary value;
--   selectedConnectingShell          : the consumer-facing shell envelope.
--
-- This is intentionally a theorem/function rather than another receipt record.
cmp116NestedAbsoluteBoundaryLocalization :
  ∀ {Domain : Set}
    (localizedDomains : List Domain)
    (differentiatedCommonYContribution commonYTreeMajorant : Domain → ℝ)
    (selectedBoundaryIntegrand selectedConnectingShell : ℝ) →
  selectedBoundaryIntegrand
    ≡ Resum.sumℝ differentiatedCommonYContribution localizedDomains →
  (∀ domain →
    absℝ (differentiatedCommonYContribution domain)
      ≤ℝ commonYTreeMajorant domain) →
  Resum.sumℝ commonYTreeMajorant localizedDomains
    ≤ℝ selectedConnectingShell →
  absℝ selectedBoundaryIntegrand ≤ℝ selectedConnectingShell
cmp116NestedAbsoluteBoundaryLocalization = absoluteNestedSourceSummation
