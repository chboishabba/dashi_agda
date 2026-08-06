module DASHI.Physics.Closure.NSTriadKNYuExteriorTailCriterionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier--Stokes Equations".
-- arXiv DOI: 10.48550/arXiv.2606.27560.
--
-- PURPOSE
-- Isolate an exact sufficient criterion for the exterior part omitted by the
-- finite annular Carleson convolution.  If an exterior residual is bounded by
--
--   sourceTail_q * profile_q,
--
-- the source tail is nonnegative, and 0 <= profile_q <= 1, then the residual
-- is pointwise bounded by sourceTail_q.  Hence vanishing of the normalized
-- source tail transfers to the exterior residual with the same cutoff.
--
-- This theorem does not derive source-tail compactness from energy.  It proves
-- the complete ordered transfer once the genuine exterior-tail estimate has
-- been established for the PDE realization.
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoTerminalInteractionDepletionTransferExact as Limit

record ExteriorTailCriterionData : Set where
  constructor exterior-tail-criterion-data
  field
    exteriorResidual sourceTail profile : ℕ → ℚ

    sourceTailNonnegative :
      (shell : ℕ) → 0ℚ ≤ sourceTail shell

    profileNonnegative :
      (shell : ℕ) → 0ℚ ≤ profile shell

    profileAtMostOne :
      (shell : ℕ) → profile shell ≤ 1ℚ

    exteriorResidualBound :
      (shell : ℕ) →
      exteriorResidual shell
      ≤ sourceTail shell * profile shell

open ExteriorTailCriterionData public

exteriorResidualPointwiseBySource :
  (dataSet : ExteriorTailCriterionData) →
  (shell : ℕ) →
  exteriorResidual dataSet shell ≤ sourceTail dataSet shell
exteriorResidualPointwiseBySource dataSet shell =
  let
    profileStep :
      sourceTail dataSet shell * profile dataSet shell
      ≤ sourceTail dataSet shell * 1ℚ
    profileStep =
      let
        instance
          sourceIsNonnegative =
            nonNegative (sourceTailNonnegative dataSet shell)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (sourceTail dataSet shell)
        (profileAtMostOne dataSet shell)

    targetMeaning :
      sourceTail dataSet shell * 1ℚ
      ≡ sourceTail dataSet shell
    targetMeaning = solve (sourceTail dataSet shell ∷ [])
  in
  ℚₚ.≤-trans
    (exteriorResidualBound dataSet shell)
    (subst
      (λ upper →
        sourceTail dataSet shell * profile dataSet shell ≤ upper)
      targetMeaning
      profileStep)

exteriorResidualVanishing :
  (dataSet : ExteriorTailCriterionData) →
  Limit.TendsToZero (sourceTail dataSet) →
  Limit.TendsToZero (exteriorResidual dataSet)
exteriorResidualVanishing dataSet sourceVanishing =
  Limit.interactionDepletionFromCriticalDepletion
    (Limit.critical-to-interaction-data
      (exteriorResidual dataSet)
      (sourceTail dataSet)
      (exteriorResidualPointwiseBySource dataSet))
    sourceVanishing
