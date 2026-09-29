{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRealFullSupportHaarExact where

open import Data.Product.Base using (Σ; _,_)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _<ℝ_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite

------------------------------------------------------------------------
-- STANDARD FULL-SUPPORT HAAR STRICT-POSITIVITY THEOREM SURFACE
--
-- On a compact group (and finite products thereof), normalized Haar measure has
-- full support.  Therefore a continuous nonnegative real function which is
-- strictly positive at one point has strictly positive Haar integral.
--
-- The current compact-Lie authority owns normalized Haar invariance but does not
-- expose topology/support.  This record is the least-privilege standard-analysis
-- extension consumed by the physical source lane.
------------------------------------------------------------------------

record FullSupportRealHaarAuthority
    {Configuration : Set}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ) : Set₁ where
  field
    Continuous : (Configuration → ℝ) → Set

    strictIntegralFromPositivePoint :
      ∀ observable →
      Finite.PointwiseNonnegative observable →
      Continuous observable →
      Σ Configuration (λ configuration → 0ℝ <ℝ observable configuration) →
      0ℝ <ℝ Physical.haarIntegral measure observable

open FullSupportRealHaarAuthority public

fullSupportRealHaarAuthorityLevel : ProofLevel
fullSupportRealHaarAuthorityLevel = standardImported
