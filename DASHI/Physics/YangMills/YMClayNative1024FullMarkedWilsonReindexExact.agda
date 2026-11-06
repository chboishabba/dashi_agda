module DASHI.Physics.YangMills.YMClayNative1024FullMarkedWilsonReindexExact where

-- YM M.02: BOTH original Wilson marks travel with the entire
-- interacting weight under the actual 64-pair + 896-spectator sort.
-- No factorization of the weight, no independently chosen effective measure.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
import Data.Vec.Base as Vec
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; 1ℝ; _+ℝ_; _*ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayNativeC3SingleVectorPermutationCertificateExact as Native
import DASHI.Physics.YangMills.YMClayNative1024WeightedWilsonReindexExact as Original
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : ℝ)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  Weight : Set
  Weight = Vec.Vec Link Native.Count → ℝ

  originalMarkedWeight : Weight → Weight → ℝ → ℝ → Weight
  originalMarkedWeight left right s t original =
    Original.originalWilsonVectorWeight
      theory traceData exponential beta original
      *ℝ
    ((1ℝ +ℝ s *ℝ left original) *ℝ (1ℝ +ℝ t *ℝ right original))

  originalSortedMarkedWeight : Weight → Weight → ℝ → ℝ → Weight
  originalSortedMarkedWeight left right s t sorted =
    originalMarkedWeight left right s t
      (Haar.permuteLinks
        (Original.inverseProgram (Original.actualPairProgram theory))
        sorted)

  -- All coefficients of the same finite 2-J generating polynomial
  -- are preserved, because the entire marked integrand is preserved.
  originalMarkedWilsonPartitionReindexes :
    (source : Haar.OneLinkProductHaar Link)
    (left right : Weight) (s t : ℝ) →
    Haar.productIntegral source (originalMarkedWeight left right s t)
    ≡ Haar.productIntegral source
        (originalSortedMarkedWeight left right s t)
  originalMarkedWilsonPartitionReindexes source left right s t =
    Original.actualWeightedReindex source
      (Original.actualPairProgram theory)
      (originalMarkedWeight left right s t)
