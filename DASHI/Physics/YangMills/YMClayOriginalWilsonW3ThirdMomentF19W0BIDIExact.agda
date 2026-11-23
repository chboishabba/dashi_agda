module DASHI.Physics.YangMills.YMClayOriginalWilsonW3ThirdMomentF19W0BIDIExact where

------------------------------------------------------------------------
-- P0.W1 -> W3 THIRD-MARK SOURCE RECEIVER, NO NEW SOURCE/T/HAMILTONIAN.
--
-- The actual original full-Wilson 1,F,G,FG F19 receiver is already in
-- YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact.
-- The 1528-plaquette Duhamel restoration of the original source W3
-- requires four ADDITIONAL source integrands for each H=t_p:
--   H, F*H, G*H, F*G*H,
-- preserving the SAME fine weight and all 896 spectators.
--
-- These are simply four specializations of ORIGINAL arbitrary-integrand
-- finite Haar/F19 reindex, not another probability or blocked T record.
-- The existing W0 first-pair conditional source T works on F*G*H.
--
-- IMPORTANT: "W0 candidate T" remains a geometric FINITE F19 source;
-- it is NOT the CMP119/122 selected Omega/Lambda/S constrained
-- physical T, and nothing here bounds the W3 absolute connecting tail.
-- SOURCE WRITTEN; Agda kernel acceptance NOT run.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Vec.Base using (Vec; _∷_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClaySUNWeightedDisjointPairFibreReparamExact as Fibre
import DASHI.Physics.YangMills.YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact as F19
import DASHI.Physics.YangMills.YMClayW0OriginalF19CandidateEquation171TExact as W0

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : ℝ)
    (source : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory source)
    (linear : Ordered.OneLinkOrderedHaarAlgebra source)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  Pair : Set
  Pair = Fibre.Pair theory source bilateral

  FineTest : Set
  FineTest = Vec Pair 64 → Vec Link 896 → ℝ

  weightedH : FineTest → FineTest → FineTest
  weightedH weight H pairs spectators =
    weight pairs spectators *ℝ H pairs spectators

  weightedFH : FineTest → FineTest → FineTest → FineTest
  weightedFH weight F H pairs spectators =
    (weight pairs spectators *ℝ F pairs spectators) *ℝ
      H pairs spectators

  weightedGH : FineTest → FineTest → FineTest → FineTest
  weightedGH weight G H pairs spectators =
    (weight pairs spectators *ℝ G pairs spectators) *ℝ
      H pairs spectators

  weightedFGH : FineTest → FineTest → FineTest → FineTest → FineTest
  weightedFGH weight F G H pairs spectators =
    ((weight pairs spectators *ℝ F pairs spectators) *ℝ
      G pairs spectators) *ℝ H pairs spectators

  -- All four original finite W3 third-mark NUMERATOR coefficients use
  -- the exact SAME existing all-integrand fine->F19 Haar theorem.
  -- The weight is arbitrary: in particular it may contain the ORIGINAL
  -- 4D Wilson beta/tau interpolation and all interacting spectators.
  sourceHIsF19 :
    ∀ weight H →
    F19.originalFineCoefficient
      theory traceData exponential beta source bilateral linear
      (weightedH weight H)
    ≡
    F19.originalF19Coefficient
      theory traceData exponential beta source bilateral linear
      (weightedH weight H)
  sourceHIsF19 weight H =
    F19.originalFineCoefficientEqualsF19
      theory traceData exponential beta source bilateral linear
      (weightedH weight H)

  sourceFHIsF19 :
    ∀ weight F H →
    F19.originalFineCoefficient
      theory traceData exponential beta source bilateral linear
      (weightedFH weight F H)
    ≡
    F19.originalF19Coefficient
      theory traceData exponential beta source bilateral linear
      (weightedFH weight F H)
  sourceFHIsF19 weight F H =
    F19.originalFineCoefficientEqualsF19
      theory traceData exponential beta source bilateral linear
      (weightedFH weight F H)

  sourceGHIsF19 :
    ∀ weight G H →
    F19.originalFineCoefficient
      theory traceData exponential beta source bilateral linear
      (weightedGH weight G H)
    ≡
    F19.originalF19Coefficient
      theory traceData exponential beta source bilateral linear
      (weightedGH weight G H)
  sourceGHIsF19 weight G H =
    F19.originalFineCoefficientEqualsF19
      theory traceData exponential beta source bilateral linear
      (weightedGH weight G H)

  sourceFGHIsF19 :
    ∀ weight F G H →
    F19.originalFineCoefficient
      theory traceData exponential beta source bilateral linear
      (weightedFGH weight F G H)
    ≡
    F19.originalF19Coefficient
      theory traceData exponential beta source bilateral linear
      (weightedFGH weight F G H)
  sourceFGHIsF19 weight F G H =
    F19.originalFineCoefficientEqualsF19
      theory traceData exponential beta source bilateral linear
      (weightedFGH weight F G H)

  -- Pointwise on the 64 ORIGINAL coarse holonomies this third mark is
  -- exactly the already selected W0 CANDIDATE conditional T mass.
  sourceFGHIsOriginalW0CandidateT :
    ∀ weight F G H coarse →
    W0.candidateF19Mass
      theory traceData exponential beta source bilateral linear
      (weightedFGH weight F G H) coarse
    ≡
    F19.originalF19CoefficientDensity
      theory traceData exponential beta source bilateral linear
      (weightedFGH weight F G H) coarse
  sourceFGHIsOriginalW0CandidateT weight F G H coarse =
    W0.candidateMassIsExistingOriginalF19
      theory traceData exponential beta source bilateral linear
      (weightedFGH weight F G H) coarse

  -- One genuine NATIVE ordered local fibre step, with the entire
  -- source F*G*H integrand and all original 896 spectator variables
  -- INSIDE the same conditional fibre, not multiplied after averaging.
  sourceFGHOriginalW0FirstPairTStep :
    ∀ weight F G H (head : Link) (tail : Vec Link 63) →
    W0.candidateF19Mass
      theory traceData exponential beta source bilateral linear
      (weightedFGH weight F G H) (head ∷ tail)
    ≡
    W0.sourceFirstPairTStep
      theory traceData exponential beta source bilateral linear
      head tail
      (W0.spectatorMarginalOfFineIntegrand
        theory traceData exponential beta source bilateral linear
        (weightedFGH weight F G H))
  sourceFGHOriginalW0FirstPairTStep weight F G H head tail =
    W0.sourceF19MarkedFirstPairLocalizationExact
      theory traceData exponential beta source bilateral linear
      head tail (weightedFGH weight F G H)
