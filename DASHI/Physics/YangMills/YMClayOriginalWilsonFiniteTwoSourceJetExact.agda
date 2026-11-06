module DASHI.Physics.YangMills.YMClayOriginalWilsonFiniteTwoSourceJetExact where

------------------------------------------------------------------------
-- Y.01/Y.02 FINITE ORIGINAL WILSON -> TWO MARKED SOURCE JET.
--
-- All finite observables are literal scalar-valued functions on the
-- ORIGINAL changing periodic SU(N) link carrier.  The finite Gibbs
-- measure is exactly YMClaySUNVariablePhysicalCutoffFamilyExact's
-- product-Haar-normalised Wilson measure; no second covariance, measure,
-- group action, beta history or selected J algebra is introduced.
--
-- The first and mixed SECOND FORMAL source jets are the actual
-- normalized Wilson one- and two-insertion expectations.  The formal
-- logarithmic second jet is their connected combination.  Reuse the
-- existing NormalizedTwoSourceConnectedCumulantExact algebraic proof
-- to identify the literal two source directions with this covariance.
--
-- IMPORTANT: a formal jet is NOT a claimed analytic derivative of the
-- actual exponential generating functional.  Its identification with
-- CMP119/CMP116's actual analytic J coordinates and differentiated
-- localized shell remains a named Y.02 physical source theorem.
-- Likewise the compact Borel one-link Haar realization, continuum,
-- physical clustering and Agda kernel acceptance are NOT inferred.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; _*ℝ_; _-ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Wilson
import DASHI.Physics.YangMills.YMClaySUNVariablePhysicalCutoffFamilyExact as Family
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : Nat → ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : ℝ → ℝ → ℝ)
  where

  OriginalLinks : Nat → Set
  OriginalLinks n = Wilson.SUNPeriodicLinks theory n

  OriginalObservable : Nat → Set
  OriginalObservable n = OriginalLinks n → ℝ

  originalWilsonMeasure :
    (n : Nat) → Physical.PhysicalFiniteYMMeasure (OriginalLinks n) ℝ
  originalWilsonMeasure =
    Family.physicalFiniteCutoffMeasure
      theory traceData exponential beta oneLink bilateral divide

  -- Y.01 source anchoring: the measure used by BOTH marked directions
  -- is the literal six-plane Wilson Gibbs density at each physical cutoff.
  originalWilsonDensityIsSelectedWilson :
    ∀ n links →
    Physical.density (originalWilsonMeasure n) links
    ≡ Wilson.periodicSUNGibbsDensity
        theory traceData exponential n (beta n) links
  originalWilsonDensityIsSelectedWilson =
    Family.physicalFiniteDensitySameWilson
      theory traceData exponential beta oneLink bilateral divide

  -- This proof is the actual partition identity already derived from one
  -- selected product-Haar source, not a fresh normalization axiom.
  originalWilsonPartitionIsSelectedProductHaar :
    ∀ n →
    Physical.partitionFunction (originalWilsonMeasure n)
    ≡
    (Physical.haarIntegral (originalWilsonMeasure n))
      (Wilson.periodicSUNGibbsDensity
        theory traceData exponential n (beta n))
  originalWilsonPartitionIsSelectedProductHaar n = refl

  originalWilsonExpectation :
    (n : Nat) → OriginalObservable n → ℝ
  originalWilsonExpectation n =
    Physical.normalizedExpectation (originalWilsonMeasure n)

  originalWilsonPair :
    (n : Nat) → OriginalObservable n → OriginalObservable n →
    OriginalObservable n
  originalWilsonPair n left right links = left links *ℝ right links

  -- The genuine n-varying Wilson observable algebra.  Its one- and
  -- two-point expectations are computed on the SAME actual finite measure.
  originalWilsonMomentAlgebra :
    (n : Nat) →
    Cumulant.TwoSourceMomentAlgebra (OriginalObservable n) ℝ
  originalWilsonMomentAlgebra n = record
    { Cumulant.TwoSourceMomentAlgebra.subtract = _-ℝ_
    ; Cumulant.TwoSourceMomentAlgebra.multiply = _*ℝ_
    ; Cumulant.TwoSourceMomentAlgebra.productObservable =
        originalWilsonPair n
    ; Cumulant.TwoSourceMomentAlgebra.expectation =
        originalWilsonExpectation n
    }

  -- Define coefficients of the normalized FORMAL two-source jet.
  -- This does not assume differentiation under a Haar integral.
  originalWilsonNormalizedJet :
    (n : Nat) →
    Cumulant.NormalizedLogSourceCalculus (originalWilsonMomentAlgebra n)
  originalWilsonNormalizedJet n = record
    { Cumulant.NormalizedLogSourceCalculus.firstSourceDerivative =
        originalWilsonExpectation n
    ; Cumulant.NormalizedLogSourceCalculus.mixedSecondSourceDerivative =
        λ left right →
          originalWilsonExpectation n (originalWilsonPair n left right)
    ; Cumulant.NormalizedLogSourceCalculus.mixedSecondLogDerivative =
        λ left right →
          originalWilsonExpectation n (originalWilsonPair n left right)
          -ℝ
          (originalWilsonExpectation n left
            *ℝ originalWilsonExpectation n right)
    ; Cumulant.NormalizedLogSourceCalculus.normalizedFirstDerivativeMeaning =
        λ observable → refl
    ; Cumulant.NormalizedLogSourceCalculus.normalizedMixedSecondDerivativeMeaning =
        λ left right → refl
    ; Cumulant.NormalizedLogSourceCalculus.normalizedLogHessianRule =
        λ left right → refl
    }

  -- The two source directions are THE ORIGINAL observables themselves.
  -- There is no arbitrary J-index type or extra equality premise.
  originalWilsonLiteralJetDirections :
    (n : Nat) →
    Cumulant.LiteralTwoSourceInsertionMeaning
      (originalWilsonNormalizedJet n) (OriginalObservable n)
  originalWilsonLiteralJetDirections n = record
    { Cumulant.LiteralTwoSourceInsertionMeaning.sourceDirectionOf =
        λ observable → observable
    ; Cumulant.LiteralTwoSourceInsertionMeaning.literalFirstDerivative =
        originalWilsonExpectation n
    ; Cumulant.LiteralTwoSourceInsertionMeaning.literalMixedSecondDerivative =
        λ left right →
          originalWilsonExpectation n (originalWilsonPair n left right)
    ; Cumulant.LiteralTwoSourceInsertionMeaning.literalMixedSecondLogDerivative =
        λ left right →
          originalWilsonExpectation n (originalWilsonPair n left right)
          -ℝ
          (originalWilsonExpectation n left
            *ℝ originalWilsonExpectation n right)
    ; Cumulant.LiteralTwoSourceInsertionMeaning.firstDirectionAgrees =
        λ observable → refl
    ; Cumulant.LiteralTwoSourceInsertionMeaning.secondDirectionAgrees =
        λ left right → refl
    ; Cumulant.LiteralTwoSourceInsertionMeaning.logSecondDirectionAgrees =
        λ left right → refl
    }

  originalWilsonMixedJetIsSameFiniteCovariance :
    ∀ n (left right : OriginalObservable n) →
    Cumulant.literalMixedSecondLogDerivative
      (originalWilsonLiteralJetDirections n)
      (Cumulant.sourceDirectionOf (originalWilsonLiteralJetDirections n) left)
      (Cumulant.sourceDirectionOf (originalWilsonLiteralJetDirections n) right)
    ≡
    (originalWilsonExpectation n (originalWilsonPair n left right)
      -ℝ
      (originalWilsonExpectation n left
        *ℝ originalWilsonExpectation n right))
  originalWilsonMixedJetIsSameFiniteCovariance n left right =
    Cumulant.literalMixedLogDerivativeIsConnectedCovariance
      (originalWilsonLiteralJetDirections n) left right

  -- An explicitly named second route checks that the selected covariance
  -- is the very same cumulant of the same finite Wilson moment algebra.
  originalWilsonMixedJetIsOriginalConnectedCumulant :
    ∀ n (left right : OriginalObservable n) →
    Cumulant.literalMixedSecondLogDerivative
      (originalWilsonLiteralJetDirections n)
      (Cumulant.sourceDirectionOf (originalWilsonLiteralJetDirections n) left)
      (Cumulant.sourceDirectionOf (originalWilsonLiteralJetDirections n) right)
    ≡ Cumulant.connectedCovariance
        (originalWilsonMomentAlgebra n) left right
  originalWilsonMixedJetIsOriginalConnectedCumulant n left right =
    Cumulant.literalMixedLogDerivativeIsConnectedCovariance
      (originalWilsonLiteralJetDirections n) left right

-- Audit boundary: this module supplies a closed formal finite-source jet,
-- not a physical CMP116 localization theorem or a Clay solution.
