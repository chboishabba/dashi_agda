{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanRationalCertificateFamilyToLiteralCMP109BoundsRound102Exact where

------------------------------------------------------------------------
-- ROUND102 A SOURCE WELD: FINITE RATIONAL CERTIFICATE -> ACTUAL CMP109 (5.42)
--
-- One history-uniform Ward/Gaussian/five-channel certificate gives fixed
-- rational slopes b/2 and B+b/2.  A canonical ordered Q->R embedding and one
-- SAME-object evaluator identity at each physical shell transport those slopes
-- to the exact `negativeOffDiagonalSecondMomentumDerivative` already carried by
-- `BalabanCutoffCouplingDynamics`.
--
-- This file therefore constructs the repository's existing literal pointwise
-- beta-bound record.  No second beta correspondence or real-valued estimate is
-- assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as ℕ

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCutoffBetaLaw as BetaLaw
import DASHI.Physics.YangMills.BalabanA1HistoryUniformTwoSidedBetaRound102Exact as Cert
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Real
import DASHI.Physics.YangMills.BalabanVacuumPolarisationPointwiseBetaBoundsExact as VP

record LiteralCMP109RationalCertificateFamily (History Cell : Set) : Set₁ where
  field
    embedding : Real.OrderedRationalRealEmbedding
    certificate : Cert.HistoryUniformTwoSidedBetaData History Cell
    historyWitness : History

    dynamics : (K : Nat) → BetaLaw.BalabanCutoffCouplingDynamics K

    historyForShell : ∀ K k → k ℕ.< K → History

    -- The certified rational beta evaluator is the SAME literal mixed derivative
    -- on every physical shell after canonical scalar embedding.
    mixedDerivativeExact : ∀ K k (k<K : k ℕ.< K) →
      BetaLaw.negativeOffDiagonalSecondMomentumDerivative
        (BetaLaw.vacuumPolarisationCoefficient (dynamics K)) k
      ≡ Real.embed embedding
          (Cert.beta certificate (historyForShell K k k<K))

open LiteralCMP109RationalCertificateFamily public

betaLowerReal :
  ∀ {History Cell} → LiteralCMP109RationalCertificateFamily History Cell → ℝ
betaLowerReal dataSet = Real.realLowerSlope (embedding dataSet) (certificate dataSet)

betaUpperReal :
  ∀ {History Cell} → LiteralCMP109RationalCertificateFamily History Cell → ℝ
betaUpperReal dataSet = Real.realUpperSlope (embedding dataSet) (certificate dataSet)

asShellRealCertificate :
  ∀ {History Cell}
    (dataSet : LiteralCMP109RationalCertificateFamily History Cell)
    K k (k<K : k ℕ.< K) →
  Real.LiteralRealBetaFromRationalCertificate
    (embedding dataSet) (certificate dataSet)
asShellRealCertificate dataSet K k k<K = record
  { Real.LiteralRealBetaFromRationalCertificate.historyForShell =
      historyForShell dataSet K k k<K
  ; Real.LiteralRealBetaFromRationalCertificate.literalMixedDerivative =
      BetaLaw.negativeOffDiagonalSecondMomentumDerivative
        (BetaLaw.vacuumPolarisationCoefficient (dynamics dataSet K)) k
  ; Real.LiteralRealBetaFromRationalCertificate.literalMixedDerivativeExact =
      mixedDerivativeExact dataSet K k k<K
  }

literalDerivativeBoundsForCutoff :
  ∀ {History Cell}
    (dataSet : LiteralCMP109RationalCertificateFamily History Cell)
    K →
  VP.LiteralVacuumPolarisationPointwiseBounds (dynamics dataSet K)
literalDerivativeBoundsForCutoff dataSet K = record
  { VP.LiteralVacuumPolarisationPointwiseBounds.betaLower = betaLowerReal dataSet
  ; VP.LiteralVacuumPolarisationPointwiseBounds.betaUpper = betaUpperReal dataSet
  ; VP.LiteralVacuumPolarisationPointwiseBounds.betaLowerPositive =
      Real.realLowerSlopePositive (embedding dataSet) (certificate dataSet)
  ; VP.LiteralVacuumPolarisationPointwiseBounds.betaLowerBelowUpper =
      Real.realLowerBelowUpperFromWitness
        (embedding dataSet) (certificate dataSet) (historyWitness dataSet)
  ; VP.LiteralVacuumPolarisationPointwiseBounds.derivativeLower =
      λ k k<K → Real.literalMixedDerivativeRealLower
        (asShellRealCertificate dataSet K k k<K)
  ; VP.LiteralVacuumPolarisationPointwiseBounds.derivativeUpper =
      λ k k<K → Real.literalMixedDerivativeRealUpper
        (asShellRealCertificate dataSet K k k<K)
  }

rationalCertificateFamilyToLiteralCMP109BoundsLevel : ProofLevel
rationalCertificateFamilyToLiteralCMP109BoundsLevel = machineChecked

-- The sole physical/source seam is `mixedDerivativeExact`: identify the finite
-- Ward/box/five-channel evaluator with the SAME CMP109 (5.42) mixed derivative.
-- All inequality transport is theorem-owned after that equality.
literalCMP109RationalEvaluatorSameObjectLevel : ProofLevel
literalCMP109RationalEvaluatorSameObjectLevel = conditional
