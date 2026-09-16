{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanDirectSelectedUpperToGapFinalExact where

------------------------------------------------------------------------
-- FINAL CURRENT-MASTER TERMINAL COMPILER
--
-- Current master already owns the least-privilege terminal source ABI:
--
--   R387.DirectSelectedSpectralUpper
--
-- whose sole theorem-bearing YM field is the exact selected finite mixed-log
-- response below the selected spectral clustering envelope.  R387 compiles that
-- field through the exact finite covariance identity and the selected
-- finite-to-continuum order closure into the existing subgap-mode clustering
-- upper.  The current transfer-gap owner then turns that mode-indexed upper plus
-- positivity of the selected candidate gap into PositiveTransferGapCore.
--
-- This file only composes those already-existing theorem owners.  It introduces
-- no new decay estimate, source envelope, CMP99/CMP109 factor replay, or
-- Hamiltonian assertion.  In particular R410 is an optional stronger
-- provenance/source-replay route, not a terminal dependency.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanCMP116R281SourceResponseSameObjectRound342Exact as R342
import DASHI.Physics.YangMills.BalabanCMP116DirectSelectedSpectralUpperRound387Exact as R387
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

/-- The shortest current-master terminal theorem compiler.

A direct selected finite mixed-log upper, the already-imported selected limit
closure, and positivity of the selected candidate gap produce the actual
least-privilege positive transfer-gap core.  No R410 source factor replay is an
input. -/
directSelectedUpperBuildsPositiveTransferGapCore :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  R387.DirectSelectedSpectralUpper base tests spectrumSource →
  R342.SelectedLimitUpperClosure {dataSet = dataSet} →
  Gap.PositiveEnergy
    (R281.asReconstructedClusteringSpectrum spectrumSource)
    (Gap.gapCandidate (R281.asReconstructedClusteringSpectrum spectrumSource)) →
  Gap.PositiveTransferGapCore
    (R281.asReconstructedClusteringSpectrum spectrumSource)
directSelectedUpperBuildsPositiveTransferGapCore
    {spectrumSource = spectrumSource} direct limitClosure positiveGap =
  Gap.positiveTransferGapCoreFromModeTests
    (R281.asReconstructedClusteringSpectrum spectrumSource)
    (R387.directSelectedSpectralUpperBuildsSubgapUpper direct limitClosure)
    positiveGap

finalDirectUpperCompilerWritten : Bool
finalDirectUpperCompilerWritten = true

finalDirectUpperCompilerWrittenIsTrue :
  finalDirectUpperCompilerWritten ≡ true
finalDirectUpperCompilerWrittenIsTrue = refl

r410MandatoryForTerminalGap : Bool
r410MandatoryForTerminalGap = false

r410MandatoryForTerminalGapIsFalse :
  r410MandatoryForTerminalGap ≡ false
r410MandatoryForTerminalGapIsFalse = refl

sourceEnvelopeMandatoryForTerminalGap : Bool
sourceEnvelopeMandatoryForTerminalGap = false

sourceEnvelopeMandatoryForTerminalGapIsFalse :
  sourceEnvelopeMandatoryForTerminalGap ≡ false
sourceEnvelopeMandatoryForTerminalGapIsFalse = refl

-- Source is written, but this connector session has not observed an Agda kernel
-- check for the exact feature-branch head.  Keep the local proof level
-- non-promotable until an actual receipt exists.
finalDirectUpperCompilerLevel : ProofLevel
finalDirectUpperCompilerLevel = conditional

finalDirectUpperKernelCertifiedAtCurrentHead : Bool
finalDirectUpperKernelCertifiedAtCurrentHead = false

finalDirectUpperKernelCertifiedAtCurrentHeadIsFalse :
  finalDirectUpperKernelCertifiedAtCurrentHead ≡ false
finalDirectUpperKernelCertifiedAtCurrentHeadIsFalse = refl

-- This is a compiler level only.  The direct selected YM upper itself retains
-- R387's conditional physical/source status until an actual producer inhabits
-- that one theorem field.
directSelectedUpperPhysicalProducerLevel : ProofLevel
directSelectedUpperPhysicalProducerLevel = R387.round387DirectSelectedUpperLevel

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
