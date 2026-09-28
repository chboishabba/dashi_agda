{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116LiteralTrajectoryToPublishedLiteralR467Exact where

------------------------------------------------------------------------
-- H1 DIRECT SOURCE COMPILER: R342 literal trajectory -> R467 published literal.
--
-- R342 and R467 carry the same two theorem-bearing physical facts:
--
--   * literal selected mixed-log localization on the common CMP116 domain;
--   * source envelope <= physical selected clustering envelope.
--
-- R342 additionally stores finite normalized demands and standard limit/order
-- structure.  R467 does not observe those.  Therefore an already-constructed
-- literal trajectory source is itself an inhabitant of the endpoint H1 ABI.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116CanonicalRadiusToCommonDomainRound114Exact as R114
import DASHI.Physics.YangMills.BalabanCMP116LiteralTrajectorySourceRound342Exact as R342
import DASHI.Physics.YangMills.BalabanCMP116PublishedLiteralSelectedRound467Exact as R467

asPublishedLiteralSelectedLocalization :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet extension base demands tests spectrumSource} →
  R342.LiteralTrajectoryCMP116Source
    {Measure = Measure}
    {TestObservable = TestObservable}
    {SpectralObservable = SpectralObservable}
    {Energy = Energy}
    {dataSet = dataSet}
    {extension = extension}
    base demands tests spectrumSource →
  R467.PublishedLiteralSelectedLocalization
    base tests spectrumSource
asPublishedLiteralSelectedLocalization
    {demands = demands}
    source = record
  { R467.PublishedLiteralSelectedLocalization.commonDomain =
      R114.canonicalCMP116CommonDomain demands
  ; R467.PublishedLiteralSelectedLocalization.sourceRoot =
      R342.sourceRoot source
  ; R467.PublishedLiteralSelectedLocalization.sourceDistance =
      R342.sourceDistance source
  ; R467.PublishedLiteralSelectedLocalization.sourceEnvelope =
      R342.sourceEnvelope source
  ; R467.PublishedLiteralSelectedLocalization.literalSelectedCMP116Localization =
      R342.literalSelectedDifferentiatedLocalization source
  ; R467.PublishedLiteralSelectedLocalization.sourceEnvelopeBelowPhysicalClusteringEnvelope =
      R342.sourceEnvelopeBelowSpectrumEnvelope source
  }

r342ToR467CompilerLevel : ProofLevel
r342ToR467CompilerLevel = machineChecked

-- No physical theorem is discharged here.  This proves only that the current
-- endpoint H1 record does not need a second inhabitant once the literal R342
-- source theorem has been proved.
r342ToR467AdditionalPhysicalPaymentLevel : ProofLevel
r342ToR467AdditionalPhysicalPaymentLevel = machineChecked
