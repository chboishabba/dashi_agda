{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCanonicalBUrsellDonorBidiExact where

------------------------------------------------------------------------
-- CANONICAL-B BURIED DONOR: OLD URSELL CAUCHY -> R275 SUBGAP CONSUMER
--
-- This owner does not change the canonical B theorem.  It records one optional
-- producer discovered by archaeology and compiles it into the already-minimal
-- R275 payment.  The old Ursell theorem supplies quantitative decay; the only
-- new source-facing seam is the exact same-family representation of the
-- subgap-selected Euclidean-time correlation and its support separation.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT2UrsellCauchyExact as Ursell
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound275Exact as R275
import DASHI.Physics.YangMills.BalabanUrsellToSubgapClusteringUpperBidiExact as Bridge

record CanonicalBUrsellProducer
    {UrsellObservable Observable Energy Bound : Set}
    (ursell : Ursell.InfiniteUrsellLimit UrsellObservable Data.Rational.ℚ)
    (spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound)
    : Set₁ where
  field
    adapter : Bridge.UrsellSubgapAdapter ursell spectrum
    candidatePositive : Gap.PositiveEnergy spectrum (Gap.gapCandidate spectrum)

open CanonicalBUrsellProducer public

ursellDonorBuildsCanonicalBPayment :
  ∀ {UrsellObservable Observable Energy Bound}
    {ursell : Ursell.InfiniteUrsellLimit UrsellObservable Data.Rational.ℚ}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound} →
  CanonicalBUrsellProducer ursell spectrum →
  R275.CanonicalBPayment275 spectrum
ursellDonorBuildsCanonicalBPayment producer = record
  { subgapClusteringUpper =
      Bridge.ursellProducesSubgapModeClusteringUpper (adapter producer)
  ; candidatePositive = candidatePositive producer
  }

ursellDonorBuildsPositiveTransferGapCore :
  ∀ {UrsellObservable Observable Energy Bound}
    {ursell : Ursell.InfiniteUrsellLimit UrsellObservable Data.Rational.ℚ}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound} →
  CanonicalBUrsellProducer ursell spectrum →
  Gap.PositiveTransferGapCore spectrum
ursellDonorBuildsPositiveTransferGapCore producer =
  R275.compileCanonicalBPaymentCore (ursellDonorBuildsCanonicalBPayment producer)

------------------------------------------------------------------------
-- Classification: the bridge/compiler is closed structurally; the producer
-- remains conditional exactly where the old Ursell physical majorant and the
-- same-family representation weld remain conditional.
------------------------------------------------------------------------

canonicalBUrsellCompilerLevel : ProofLevel
canonicalBUrsellCompilerLevel = machineChecked

physicalUrsellMajorantLevel : ProofLevel
physicalUrsellMajorantLevel = Ursell.physicalUrsellTreeGraphMajorantLevel

subgapSameFamilyUrsellWeldLevel : ProofLevel
subgapSameFamilyUrsellWeldLevel = Bridge.ursellToSubgapRepresentationWeldLevel
