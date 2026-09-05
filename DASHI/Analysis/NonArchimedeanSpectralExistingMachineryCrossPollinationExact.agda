module DASHI.Analysis.NonArchimedeanSpectralExistingMachineryCrossPollinationExact where

------------------------------------------------------------------------
-- EXISTING REPO PRECEDENTS REUSED BY THE DYADIC LANE
--
-- 1. TriadicDepthTwoDFTGroupBridge proves that spectral coordinates are not an
--    arbitrary enumeration: the DFT index is round-trip equivalent to the
--    actual finite quotient carrier and respects addition.
--
-- 2. RiemannG2CanonicalHXToHTCompilerExact proves the proof-search pattern:
--    once the exact source carrier already owns the character-product law, a
--    historical intertwiner target is compiler output rather than a new theorem.
--
-- The dyadic lane imports these as architectural precedents only.  It does not
-- identify Z/9Z with Z/2^nZ and does not transport their numerical theorems.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.TriadicFiniteQuotient as Q
import DASHI.Algebra.TriadicFiniteIrrep as Irrep
import DASHI.Algebra.TriadicDepthTwoCyclotomicDFT as DFT9
import DASHI.Algebra.TriadicDepthTwoDFTGroupBridge as DFT9Group
import DASHI.Analysis.RiemannG2CanonicalHXToHTCompilerExact as HXHT

------------------------------------------------------------------------
-- Concrete checked precedent: exact spectral codec on genuine group labels.
------------------------------------------------------------------------

triadicGroupAlignedCodecWitness : Irrep.ExactSpectralCodec Q.two
triadicGroupAlignedCodecWitness = DFT9Group.groupAlignedDepthTwoCodec

triadicIndexRoundTripWitness :
  (i : DFT9.Index9) →
  DFT9Group.residueToIndex (DFT9Group.indexToResidue i) ≡ i
triadicIndexRoundTripWitness = DFT9Group.indexRoundTrip

------------------------------------------------------------------------
-- Concrete checked precedent: once the same source object owns the required
-- character law, rebuilding the historical intertwiner is explicitly pruned.
------------------------------------------------------------------------

riemannDuplicateIntertwinerRebuildIsPruned :
  HXHT.searchStatus HXHT.rebuildTranslationModulationIntertwiner ≡ HXHT.pruned
riemannDuplicateIntertwinerRebuildIsPruned = HXHT.htRebuildPruned

------------------------------------------------------------------------
-- What transfers and what does not.
------------------------------------------------------------------------

record ExistingMachineryCrossPollinationBoundary : Set where
  constructor existingMachineryCrossPollinationBoundary
  field
    exactGroupLabellingPatternTransfers : Bool
    exactCodecRoundTripPatternTransfers : Bool
    sameObjectCompilerPatternTransfers : Bool

    triadicCarrierEqualsDyadicCarrier : Bool
    triadicCyclotomicValuesTransferNumerically : Bool
    riemannCharacterTheoremProvesDyadicCharacterAction : Bool

canonicalExistingMachineryCrossPollinationBoundary :
  ExistingMachineryCrossPollinationBoundary
canonicalExistingMachineryCrossPollinationBoundary =
  existingMachineryCrossPollinationBoundary
    true
    true
    true
    false
    false
    false
