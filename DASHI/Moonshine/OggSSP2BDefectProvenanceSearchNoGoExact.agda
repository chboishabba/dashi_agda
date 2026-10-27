module DASHI.Moonshine.OggSSP2BDefectProvenanceSearchNoGoExact where

------------------------------------------------------------------------
-- D PROVENANCE SEARCH MAX-CUT
--
-- The defect profile leaves four charts = two independent orientation bits.
-- Two natural p=2 donors were checked:
--
--   * oriented inertia: a DASHI-defined orientation-sheet x inertia-sector
--     construction whose own boundary explicitly refuses a Base369/Monster
--     semantic identity;
--   * Banerjee Galois class action: on the seven binary-tetrahedral classes the
--     Galois action equals inversion, so the five-orbit quotient is the same
--     quotient already used by the defect carrier.  Its retained sheet x five
--     presentation is explicitly not promoted to a source-native quotient.
--
-- Therefore neither donor source-selects either remaining CompletionMode5 ->
-- 2T orientation bit.  This file records that negative result without choosing
-- the repository's convenient but explicitly non-semantic finite indexing.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSP2BDefectTwoBitProvenanceSelectorExact as Bits
import DASHI.Moonshine.OggSSPP2OrientedInertiaModuliProblemExact as Oriented
import DASHI.Moonshine.OggSSPP2BanerjeeGaloisClassOrbitFiveExact as Galois

remainingSourceDecisionCount : Nat
remainingSourceDecisionCount = 2

remainingSourceDecisionCountIsTwo : remainingSourceDecisionCount ≡ 2
remainingSourceDecisionCountIsTwo = refl

orientedBase369SemanticIdentityClaimed : Bool
orientedBase369SemanticIdentityClaimed =
  Oriented.P2OrientedInertiaModuliProblemBoundary.base369SemanticIdentityClaimed
    Oriented.canonicalP2OrientedInertiaModuliProblemBoundary

orientedRouteDoesNotSourceSelectBits :
  orientedBase369SemanticIdentityClaimed ≡ false
orientedRouteDoesNotSourceSelectBits = refl

galoisRetainedTenPromotedToSourceNativeQuotient : Bool
galoisRetainedTenPromotedToSourceNativeQuotient =
  Galois.BanerjeeGaloisClassOrbitFiveBoundary.retainedTenPromotedToSourceNativeQuotient
    Galois.canonicalBanerjeeGaloisClassOrbitFiveBoundary

galoisRouteDoesNotSourceSelectBits :
  galoisRetainedTenPromotedToSourceNativeQuotient ≡ false
galoisRouteDoesNotSourceSelectBits = refl

provenanceChoiceCountStillFour : Bits.provenanceChoiceCount ≡ 4
provenanceChoiceCountStillFour = Bits.provenanceChoiceCountIsFour

record DefectProvenanceSearchStatus : Set where
  constructor defect-provenance-search-status
  field
    defectCompatibleCharts : Nat
    remainingIndependentSourceBits : Nat
    orientedInertiaRouteChecked : Bool
    orientedInertiaSourceSelectsBits : Bool
    galoisClassOrbitRouteChecked : Bool
    galoisClassOrbitSourceSelectsBits : Bool
    sourceSelectionPaid : Bool

canonicalDefectProvenanceSearchStatus : DefectProvenanceSearchStatus
canonicalDefectProvenanceSearchStatus =
  defect-provenance-search-status 4 2 true false true false false
