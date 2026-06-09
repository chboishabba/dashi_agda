module DASHI.Physics.QFT.DHROriginalPaperAuthorityReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.DHRGaugeReceiptSurface as DHR
import DASHI.Physics.QFT.DHRHexagonObligation as Hexagon
import DASHI.Physics.QFT.DHRTensorDualGroupReconstruction as TensorDR
import DASHI.Physics.QFT.FinitePrimeLaneConjugateDualReceipts as Duals
import DASHI.Physics.QFT.FinitePrimeLaneDHRSMCompatibilityLedger as FiniteLedger

------------------------------------------------------------------------
-- DHR original-paper authority receipt.
--
-- This module records the original Doplicher-Haag-Roberts authority boundary
-- for localized endomorphisms and finite statistics.  It is literature
-- authority plus precondition accounting only: it does not apply a
-- reconstruction theorem, construct a compact gauge group, or identify any
-- reconstructed group with the Standard Model gauge group.

data DHROriginalPaperCitation : Set where
  dhr1971LocalObservablesAndParticleStatistics :
    DHROriginalPaperCitation

  dhr1974LocalObservablesAndParticleStatisticsPartII :
    DHROriginalPaperCitation

canonicalDHROriginalPaperCitations :
  List DHROriginalPaperCitation
canonicalDHROriginalPaperCitations =
  dhr1971LocalObservablesAndParticleStatistics
  ∷ dhr1974LocalObservablesAndParticleStatisticsPartII
  ∷ []

data DHROriginalTheoremBoundary : Set where
  symmetricMonoidalCStarCategoryOfLocalizedEndomorphismsWithFiniteStatistics :
    DHROriginalTheoremBoundary

  compactGaugeGroupReconstructionAuthorityBoundary :
    DHROriginalTheoremBoundary

  categoryEquivalenceToCompactGroupRepresentationsBoundary :
    DHROriginalTheoremBoundary

canonicalDHROriginalTheoremBoundaries :
  List DHROriginalTheoremBoundary
canonicalDHROriginalTheoremBoundaries =
  symmetricMonoidalCStarCategoryOfLocalizedEndomorphismsWithFiniteStatistics
  ∷ compactGaugeGroupReconstructionAuthorityBoundary
  ∷ categoryEquivalenceToCompactGroupRepresentationsBoundary
  ∷ []

data DHROriginalAuthorityBlocker : Set where
  blockedByNoArbitraryLocalizedEndomorphismCategoryLawInhabitants :
    DHROriginalAuthorityBlocker

  blockedByNoArbitrarySectorFiniteStatisticsProof :
    DHROriginalAuthorityBlocker

  blockedByNoTheoremApplicationInsideDASHI :
    DHROriginalAuthorityBlocker

  blockedByNoCompactGaugeGroupConstruction :
    DHROriginalAuthorityBlocker

  blockedByNoStandardModelGaugeIdentification :
    DHROriginalAuthorityBlocker

canonicalDHROriginalAuthorityBlockers :
  List DHROriginalAuthorityBlocker
canonicalDHROriginalAuthorityBlockers =
  blockedByNoArbitraryLocalizedEndomorphismCategoryLawInhabitants
  ∷ blockedByNoArbitrarySectorFiniteStatisticsProof
  ∷ blockedByNoTheoremApplicationInsideDASHI
  ∷ blockedByNoCompactGaugeGroupConstruction
  ∷ blockedByNoStandardModelGaugeIdentification
  ∷ []

record DHROriginalPaperAuthorityReceipt : Setω where
  field
    primary1971DOI :
      String

    primary1971DOIIsCanonical :
      primary1971DOI ≡ "10.1007/BF01877742"

    sequel1974DOI :
      String

    sequel1974DOIIsCanonical :
      sequel1974DOI ≡ "10.1007/BF01646454"

    citations :
      List DHROriginalPaperCitation

    citationsAreCanonical :
      citations ≡ canonicalDHROriginalPaperCitations

    theoremBoundary :
      List DHROriginalTheoremBoundary

    theoremBoundaryIsCanonical :
      theoremBoundary ≡ canonicalDHROriginalTheoremBoundaries

    theoremStatement :
      String

    theoremStatementIsScoped :
      theoremStatement
      ≡
      "symmetric-monoidal-C-star-category-of-localized-endomorphisms-with-finite-statistics-gives-compact-gauge-group-reconstruction-authority"

    dhrCategoryPrimitives :
      DHR.DHRCategoryPrimitiveSurface

    drHypotheses :
      DHR.DRHypothesesForDASHI

    finiteAxiomReceiptPack :
      DHR.DHRDRInternalAxiomReceiptPack

    finiteCarrierLocalisedEndomorphismReceipt :
      FiniteLedger.FinitePrimeLaneCarrierLevelLocalisedEndomorphismReceipt

    finitePrimeLaneNaturalityReceipt :
      FiniteLedger.FinitePrimeLaneDHRSMNaturalityReceipt

    finitePairSwapBraidingReceipt :
      FiniteLedger.FinitePrimeLanePairSwapBraidingNaturalityReceipt

    finiteLeftRightHexagonReceipt :
      Hexagon.DHRFinitePrimeLaneLeftRightHexagonCoherenceReceipt

    finiteStatisticsAsBraidingReceipt :
      TensorDR.FinitePrimeLaneStatisticsAsBraidingTargetReceipt

    finiteConjugateDualReceipt :
      Duals.FinitePrimeLaneConjugateDualReceipt

    finitePrimeLaneNaturalityReceiptThreadedFromPack :
      Bool

    finitePrimeLaneNaturalityReceiptThreadedFromPackIsTrue :
      finitePrimeLaneNaturalityReceiptThreadedFromPack ≡ true

    finitePrimeLaneNaturalityAvailable :
      Bool

    finitePrimeLaneNaturalityAvailableIsTrue :
      finitePrimeLaneNaturalityAvailable ≡ true

    finiteRowBraidingNaturalityThreaded :
      Bool

    finiteRowBraidingNaturalityThreadedIsTrue :
      finiteRowBraidingNaturalityThreaded ≡ true

    dhrOriginalAuthorityRecorded :
      Bool

    dhrOriginalAuthorityRecordedIsTrue :
      dhrOriginalAuthorityRecorded ≡ true

    internalFinitePrimeLanePreconditionsInhabited :
      Bool

    internalFinitePrimeLanePreconditionsInhabitedIsTrue :
      internalFinitePrimeLanePreconditionsInhabited ≡ true

    theoremAppliedHere :
      Bool

    theoremAppliedHereIsFalse :
      theoremAppliedHere ≡ false

    compactGaugeGroupConstructedHere :
      Bool

    compactGaugeGroupConstructedHereIsFalse :
      compactGaugeGroupConstructedHere ≡ false

    categoryEquivalenceToRepGPromoted :
      Bool

    categoryEquivalenceToRepGPromotedIsFalse :
      categoryEquivalenceToRepGPromoted ≡ false

    standardModelMatchingPromoted :
      Bool

    standardModelMatchingPromotedIsFalse :
      standardModelMatchingPromoted ≡ false

    blockers :
      List DHROriginalAuthorityBlocker

    blockersAreCanonical :
      blockers ≡ canonicalDHROriginalAuthorityBlockers

    firstBlocker :
      DHROriginalAuthorityBlocker

    firstBlockerIsArbitraryLocalizedEndomorphismCategoryLaws :
      firstBlocker
      ≡
      blockedByNoArbitraryLocalizedEndomorphismCategoryLawInhabitants

    authorityBoundary :
      List String

open DHROriginalPaperAuthorityReceipt public

canonicalDHROriginalPaperAuthorityReceipt :
  DHROriginalPaperAuthorityReceipt
canonicalDHROriginalPaperAuthorityReceipt =
  record
    { primary1971DOI =
        "10.1007/BF01877742"
    ; primary1971DOIIsCanonical =
        refl
    ; sequel1974DOI =
        "10.1007/BF01646454"
    ; sequel1974DOIIsCanonical =
        refl
    ; citations =
        canonicalDHROriginalPaperCitations
    ; citationsAreCanonical =
        refl
    ; theoremBoundary =
        canonicalDHROriginalTheoremBoundaries
    ; theoremBoundaryIsCanonical =
        refl
    ; theoremStatement =
        "symmetric-monoidal-C-star-category-of-localized-endomorphisms-with-finite-statistics-gives-compact-gauge-group-reconstruction-authority"
    ; theoremStatementIsScoped =
        refl
    ; dhrCategoryPrimitives =
        DHR.canonicalDHRCategoryPrimitiveSurface
    ; drHypotheses =
        DHR.canonicalDRHypothesesForDASHI
    ; finiteAxiomReceiptPack =
        DHR.canonicalDHRDRInternalAxiomReceiptPack
    ; finiteCarrierLocalisedEndomorphismReceipt =
        FiniteLedger.canonicalFinitePrimeLaneCarrierLevelLocalisedEndomorphismReceipt
    ; finitePrimeLaneNaturalityReceipt =
        DHR.DHRDRInternalAxiomReceiptPack.finitePrimeLaneNaturalityReceipt
          DHR.canonicalDHRDRInternalAxiomReceiptPack
    ; finitePairSwapBraidingReceipt =
        FiniteLedger.canonicalFinitePrimeLanePairSwapBraidingNaturalityReceipt
    ; finiteLeftRightHexagonReceipt =
        Hexagon.canonicalDHRFinitePrimeLaneLeftRightHexagonCoherenceReceipt
    ; finiteStatisticsAsBraidingReceipt =
        TensorDR.canonicalFinitePrimeLaneStatisticsAsBraidingTargetReceipt
    ; finiteConjugateDualReceipt =
        Duals.canonicalFinitePrimeLaneConjugateDualReceipt
    ; finitePrimeLaneNaturalityReceiptThreadedFromPack =
        true
    ; finitePrimeLaneNaturalityReceiptThreadedFromPackIsTrue =
        refl
    ; finitePrimeLaneNaturalityAvailable =
        FiniteLedger.FinitePrimeLaneDHRSMNaturalityReceipt.naturalityReceiptsAvailable
          FiniteLedger.canonicalFinitePrimeLaneDHRSMNaturalityReceipt
    ; finitePrimeLaneNaturalityAvailableIsTrue =
        FiniteLedger.FinitePrimeLaneDHRSMNaturalityReceipt.naturalityReceiptsAvailableIsTrue
          FiniteLedger.canonicalFinitePrimeLaneDHRSMNaturalityReceipt
    ; finiteRowBraidingNaturalityThreaded =
        DHR.DHRDRInternalAxiomReceiptPack.finiteRowBraidingNaturalityThreaded
          DHR.canonicalDHRDRInternalAxiomReceiptPack
    ; finiteRowBraidingNaturalityThreadedIsTrue =
        DHR.DHRDRInternalAxiomReceiptPack.finiteRowBraidingNaturalityThreadedIsTrue
          DHR.canonicalDHRDRInternalAxiomReceiptPack
    ; dhrOriginalAuthorityRecorded =
        true
    ; dhrOriginalAuthorityRecordedIsTrue =
        refl
    ; internalFinitePrimeLanePreconditionsInhabited =
        true
    ; internalFinitePrimeLanePreconditionsInhabitedIsTrue =
        refl
    ; theoremAppliedHere =
        false
    ; theoremAppliedHereIsFalse =
        refl
    ; compactGaugeGroupConstructedHere =
        false
    ; compactGaugeGroupConstructedHereIsFalse =
        refl
    ; categoryEquivalenceToRepGPromoted =
        false
    ; categoryEquivalenceToRepGPromotedIsFalse =
        refl
    ; standardModelMatchingPromoted =
        false
    ; standardModelMatchingPromotedIsFalse =
        refl
    ; blockers =
        canonicalDHROriginalAuthorityBlockers
    ; blockersAreCanonical =
        refl
    ; firstBlocker =
        blockedByNoArbitraryLocalizedEndomorphismCategoryLawInhabitants
    ; firstBlockerIsArbitraryLocalizedEndomorphismCategoryLaws =
        refl
    ; authorityBoundary =
        "DHR 1971 and DHR 1974 are recorded by DOI as original authority for localized transportable sectors and finite-statistics superselection structure"
        ∷ "The theorem statement is scoped to the authority boundary: a symmetric monoidal C*-category of localized endomorphisms with finite statistics is the input shape for compact gauge-group reconstruction and Rep(G)-style comparison"
        ∷ "Existing finite p2/p3/p5 DHR receipts are threaded explicitly: localised endomorphism/star, naturality, pair-swap braiding, left/right hexagon, statistics-as-braiding, and conjugate-dual zigzags"
        ∷ "This receipt does not apply the theorem, construct the compact gauge group, promote category equivalence to Rep(G), or identify G_DHR with the Standard Model gauge group"
        ∷ []
    }

canonicalDHROriginalAuthorityStillFailClosedForSM :
  DHROriginalPaperAuthorityReceipt.standardModelMatchingPromoted
    canonicalDHROriginalPaperAuthorityReceipt
  ≡
  false
canonicalDHROriginalAuthorityStillFailClosedForSM =
  refl
