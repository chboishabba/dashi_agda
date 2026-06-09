module DASHI.Physics.QFT.SpinStatisticsConnectionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.BraidingMorphismReceipt as Braiding
import DASHI.Physics.QFT.ConditionalGDHRSMPromotionReceipt as Conditional
import DASHI.Physics.QFT.DHRGaugeReceiptSurface as DHR
import DASHI.Physics.QFT.DiracSpinSectorReceipt as Dirac

------------------------------------------------------------------------
-- DHR spin-statistics connection receipt.
--
-- This receipt consumes the current finite CM-character braiding diagnostic:
-- the p2/p3/p5 prime-lane sectors support only symmetric bosonic swaps at
-- this surface.  It records the DHR spin-statistics consequence without
-- promoting those finite CM characters to fundamental fermion
-- representations, and without promoting G_DHR ~= G_SM or full arbitrary DHR.

data SpinStatisticsConclusionKind : Set where
  primeLaneBosonicCMCharacterConclusion :
    SpinStatisticsConclusionKind

  diracSpinSectorRequiredConclusion :
    SpinStatisticsConclusionKind

  fullDHRPromotionNotClaimedConclusion :
    SpinStatisticsConclusionKind

data FundamentalFermionRepresentationPromotion : Set where

fundamentalFermionRepresentationPromotionImpossibleHere :
  FundamentalFermionRepresentationPromotion →
  ⊥
fundamentalFermionRepresentationPromotionImpossibleHere ()

canonicalSpinStatisticsBoundary : List String
canonicalSpinStatisticsBoundary =
  "The finite p2/p3/p5 prime-lane sectors are recorded as bosonic CM-character sectors"
  ∷ "They are not recorded as fundamental fermion representations"
  ∷ "A separate Dirac spin sector is required for physical fermions"
  ∷ "No Standard Model or full arbitrary-DHR promotion is made here"
  ∷ []

record SpinStatisticsConnectionReceipt : Setω where
  field
    finiteCMBraidingDiagnostic :
      Braiding.BraidingMorphismReceipt

    conditionalGDHRSMPromotionReceipt :
      Conditional.ConditionalGDHRSMPromotionReceipt

    dhrSymmetricTensorStarCategoryReceipt :
      DHR.DRH1SymmetricTensorStarCategory

    diracSpinSectorCandidate :
      Dirac.DiracSpinSectorReceipt

    diracSpinSectorCandidateIsFermionic :
      Dirac.fermionicByConstruction diracSpinSectorCandidate ≡ true

    diracSpinSectorCandidateHasNoFullPromotion :
      Dirac.fullPromotion diracSpinSectorCandidate ≡ false

    p2p3Statistics :
      Braiding.FiniteBraidingStatisticsKind

    p2p3StatisticsIsBosonicSwap :
      p2p3Statistics ≡ Braiding.bosonicTrivialSymmetricSwap

    finitePrimeLaneBosonicSurfaceInhabited :
      Bool

    finitePrimeLaneBosonicSurfaceInhabitedIsTrue :
      finitePrimeLaneBosonicSurfaceInhabited ≡ true

    primeLaneSectorsAreBosonicCMChars :
      Bool

    primeLaneSectorsAreBosonicCMCharsIsTrue :
      primeLaneSectorsAreBosonicCMChars ≡ true

    primeLaneSectorsAreFundamentalFermionReps :
      Bool

    primeLaneSectorsAreFundamentalFermionRepsIsFalse :
      primeLaneSectorsAreFundamentalFermionReps ≡ false

    diracSpinSectorRequired :
      Bool

    diracSpinSectorRequiredIsTrue :
      diracSpinSectorRequired ≡ true

    fermionicMinusOneSectorIntroducedByPrimeLanes :
      Bool

    fermionicMinusOneSectorIntroducedByPrimeLanesIsFalse :
      fermionicMinusOneSectorIntroducedByPrimeLanes ≡ false

    dhrBosonicStatisticsOutput :
      DHR.DoplicherRobertsGaugeOutputKind

    dhrBosonicStatisticsOutputIsCompactGroup :
      dhrBosonicStatisticsOutput ≡ DHR.compactGroupOutput

    dhrFermionicStatisticsOutput :
      DHR.DoplicherRobertsGaugeOutputKind

    dhrFermionicStatisticsOutputIsCompactSupergroup :
      dhrFermionicStatisticsOutput ≡ DHR.compactSupergroupOutput

    noFundamentalFermionRepPromotion :
      FundamentalFermionRepresentationPromotion → ⊥

    gDHREqualsGSMPromoted :
      Bool

    gDHREqualsGSMPromotedIsFalse :
      gDHREqualsGSMPromoted ≡ false

    fullDHRSMTheoremClaimed :
      Bool

    fullDHRSMTheoremClaimedIsFalse :
      fullDHRSMTheoremClaimed ≡ false

    conclusionOrder :
      List SpinStatisticsConclusionKind

    conclusionOrderIsCanonical :
      conclusionOrder
      ≡
      primeLaneBosonicCMCharacterConclusion
      ∷ diracSpinSectorRequiredConclusion
      ∷ fullDHRPromotionNotClaimedConclusion
      ∷ []

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalSpinStatisticsBoundary

open SpinStatisticsConnectionReceipt public

canonicalSpinStatisticsConnectionReceipt :
  SpinStatisticsConnectionReceipt
canonicalSpinStatisticsConnectionReceipt =
  record
    { finiteCMBraidingDiagnostic =
        Braiding.canonicalBraidingMorphismReceipt
    ; conditionalGDHRSMPromotionReceipt =
        Conditional.canonicalConditionalGDHRSMPromotionReceipt
    ; dhrSymmetricTensorStarCategoryReceipt =
        DHR.canonicalDRH1SymmetricTensorStarCategory
    ; diracSpinSectorCandidate =
        Dirac.canonicalDiracSpinSectorReceipt
    ; diracSpinSectorCandidateIsFermionic =
        Dirac.diracSpinSectorIsFermionicByConstruction
    ; diracSpinSectorCandidateHasNoFullPromotion =
        Dirac.diracSpinSectorNoFullPromotion
    ; p2p3Statistics =
        Braiding.p2p3Statistics Braiding.canonicalBraidingMorphismReceipt
    ; p2p3StatisticsIsBosonicSwap =
        Braiding.p2p3StatisticsIsBosonicSwap
          Braiding.canonicalBraidingMorphismReceipt
    ; finitePrimeLaneBosonicSurfaceInhabited =
        Braiding.finitePrimeLaneBosonicSurfaceInhabited
          Braiding.canonicalBraidingMorphismReceipt
    ; finitePrimeLaneBosonicSurfaceInhabitedIsTrue =
        Braiding.finitePrimeLaneBosonicSurfaceInhabitedIsTrue
          Braiding.canonicalBraidingMorphismReceipt
    ; primeLaneSectorsAreBosonicCMChars =
        true
    ; primeLaneSectorsAreBosonicCMCharsIsTrue =
        refl
    ; primeLaneSectorsAreFundamentalFermionReps =
        false
    ; primeLaneSectorsAreFundamentalFermionRepsIsFalse =
        refl
    ; diracSpinSectorRequired =
        true
    ; diracSpinSectorRequiredIsTrue =
        refl
    ; fermionicMinusOneSectorIntroducedByPrimeLanes =
        Braiding.fermionicMinusOneSectorIntroduced
          Braiding.canonicalBraidingMorphismReceipt
    ; fermionicMinusOneSectorIntroducedByPrimeLanesIsFalse =
        Braiding.fermionicMinusOneSectorIntroducedIsFalse
          Braiding.canonicalBraidingMorphismReceipt
    ; dhrBosonicStatisticsOutput =
        DHR.canonicalDRStatisticsOutputKind DHR.bosonicStatistics
    ; dhrBosonicStatisticsOutputIsCompactGroup =
        refl
    ; dhrFermionicStatisticsOutput =
        DHR.canonicalDRStatisticsOutputKind DHR.fermionicStatistics
    ; dhrFermionicStatisticsOutputIsCompactSupergroup =
        refl
    ; noFundamentalFermionRepPromotion =
        fundamentalFermionRepresentationPromotionImpossibleHere
    ; gDHREqualsGSMPromoted =
        Conditional.unconditionalGDHREqualsGSMPromoted
          Conditional.canonicalConditionalGDHRSMPromotionReceipt
    ; gDHREqualsGSMPromotedIsFalse =
        Conditional.unconditionalGDHREqualsGSMPromotedIsFalse
          Conditional.canonicalConditionalGDHRSMPromotionReceipt
    ; fullDHRSMTheoremClaimed =
        Conditional.fullTheoremInRepoClaimed
          Conditional.canonicalConditionalGDHRSMPromotionReceipt
    ; fullDHRSMTheoremClaimedIsFalse =
        Conditional.fullTheoremInRepoClaimedIsFalse
          Conditional.canonicalConditionalGDHRSMPromotionReceipt
    ; conclusionOrder =
        primeLaneBosonicCMCharacterConclusion
        ∷ diracSpinSectorRequiredConclusion
        ∷ fullDHRPromotionNotClaimedConclusion
        ∷ []
    ; conclusionOrderIsCanonical =
        refl
    ; receiptBoundary =
        canonicalSpinStatisticsBoundary
    ; receiptBoundaryIsCanonical =
        refl
    }

primeLaneSectorsAreNotFundamentalFermionReps :
  SpinStatisticsConnectionReceipt.primeLaneSectorsAreFundamentalFermionReps
    canonicalSpinStatisticsConnectionReceipt
  ≡
  false
primeLaneSectorsAreNotFundamentalFermionReps =
  refl

spinStatisticsConnectionDoesNotPromoteGSM :
  SpinStatisticsConnectionReceipt.gDHREqualsGSMPromoted
    canonicalSpinStatisticsConnectionReceipt
  ≡
  false
spinStatisticsConnectionDoesNotPromoteGSM =
  refl

spinStatisticsConnectionDoesNotClaimFullDHRSM :
  SpinStatisticsConnectionReceipt.fullDHRSMTheoremClaimed
    canonicalSpinStatisticsConnectionReceipt
  ≡
  false
spinStatisticsConnectionDoesNotClaimFullDHRSM =
  refl
