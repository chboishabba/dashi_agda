module DASHI.Physics.QFT.LevelRankDecouplingReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.LevelRankDualityReceipt as LevelRank
import DASHI.Physics.QFT.SMGaugeGroupFromCS3LanesReceipt as GaugeCS

------------------------------------------------------------------------
-- Level-rank decoupling candidate receipt.
--
-- This receipt records the proposed representation-theoretic way to separate
-- SU(2)-like and SU(3)-like factors after they have appeared from shared
-- level-rank Chern-Simons data: inspect their action on 3+1D matter
-- representations.  The argument is candidate-only and is not derived here.
--
-- No direct-product independence theorem, exact physical gauge group, exact
-- Standard Model, G_DHR ~= G_SM, or terminal promotion is asserted.

data DecouplingMethod : Set where
  matterRepresentationDecoupling :
    DecouplingMethod

data SpacetimeRepresentationStatus : Set where
  fourDimensionalMatterRepCandidate :
    SpacetimeRepresentationStatus

data DecouplingDerivationStatus : Set where
  candidateNotDerived :
    DecouplingDerivationStatus

data MatterRepresentationChannel : Set where
  weakDoubletChannel :
    MatterRepresentationChannel

  colourTripletChannel :
    MatterRepresentationChannel

  hyperchargeCharacterChannel :
    MatterRepresentationChannel

canonicalMatterRepresentationChannels :
  List MatterRepresentationChannel
canonicalMatterRepresentationChannels =
  weakDoubletChannel
  ∷ colourTripletChannel
  ∷ hyperchargeCharacterChannel
  ∷ []

decouplingCandidateLabel : String
decouplingCandidateLabel =
  "Candidate decoupling: distinguish level-rank SU(2) and SU(3) data by their 3+1D matter representation actions"

notDerivedLabel : String
notDerivedLabel =
  "The representation-theoretic decoupling is recorded as a candidate and is not derived in this receipt"

directProductStillOpenLabel : String
directProductStillOpenLabel =
  "Direct-product independence remains open until the matter-representation decoupling is proved"

record LevelRankDecouplingReceipt : Setω where
  field
    levelRankReceipt :
      LevelRank.LevelRankDualityReceipt

    sharedLevelRankDataIsCandidate :
      LevelRank.LevelRankDualityReceipt.su2SpinAndSu3ColourFromSameCMRing
        levelRankReceipt
      ≡
      true

    smGaugeCS3LanesReceipt :
      GaugeCS.SMGaugeGroupFromCS3LanesReceipt

    directProductIndependenceNeeded :
      GaugeCS.SMGaugeGroupFromCS3LanesReceipt.directProductIndependenceConstructed
        smGaugeCS3LanesReceipt
      ≡
      false

    method :
      DecouplingMethod

    methodIsMatterRepresentationDecoupling :
      method ≡ matterRepresentationDecoupling

    representationStatus :
      SpacetimeRepresentationStatus

    representationStatusIs4DMatterRepCandidate :
      representationStatus ≡ fourDimensionalMatterRepCandidate

    matterRepresentationChannels :
      List MatterRepresentationChannel

    matterRepresentationChannelsAreCanonical :
      matterRepresentationChannels ≡ canonicalMatterRepresentationChannels

    candidateDecouplingStatement :
      String

    candidateDecouplingStatementIsCanonical :
      candidateDecouplingStatement ≡ decouplingCandidateLabel

    representationTheoreticDecouplingCandidate :
      Bool

    representationTheoreticDecouplingCandidateIsTrue :
      representationTheoreticDecouplingCandidate ≡ true

    decouplingDerivationStatus :
      DecouplingDerivationStatus

    decouplingDerivationStatusIsCandidateNotDerived :
      decouplingDerivationStatus ≡ candidateNotDerived

    derivedInThisReceipt :
      Bool

    derivedInThisReceiptIsFalse :
      derivedInThisReceipt ≡ false

    notDerivedStatement :
      String

    notDerivedStatementIsCanonical :
      notDerivedStatement ≡ notDerivedLabel

    directProductIndependenceProved :
      Bool

    directProductIndependenceProvedIsFalse :
      directProductIndependenceProved ≡ false

    directProductStillOpenStatement :
      String

    directProductStillOpenStatementIsCanonical :
      directProductStillOpenStatement ≡ directProductStillOpenLabel

    exactPhysicalGaugeGroup :
      Bool

    exactPhysicalGaugeGroupIsFalse :
      exactPhysicalGaugeGroup ≡ false

    exactStandardModel :
      Bool

    exactStandardModelIsFalse :
      exactStandardModel ≡ false

    exactGDHREqualsGSM :
      Bool

    exactGDHREqualsGSMIsFalse :
      exactGDHREqualsGSM ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    receiptBoundary :
      List String

open LevelRankDecouplingReceipt public

canonicalLevelRankDecouplingReceipt :
  LevelRankDecouplingReceipt
canonicalLevelRankDecouplingReceipt =
  record
    { levelRankReceipt =
        LevelRank.canonicalLevelRankDualityReceipt
    ; sharedLevelRankDataIsCandidate =
        refl
    ; smGaugeCS3LanesReceipt =
        GaugeCS.canonicalSMGaugeGroupFromCS3LanesReceipt
    ; directProductIndependenceNeeded =
        refl
    ; method =
        matterRepresentationDecoupling
    ; methodIsMatterRepresentationDecoupling =
        refl
    ; representationStatus =
        fourDimensionalMatterRepCandidate
    ; representationStatusIs4DMatterRepCandidate =
        refl
    ; matterRepresentationChannels =
        canonicalMatterRepresentationChannels
    ; matterRepresentationChannelsAreCanonical =
        refl
    ; candidateDecouplingStatement =
        decouplingCandidateLabel
    ; candidateDecouplingStatementIsCanonical =
        refl
    ; representationTheoreticDecouplingCandidate =
        true
    ; representationTheoreticDecouplingCandidateIsTrue =
        refl
    ; decouplingDerivationStatus =
        candidateNotDerived
    ; decouplingDerivationStatusIsCandidateNotDerived =
        refl
    ; derivedInThisReceipt =
        false
    ; derivedInThisReceiptIsFalse =
        refl
    ; notDerivedStatement =
        notDerivedLabel
    ; notDerivedStatementIsCanonical =
        refl
    ; directProductIndependenceProved =
        false
    ; directProductIndependenceProvedIsFalse =
        refl
    ; directProductStillOpenStatement =
        directProductStillOpenLabel
    ; directProductStillOpenStatementIsCanonical =
        refl
    ; exactPhysicalGaugeGroup =
        false
    ; exactPhysicalGaugeGroupIsFalse =
        refl
    ; exactStandardModel =
        false
    ; exactStandardModelIsFalse =
        refl
    ; exactGDHREqualsGSM =
        false
    ; exactGDHREqualsGSMIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; receiptBoundary =
        "A representation-theoretic 3+1D matter-rep decoupling route is recorded"
        ∷ "The route is candidate-only and is not derived here"
        ∷ "Direct-product independence, exact gauge group, exact SM, and terminal promotions remain false"
        ∷ []
    }

levelRankDecouplingCandidateTrue :
  representationTheoreticDecouplingCandidate
    canonicalLevelRankDecouplingReceipt
  ≡
  true
levelRankDecouplingCandidateTrue =
  refl

levelRankDecouplingDerivedFalse :
  derivedInThisReceipt canonicalLevelRankDecouplingReceipt
  ≡
  false
levelRankDecouplingDerivedFalse =
  refl

levelRankDecouplingDirectProductProvedFalse :
  directProductIndependenceProved canonicalLevelRankDecouplingReceipt
  ≡
  false
levelRankDecouplingDirectProductProvedFalse =
  refl
