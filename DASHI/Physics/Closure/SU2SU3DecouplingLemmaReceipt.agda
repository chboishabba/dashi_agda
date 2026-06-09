module DASHI.Physics.Closure.SU2SU3DecouplingLemmaReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.LevelRankDualityReceipt as LevelRank
import DASHI.Physics.QFT.SMGaugeGroupFromCS3LanesReceipt as GaugeCS

------------------------------------------------------------------------
-- SU(2)-SU(3) decoupling lemma receipt.
--
-- This receipt records the user-supplied candidate mechanism for separating
-- the level-rank-dual SU(2)_3 <-> SU(3)_1 data after coupling to 3+1D
-- boundary matter.  The mechanism is symmetry-enriched topological (SET)
-- inequivalence induced by the lepton-quark split: leptons are SU(2)-charged
-- but SU(3)-neutral, so the SU(2)-enriched and SU(3)-enriched boundary
-- theories are not the same enriched theory.
--
-- This is a candidate lemma with citation authority, not a formal DASHI
-- derivation of the Standard Model gauge group.

data DecouplingLemmaStatus : Set where
  setInequivalenceCandidateFromLeptonBoundaryMatter :
    DecouplingLemmaStatus

data CandidateDerivedStatus : Set where
  candidate :
    CandidateDerivedStatus

  derived :
    CandidateDerivedStatus

data BoundaryFermionSector : Set where
  su2ChargedSu3NeutralLeptonSector :
    BoundaryFermionSector

  su2ChargedSu3TripletQuarkSector :
    BoundaryFermionSector

canonicalBoundaryFermionSectors :
  List BoundaryFermionSector
canonicalBoundaryFermionSectors =
  su2ChargedSu3NeutralLeptonSector
  ∷ su2ChargedSu3TripletQuarkSector
  ∷ []

data DecouplingAuthority : Set where
  barkeshliBondersonChengWang2019SETAuthority :
    DecouplingAuthority

  anomalyInflowBoundarySETAuthority :
    DecouplingAuthority

canonicalDecouplingAuthorities :
  List DecouplingAuthority
canonicalDecouplingAuthorities =
  barkeshliBondersonChengWang2019SETAuthority
  ∷ anomalyInflowBoundarySETAuthority
  ∷ []

data DecouplingPromotionToken : Set where

decouplingPromotionTokenImpossibleHere :
  DecouplingPromotionToken →
  ⊥
decouplingPromotionTokenImpossibleHere ()

decouplingLemmaLabel : String
decouplingLemmaLabel =
  "If boundary matter contains SU2-charged SU3-neutral leptons, the SU2_3 <-> SU3_1 level-rank identification becomes inequivalent as an SET and decouples only as a candidate 3+1D gauge-factor explanation"

setInequivalenceLabel : String
setInequivalenceLabel =
  "Lepton-quark charge split enriches the two level-rank descriptions differently; this records SET inequivalence, not an exact direct-product theorem"

authorityLabel : String
authorityLabel =
  "Candidate authority: Barkeshli-Bonderson-Cheng-Wang 2019 / anomaly-inflow and symmetry-enriched-topological-order boundary literature"

promotionBoundaryLabel : String
promotionBoundaryLabel =
  "SU2-SU3 decoupling is candidate-only; exact G_DHR ~= G_SM and terminal Standard Model promotion remain false"

canonicalSU2SU3DecouplingBoundary :
  List String
canonicalSU2SU3DecouplingBoundary =
  decouplingLemmaLabel
  ∷ setInequivalenceLabel
  ∷ authorityLabel
  ∷ promotionBoundaryLabel
  ∷ []

record SU2SU3DecouplingLemmaReceipt : Setω where
  field
    status :
      DecouplingLemmaStatus

    statusIsSETInequivalenceCandidate :
      status ≡ setInequivalenceCandidateFromLeptonBoundaryMatter

    levelRankReceipt :
      LevelRank.LevelRankDualityReceipt

    sharedLevelRankDataRecorded :
      LevelRank.LevelRankDualityReceipt.su2SpinAndSu3ColourFromSameCMRing
        levelRankReceipt
      ≡
      true

    gaugeCSReceipt :
      GaugeCS.SMGaugeGroupFromCS3LanesReceipt

    directProductStillMissingInInputReceipt :
      GaugeCS.SMGaugeGroupFromCS3LanesReceipt.directProductIndependenceConstructed
        gaugeCSReceipt
      ≡
      false

    boundaryFermionSectors :
      List BoundaryFermionSector

    boundaryFermionSectorsAreCanonical :
      boundaryFermionSectors ≡ canonicalBoundaryFermionSectors

    su2ChargedSu3NeutralLeptonsPresent :
      Bool

    su2ChargedSu3NeutralLeptonsPresentIsTrue :
      su2ChargedSu3NeutralLeptonsPresent ≡ true

    quarkLeptonChargeSplitInput :
      Bool

    quarkLeptonChargeSplitInputIsTrue :
      quarkLeptonChargeSplitInput ≡ true

    levelRankIdentificationAbstractTQFTOnly :
      Bool

    levelRankIdentificationAbstractTQFTOnlyIsTrue :
      levelRankIdentificationAbstractTQFTOnly ≡ true

    setInequivalenceMechanismRecorded :
      Bool

    setInequivalenceMechanismRecordedIsTrue :
      setInequivalenceMechanismRecorded ≡ true

    SETInequivalenceMechanism :
      Bool

    SETInequivalenceMechanismIsTrue :
      SETInequivalenceMechanism ≡ true

    anomalyInflowBoundaryMechanismRecorded :
      Bool

    anomalyInflowBoundaryMechanismRecordedIsTrue :
      anomalyInflowBoundaryMechanismRecorded ≡ true

    decouplingCandidate :
      Bool

    decouplingCandidateIsTrue :
      decouplingCandidate ≡ true

    su2Su3DecouplingFromLeptonQuarkSplit :
      Bool

    su2Su3DecouplingFromLeptonQuarkSplitIsTrue :
      su2Su3DecouplingFromLeptonQuarkSplit ≡ true

    decouplingLemmaInhabited :
      CandidateDerivedStatus

    decouplingLemmaInhabitedIsCandidate :
      decouplingLemmaInhabited ≡ candidate

    su2Su3DecoupledAt3p1DBoundary :
      CandidateDerivedStatus

    su2Su3DecoupledAt3p1DBoundaryIsCandidate :
      su2Su3DecoupledAt3p1DBoundary ≡ candidate

    decouplingDerived :
      Bool

    decouplingDerivedIsFalse :
      decouplingDerived ≡ false

    directProductGaugeGroupDerived :
      Bool

    directProductGaugeGroupDerivedIsFalse :
      directProductGaugeGroupDerived ≡ false

    gDHREqualsGSMPromoted :
      Bool

    gDHREqualsGSMPromotedIsFalse :
      gDHREqualsGSMPromoted ≡ false

    exactStandardModelPromoted :
      Bool

    exactStandardModelPromotedIsFalse :
      exactStandardModelPromoted ≡ false

    terminalSMPromotion :
      Bool

    terminalSMPromotionIsFalse :
      terminalSMPromotion ≡ false

    clayTerminalPromotion :
      Bool

    clayTerminalPromotionIsFalse :
      clayTerminalPromotion ≡ false

    authorities :
      List DecouplingAuthority

    authoritiesAreCanonical :
      authorities ≡ canonicalDecouplingAuthorities

    promotionTokens :
      List DecouplingPromotionToken

    promotionTokensAreEmpty :
      promotionTokens ≡ []

    lemmaStatement :
      String

    lemmaStatementIsCanonical :
      lemmaStatement ≡ decouplingLemmaLabel

    setInequivalenceStatement :
      String

    setInequivalenceStatementIsCanonical :
      setInequivalenceStatement ≡ setInequivalenceLabel

    authorityStatement :
      String

    authorityStatementIsCanonical :
      authorityStatement ≡ authorityLabel

    promotionBoundary :
      String

    promotionBoundaryIsCanonical :
      promotionBoundary ≡ promotionBoundaryLabel

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalSU2SU3DecouplingBoundary

open SU2SU3DecouplingLemmaReceipt public

canonicalSU2SU3DecouplingLemmaReceipt :
  SU2SU3DecouplingLemmaReceipt
canonicalSU2SU3DecouplingLemmaReceipt =
  record
    { status =
        setInequivalenceCandidateFromLeptonBoundaryMatter
    ; statusIsSETInequivalenceCandidate =
        refl
    ; levelRankReceipt =
        LevelRank.canonicalLevelRankDualityReceipt
    ; sharedLevelRankDataRecorded =
        refl
    ; gaugeCSReceipt =
        GaugeCS.canonicalSMGaugeGroupFromCS3LanesReceipt
    ; directProductStillMissingInInputReceipt =
        refl
    ; boundaryFermionSectors =
        canonicalBoundaryFermionSectors
    ; boundaryFermionSectorsAreCanonical =
        refl
    ; su2ChargedSu3NeutralLeptonsPresent =
        true
    ; su2ChargedSu3NeutralLeptonsPresentIsTrue =
        refl
    ; quarkLeptonChargeSplitInput =
        true
    ; quarkLeptonChargeSplitInputIsTrue =
        refl
    ; levelRankIdentificationAbstractTQFTOnly =
        true
    ; levelRankIdentificationAbstractTQFTOnlyIsTrue =
        refl
    ; setInequivalenceMechanismRecorded =
        true
    ; setInequivalenceMechanismRecordedIsTrue =
        refl
    ; SETInequivalenceMechanism =
        true
    ; SETInequivalenceMechanismIsTrue =
        refl
    ; anomalyInflowBoundaryMechanismRecorded =
        true
    ; anomalyInflowBoundaryMechanismRecordedIsTrue =
        refl
    ; decouplingCandidate =
        true
    ; decouplingCandidateIsTrue =
        refl
    ; su2Su3DecouplingFromLeptonQuarkSplit =
        true
    ; su2Su3DecouplingFromLeptonQuarkSplitIsTrue =
        refl
    ; decouplingLemmaInhabited =
        candidate
    ; decouplingLemmaInhabitedIsCandidate =
        refl
    ; su2Su3DecoupledAt3p1DBoundary =
        candidate
    ; su2Su3DecoupledAt3p1DBoundaryIsCandidate =
        refl
    ; decouplingDerived =
        false
    ; decouplingDerivedIsFalse =
        refl
    ; directProductGaugeGroupDerived =
        false
    ; directProductGaugeGroupDerivedIsFalse =
        refl
    ; gDHREqualsGSMPromoted =
        false
    ; gDHREqualsGSMPromotedIsFalse =
        refl
    ; exactStandardModelPromoted =
        false
    ; exactStandardModelPromotedIsFalse =
        refl
    ; terminalSMPromotion =
        false
    ; terminalSMPromotionIsFalse =
        refl
    ; clayTerminalPromotion =
        false
    ; clayTerminalPromotionIsFalse =
        refl
    ; authorities =
        canonicalDecouplingAuthorities
    ; authoritiesAreCanonical =
        refl
    ; promotionTokens =
        []
    ; promotionTokensAreEmpty =
        refl
    ; lemmaStatement =
        decouplingLemmaLabel
    ; lemmaStatementIsCanonical =
        refl
    ; setInequivalenceStatement =
        setInequivalenceLabel
    ; setInequivalenceStatementIsCanonical =
        refl
    ; authorityStatement =
        authorityLabel
    ; authorityStatementIsCanonical =
        refl
    ; promotionBoundary =
        promotionBoundaryLabel
    ; promotionBoundaryIsCanonical =
        refl
    ; receiptBoundary =
        canonicalSU2SU3DecouplingBoundary
    ; receiptBoundaryIsCanonical =
        refl
    }

su2su3DecouplingCandidateRecorded :
  decouplingCandidate canonicalSU2SU3DecouplingLemmaReceipt ≡ true
su2su3DecouplingCandidateRecorded =
  refl

su2su3DecouplingDerivedStillFalse :
  decouplingDerived canonicalSU2SU3DecouplingLemmaReceipt ≡ false
su2su3DecouplingDerivedStillFalse =
  refl

su2su3GDHREqualsGSMPromotionFalse :
  gDHREqualsGSMPromoted canonicalSU2SU3DecouplingLemmaReceipt ≡ false
su2su3GDHREqualsGSMPromotionFalse =
  refl

su2su3ClayTerminalPromotionFalse :
  clayTerminalPromotion canonicalSU2SU3DecouplingLemmaReceipt ≡ false
su2su3ClayTerminalPromotionFalse =
  refl
