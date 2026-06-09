module DASHI.Physics.Closure.MixedParticleClaimPacketReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.AnyonicSectorPhysicsReceipt as Anyon

------------------------------------------------------------------------
-- Mixed particle-claim packet receipt.
--
-- This receipt separates three claim lanes that are often collapsed in
-- social/news summaries:
--
--   * 2026 CERN/LHCb Xi_cc+ is one new doubly charmed baryon, a QCD
--     spectroscopy datum;
--   * the "three exotic particles" wording belongs to the older 2022 LHCb
--     tetraquark/pentaquark cluster;
--   * one-dimensional anyons are low-dimensional exchange-statistics
--     theory/quasiparticle sectors, not collider discoveries.
--
-- The receipt is empirical/theoretical claim governance only.  It records
-- narrow supported promotions and keeps new-force, Standard-Model-rewrite,
-- elementary-particle, and LHC-anyon promotions impossible here.

data ClaimSource : Set where
  cernHomeLHCbXiCCPlus20260317 :
    ClaimSource

  lhcbOutreachExoticHadrons20220705 :
    ClaimSource

  oistOneDAnyon20260203 :
    ClaimSource

data ClaimDate : Set where
  date20260317 :
    ClaimDate

  date20220705 :
    ClaimDate

  date20260203 :
    ClaimDate

data ClaimSystem : Set where
  upgradedLHCbDetector :
    ClaimSystem

  lhcbColliderReconstruction :
    ClaimSystem

  lowDimensionalQuantumModel :
    ClaimSystem

data EntityKind : Set where
  elementaryParticle :
    EntityKind

  conventionalHadron :
    EntityKind

  exoticHadron :
    EntityKind

  quasiparticle :
    EntityKind

  statisticalSector :
    EntityKind

data ObservationStatus : Set where
  unsupported :
    ObservationStatus

  openStatus :
    ObservationStatus

  supported :
    ObservationStatus

data TheoryLane : Set where
  QCDSpectroscopy :
    TheoryLane

  StrongForceBinding :
    TheoryLane

  ExchangeStatistics :
    TheoryLane

  BeyondStandardModel :
    TheoryLane

data Promotion : Set where
  QCDConstraint :
    Promotion

  HadronSpectrumExtension :
    Promotion

  ExoticBindingEvidence :
    Promotion

  TunableExchangeStatistics :
    Promotion

  LowDimensionalTopology :
    Promotion

  NewForce :
    Promotion

  StandardModelRewrite :
    Promotion

  ElementaryParticlePromotion :
    Promotion

  ThreeParticlesToday :
    Promotion

  ColliderDiscovery :
    Promotion

  NewVacuumParticle :
    Promotion

  GlobalBosonFermionCollapse :
    Promotion

  LHCAnyonDiscovery :
    Promotion

data ClaimAtom : Set where
  c1LHCJustFoundThreeNewParticles :
    ClaimAtom

  c2MajorQuantumPhysicsBreakthrough :
    ClaimAtom

  c3CERNLHCbFoundRareHadrons :
    ClaimAtom

  c4AnyonWorkBreaksBosonFermionRule :
    ClaimAtom

  c5TheseImplyNewPhysicsRewriteReality :
    ClaimAtom

canonicalMixedClaimAtoms : List ClaimAtom
canonicalMixedClaimAtoms =
  c1LHCJustFoundThreeNewParticles
  ∷ c2MajorQuantumPhysicsBreakthrough
  ∷ c3CERNLHCbFoundRareHadrons
  ∷ c4AnyonWorkBreaksBosonFermionRule
  ∷ c5TheseImplyNewPhysicsRewriteReality
  ∷ []

data SupportedAtom : Set where
  xiCCPlusObservedByLHCb :
    SupportedAtom

  exoticHadronsObservedByLHCb2022 :
    SupportedAtom

  oneDAnyonModelLegitimateLowDimensionalSector :
    SupportedAtom

canonicalSupportedAtoms : List SupportedAtom
canonicalSupportedAtoms =
  xiCCPlusObservedByLHCb
  ∷ exoticHadronsObservedByLHCb2022
  ∷ oneDAnyonModelLegitimateLowDimensionalSector
  ∷ []

data RejectedAtom : Set where
  rejectedThreeParticlesTodayFor2026LHCb :
    RejectedAtom

  rejectedNewForce :
    RejectedAtom

  rejectedStandardModelRewrite :
    RejectedAtom

  rejectedHadronStateToElementaryParticlePromotion :
    RejectedAtom

  rejectedLHCAnyonDiscovery :
    RejectedAtom

  rejectedGlobalBosonFermionCollapse :
    RejectedAtom

canonicalRejectedAtoms : List RejectedAtom
canonicalRejectedAtoms =
  rejectedThreeParticlesTodayFor2026LHCb
  ∷ rejectedNewForce
  ∷ rejectedStandardModelRewrite
  ∷ rejectedHadronStateToElementaryParticlePromotion
  ∷ rejectedLHCAnyonDiscovery
  ∷ rejectedGlobalBosonFermionCollapse
  ∷ []

data ParticleClaimPromotionFlag : Set where

particleClaimPromotionImpossibleHere :
  ParticleClaimPromotionFlag →
  ⊥
particleClaimPromotionImpossibleHere ()

record ParticleClaimReceipt : Set where
  field
    source :
      ClaimSource

    date :
      ClaimDate

    sourceUri :
      String

    system :
      ClaimSystem

    entityKind :
      EntityKind

    observationStatus :
      ObservationStatus

    theoryLane :
      TheoryLane

    observedEntity :
      String

    entityDescription :
      String

    supportedPromotion :
      List Promotion

    forbiddenPromotion :
      List Promotion

open ParticleClaimReceipt public

xiCCPlusSourceUri : String
xiCCPlusSourceUri =
  "https://home.cern/news/news/physics/lhcb-collaboration-discovers-new-proton-particle"

exoticHadrons2022SourceUri : String
exoticHadrons2022SourceUri =
  "https://lhcb-outreach.web.cern.ch/2022/07/05/observation-of-a-strange-pentaquark-a-doubly-charged-tetraquark-and-its-neutral-partner/"

oneDAnyonSourceUri : String
oneDAnyonSourceUri =
  "https://www.oist.jp/news-center/news/2026/2/3/new-class-strange-one-dimensional-particles"

XiCCPlusReceipt : ParticleClaimReceipt
XiCCPlusReceipt =
  record
    { source =
        cernHomeLHCbXiCCPlus20260317
    ; date =
        date20260317
    ; sourceUri =
        xiCCPlusSourceUri
    ; system =
        upgradedLHCbDetector
    ; entityKind =
        conventionalHadron
    ; observationStatus =
        supported
    ; theoryLane =
        StrongForceBinding
    ; observedEntity =
        "Xi_cc+"
    ; entityDescription =
        "doubly charmed baryon with quark content c c d; QCD spectroscopy datum"
    ; supportedPromotion =
        QCDConstraint
        ∷ HadronSpectrumExtension
        ∷ []
    ; forbiddenPromotion =
        NewForce
        ∷ StandardModelRewrite
        ∷ ElementaryParticlePromotion
        ∷ ThreeParticlesToday
        ∷ []
    }

LHCbExoticHadrons2022Receipt : ParticleClaimReceipt
LHCbExoticHadrons2022Receipt =
  record
    { source =
        lhcbOutreachExoticHadrons20220705
    ; date =
        date20220705
    ; sourceUri =
        exoticHadrons2022SourceUri
    ; system =
        lhcbColliderReconstruction
    ; entityKind =
        exoticHadron
    ; observationStatus =
        supported
    ; theoryLane =
        QCDSpectroscopy
    ; observedEntity =
        "strange pentaquark plus doubly charged tetraquark and neutral partner"
    ; entityDescription =
        "exotic hadron / multiquark bound-state cluster in QCD spectroscopy"
    ; supportedPromotion =
        ExoticBindingEvidence
        ∷ QCDConstraint
        ∷ []
    ; forbiddenPromotion =
        NewForce
        ∷ StandardModelRewrite
        ∷ ElementaryParticlePromotion
        ∷ ThreeParticlesToday
        ∷ []
    }

OneDAnyonReceipt : ParticleClaimReceipt
OneDAnyonReceipt =
  record
    { source =
        oistOneDAnyon20260203
    ; date =
        date20260203
    ; sourceUri =
        oneDAnyonSourceUri
    ; system =
        lowDimensionalQuantumModel
    ; entityKind =
        statisticalSector
    ; observationStatus =
        openStatus
    ; theoryLane =
        ExchangeStatistics
    ; observedEntity =
        "one-dimensional anyon sector"
    ; entityDescription =
        "low-dimensional exchange-statistics sector with tunable exchange behavior"
    ; supportedPromotion =
        TunableExchangeStatistics
        ∷ LowDimensionalTopology
        ∷ []
    ; forbiddenPromotion =
        ColliderDiscovery
        ∷ NewVacuumParticle
        ∷ GlobalBosonFermionCollapse
        ∷ LHCAnyonDiscovery
        ∷ []
    }

data MixedParticleClaimPacketStatus : Set where
  mixedPrecisionClaimPacketSplitBindingGrammarFromExchangeGrammar :
    MixedParticleClaimPacketStatus

bindingGrammarStatement : String
bindingGrammarStatement =
  "LHCb hadrons are QCD binding-grammar receipts: composition, confinement, spectroscopy, reconstruction."

exchangeGrammarStatement : String
exchangeGrammarStatement =
  "Anyons are exchange-grammar receipts: low-dimensional topology, indistinguishability, braid/path class, exchange phase."

physicalSentence : String
physicalSentence =
  "LHCb hadrons extend the observed QCD hadron spectrum; one-dimensional anyons concern low-dimensional exchange statistics.  These are different lanes and neither promotes a new force or Standard Model rewrite here."

record MixedParticleClaimPacketReceipt : Setω where
  field
    status :
      MixedParticleClaimPacketStatus

    statusIsCanonical :
      status
      ≡
      mixedPrecisionClaimPacketSplitBindingGrammarFromExchangeGrammar

    xiCCPlusReceipt :
      ParticleClaimReceipt

    xiCCPlusReceiptIsCanonical :
      xiCCPlusReceipt ≡ XiCCPlusReceipt

    exoticHadrons2022Receipt :
      ParticleClaimReceipt

    exoticHadrons2022ReceiptIsCanonical :
      exoticHadrons2022Receipt ≡ LHCbExoticHadrons2022Receipt

    oneDAnyonReceipt :
      ParticleClaimReceipt

    oneDAnyonReceiptIsCanonical :
      oneDAnyonReceipt ≡ OneDAnyonReceipt

    anyonicSectorReceipt :
      Anyon.AnyonicSectorPhysicsReceipt

    anyonicSectorKeepsThreePlusOneDFermionDerivationFalse :
      Anyon.fullThreePlusOneDFermionDerivation anyonicSectorReceipt ≡ false

    packetAtoms :
      List ClaimAtom

    packetAtomsAreCanonical :
      packetAtoms ≡ canonicalMixedClaimAtoms

    supportedAtoms :
      List SupportedAtom

    supportedAtomsAreCanonical :
      supportedAtoms ≡ canonicalSupportedAtoms

    rejectedAtoms :
      List RejectedAtom

    rejectedAtomsAreCanonical :
      rejectedAtoms ≡ canonicalRejectedAtoms

    bindingGrammar :
      String

    bindingGrammarIsCanonical :
      bindingGrammar ≡ bindingGrammarStatement

    exchangeGrammar :
      String

    exchangeGrammarIsCanonical :
      exchangeGrammar ≡ exchangeGrammarStatement

    physicalReading :
      String

    physicalReadingIsCanonical :
      physicalReading ≡ physicalSentence

    newFundamentalForcePromoted :
      Bool

    newFundamentalForcePromotedIsFalse :
      newFundamentalForcePromoted ≡ false

    standardModelRewritePromoted :
      Bool

    standardModelRewritePromotedIsFalse :
      standardModelRewritePromoted ≡ false

    lhcAnyonDiscoveryPromoted :
      Bool

    lhcAnyonDiscoveryPromotedIsFalse :
      lhcAnyonDiscoveryPromoted ≡ false

    elementaryParticlePromotionFromHadron :
      Bool

    elementaryParticlePromotionFromHadronIsFalse :
      elementaryParticlePromotionFromHadron ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    promotionFlags :
      List ParticleClaimPromotionFlag

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open MixedParticleClaimPacketReceipt public

canonicalMixedParticleClaimPacketReceipt :
  MixedParticleClaimPacketReceipt
canonicalMixedParticleClaimPacketReceipt =
  record
    { status =
        mixedPrecisionClaimPacketSplitBindingGrammarFromExchangeGrammar
    ; statusIsCanonical =
        refl
    ; xiCCPlusReceipt =
        XiCCPlusReceipt
    ; xiCCPlusReceiptIsCanonical =
        refl
    ; exoticHadrons2022Receipt =
        LHCbExoticHadrons2022Receipt
    ; exoticHadrons2022ReceiptIsCanonical =
        refl
    ; oneDAnyonReceipt =
        OneDAnyonReceipt
    ; oneDAnyonReceiptIsCanonical =
        refl
    ; anyonicSectorReceipt =
        Anyon.canonicalAnyonicSectorPhysicsReceipt
    ; anyonicSectorKeepsThreePlusOneDFermionDerivationFalse =
        refl
    ; packetAtoms =
        canonicalMixedClaimAtoms
    ; packetAtomsAreCanonical =
        refl
    ; supportedAtoms =
        canonicalSupportedAtoms
    ; supportedAtomsAreCanonical =
        refl
    ; rejectedAtoms =
        canonicalRejectedAtoms
    ; rejectedAtomsAreCanonical =
        refl
    ; bindingGrammar =
        bindingGrammarStatement
    ; bindingGrammarIsCanonical =
        refl
    ; exchangeGrammar =
        exchangeGrammarStatement
    ; exchangeGrammarIsCanonical =
        refl
    ; physicalReading =
        physicalSentence
    ; physicalReadingIsCanonical =
        refl
    ; newFundamentalForcePromoted =
        false
    ; newFundamentalForcePromotedIsFalse =
        refl
    ; standardModelRewritePromoted =
        false
    ; standardModelRewritePromotedIsFalse =
        refl
    ; lhcAnyonDiscoveryPromoted =
        false
    ; lhcAnyonDiscoveryPromotedIsFalse =
        refl
    ; elementaryParticlePromotionFromHadron =
        false
    ; elementaryParticlePromotionFromHadronIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The 2026 LHCb Xi_cc+ receipt is one conventional doubly charmed baryon, not three particles today"
        ∷ "The 2022 LHCb exotic-hadron cluster is separate and remains QCD spectroscopy"
        ∷ "The one-dimensional anyon receipt is low-dimensional exchange-statistics theory, not an LHC discovery"
        ∷ "New force, Standard Model rewrite, hadron-to-elementary promotion, LHC anyon, and terminal claim promotions are false"
        ∷ []
    }

mixedPacketRejectsNewForce :
  newFundamentalForcePromoted canonicalMixedParticleClaimPacketReceipt
  ≡
  false
mixedPacketRejectsNewForce =
  refl

mixedPacketRejectsSMRewrite :
  standardModelRewritePromoted canonicalMixedParticleClaimPacketReceipt
  ≡
  false
mixedPacketRejectsSMRewrite =
  refl

mixedPacketRejectsLHCAnyonDiscovery :
  lhcAnyonDiscoveryPromoted canonicalMixedParticleClaimPacketReceipt
  ≡
  false
mixedPacketRejectsLHCAnyonDiscovery =
  refl

mixedPacketRejectsHadronToElementaryPromotion :
  elementaryParticlePromotionFromHadron canonicalMixedParticleClaimPacketReceipt
  ≡
  false
mixedPacketRejectsHadronToElementaryPromotion =
  refl

mixedPacketKeepsTerminalPromotionFalse :
  terminalClaimPromoted canonicalMixedParticleClaimPacketReceipt
  ≡
  false
mixedPacketKeepsTerminalPromotionFalse =
  refl
