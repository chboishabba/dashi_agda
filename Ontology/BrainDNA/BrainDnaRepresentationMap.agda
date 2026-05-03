module Ontology.BrainDNA.BrainDnaRepresentationMap where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; fst; snd)
open import Data.Vec using (Vec)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
import Ontology.Brain.BrainRegionAutomatonSurface as Region
import Ontology.Brain.BrainVisualFormConstantSurface as Visual
import Ontology.Brain.BrainLearningEigenbasisSurface as Learn
import Ontology.Brain.BrainMorphospaceGapJunctionSurface as Morph
import Ontology.BrainDNA.BrainThemeConnectorSurface as Theme
import Ontology.BrainDNA.BrainVocabularyPacketCompatibility as PacketCompat
import Ontology.BrainDNA.BrainStateCrossoverLaws as StateLaw
import Ontology.BrainDNA.PacketCodecBridge as Bridge
import Ontology.DNA.CrossoverAttachmentSurface as Attach
import Ontology.DNA.CrossoverAttachmentLaws as AttachLaw
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)
open import Ontology.DNA.Supervoxel4Adic using (Base)
import Ontology.DNA.ChannelCodingSurface as CCS

symEq : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
symEq refl = refl

transEq : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
transEq refl q = q

------------------------------------------------------------------------
-- Smallest honest brain->DNA representation owner surface over the current
-- local theme connector and packet/attachment boundaries.
--
-- This remains theorem-thin and non-claiming: it packages one typed
-- representation boundary together with exact width/order/profile
-- compatibility on the current carrier. It does not claim realistic biology,
-- optimal coding, or complete representation semantics.

record BrainDnaRepresentation (n : Nat) : Set₁ where
  constructor brainDnaRepresentation
  field
    themeProfile : Theme.BrainThemeProfile n
    packet : Bridge.BrainPacket n
    encodedBases : Vec Base n
    emittedBases : Σ Nat (λ m → Vec Base m)
    dnaAttachment : Attach.CrossoverAttachmentSurface
    dnaAttachmentLaws : AttachLaw.CrossoverAttachmentLawSurface

representationOf :
  ∀ {n} → BrainState n → Region.BrainRegion → BrainDnaRepresentation n
representationOf st r =
  brainDnaRepresentation
    (Theme.themeProfileOf st r)
    (PacketCompat.stateToBridge st)
    (Bridge.encodePacket (PacketCompat.stateToBridge st))
    (Bridge.packetEmit (PacketCompat.stateToBridge st))
    Attach.crossoverAttachmentSurface
    AttachLaw.crossoverAttachmentLawSurface

representationPacketOrder :
  ∀ {n} → BrainState n → ScanOrder
representationPacketOrder st =
  PacketCompat.BrainVocabularyPacketCompatibilitySurface.packetOrderCompatible
    PacketCompat.brainVocabularyPacketCompatibilitySurface st

representationThemePacketOrderCompatible :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Theme.BrainThemeProfile.packetOrder
    (BrainDnaRepresentation.themeProfile (representationOf st r))
    ≡
  representationPacketOrder st
representationThemePacketOrderCompatible st r = refl

representationOrderLineMajor :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  representationPacketOrder st ≡ lineMajor
representationOrderLineMajor st r =
  PacketCompat.statePacketOrder-lineMajor st

representationVisualWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Visual.BrainLogPolarGeometry.radialRing
    (Theme.BrainThemeProfile.visualGeometry
      (BrainDnaRepresentation.themeProfile (representationOf st r)))
    ≡
  n
representationVisualWidthExact st r =
  Theme.themeVisualWidthExact st r

representationLearningWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Learn.BrainLearningEigenbasisProfile.width
    (Theme.BrainThemeProfile.learningProfile
      (BrainDnaRepresentation.themeProfile (representationOf st r)))
    ≡
  n
representationLearningWidthExact st r =
  Theme.themeLearningWidthExact st r

representationMorphospaceWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Morph.BrainMorphospacePoint.width
    (Theme.BrainThemeProfile.morphospacePoint
      (BrainDnaRepresentation.themeProfile (representationOf st r)))
    ≡
  n
representationMorphospaceWidthExact st r =
  Theme.themeMorphospaceWidthExact st r

representationPacketWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  fst (BrainDnaRepresentation.emittedBases (representationOf st r)) ≡ n
representationPacketWidthExact st r
  rewrite Bridge.packetEmit-identity (PacketCompat.stateToBridge st)
  = refl

representationEmitLengthCompatible :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  fst
    (CCS.IntegratedChannelSurface.emit
      (Attach.CrossoverAttachmentSurface.channel
        (BrainDnaRepresentation.dnaAttachment (representationOf st r)))
      (BrainDnaRepresentation.encodedBases (representationOf st r)))
    ≡
  n
representationEmitLengthCompatible st r =
  AttachLaw.CrossoverAttachmentLawSurface.emitOutputLengthExact
    (BrainDnaRepresentation.dnaAttachmentLaws (representationOf st r))
    (Bridge.encodePacket (PacketCompat.stateToBridge st))

representationEmitAdmissibilityCompatible :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  CCS.genericAdmissibilityFlag
    (snd
      (CCS.IntegratedChannelSurface.emit
        (Attach.CrossoverAttachmentSurface.channel
          (BrainDnaRepresentation.dnaAttachment (representationOf st r)))
        (BrainDnaRepresentation.encodedBases (representationOf st r))))
    ≡
  CCS.genericAdmissibilityFlag
    (BrainDnaRepresentation.encodedBases (representationOf st r))
representationEmitAdmissibilityCompatible st r =
  AttachLaw.CrossoverAttachmentLawSurface.emitOutputGenericAdmissibility
    (BrainDnaRepresentation.dnaAttachmentLaws (representationOf st r))
    (Bridge.encodePacket (PacketCompat.stateToBridge st))

representationStateEncodedBasesCompatible :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainDnaRepresentation.encodedBases (representationOf st r)
    ≡
  StateLaw.BrainStateCrossoverLawSurface.stateEncodedBases
    StateLaw.brainStateCrossoverLawSurface st
representationStateEncodedBasesCompatible st r = refl

representationStateEmittedBasesCompatible :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainDnaRepresentation.emittedBases (representationOf st r)
    ≡
  StateLaw.BrainStateCrossoverLawSurface.stateEmittedBases
    StateLaw.brainStateCrossoverLawSurface st
representationStateEmittedBasesCompatible st r = refl

representationPacketAdmissibilityExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Bridge.packetAdmissibility
    (BrainDnaRepresentation.packet (representationOf st r))
    ≡
  CCS.genericAdmissibilityFlag
    (BrainDnaRepresentation.encodedBases (representationOf st r))
representationPacketAdmissibilityExact st r =
  StateLaw.BrainStateCrossoverLawSurface.statePacketAdmissibilityExact
    StateLaw.brainStateCrossoverLawSurface st

record BrainDnaRepresentationSemantics (n : Nat) : Set₁ where
  constructor brainDnaRepresentationSemantics
  field
    representation : BrainDnaRepresentation n
    order : ScanOrder
    width : Nat
    encodedAdmissibility : Bool
    emittedAdmissibility : Bool

representationSemanticsOf :
  ∀ {n} → BrainState n → Region.BrainRegion → BrainDnaRepresentationSemantics n
representationSemanticsOf st r =
  brainDnaRepresentationSemantics
    (representationOf st r)
    (representationPacketOrder st)
    (fst (BrainDnaRepresentation.emittedBases (representationOf st r)))
    (CCS.genericAdmissibilityFlag
      (BrainDnaRepresentation.encodedBases (representationOf st r)))
    (CCS.genericAdmissibilityFlag
      (snd (BrainDnaRepresentation.emittedBases (representationOf st r))))

representationSemanticsProfileOrderCompatible :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainDnaRepresentationSemantics.order
    (representationSemanticsOf st r)
    ≡
  Theme.BrainThemeProfile.packetOrder
    (BrainDnaRepresentation.themeProfile
      (BrainDnaRepresentationSemantics.representation
        (representationSemanticsOf st r)))
representationSemanticsProfileOrderCompatible st r =
  symEq (representationThemePacketOrderCompatible st r)

representationSemanticsWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainDnaRepresentationSemantics.width
    (representationSemanticsOf st r)
    ≡
  n
representationSemanticsWidthExact st r =
  representationPacketWidthExact st r

representationSemanticsEncodedAdmissibilityExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainDnaRepresentationSemantics.encodedAdmissibility
    (representationSemanticsOf st r)
    ≡
  Bridge.packetAdmissibility
    (BrainDnaRepresentation.packet
      (BrainDnaRepresentationSemantics.representation
        (representationSemanticsOf st r)))
representationSemanticsEncodedAdmissibilityExact st r =
  symEq (representationPacketAdmissibilityExact st r)

representationSemanticsEmittedAdmissibilityExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainDnaRepresentationSemantics.emittedAdmissibility
    (representationSemanticsOf st r)
    ≡
  Bridge.packetAdmissibility
    (BrainDnaRepresentation.packet
      (BrainDnaRepresentationSemantics.representation
        (representationSemanticsOf st r)))
representationSemanticsEmittedAdmissibilityExact st r =
  transEq
    (representationEmitAdmissibilityCompatible st r)
    (symEq (representationPacketAdmissibilityExact st r))

record BrainDnaRepresentationMapSurface : Set₂ where
  field
    themeConnector : Theme.BrainThemeConnectorSurface
    packetCompatibility : PacketCompat.BrainVocabularyPacketCompatibilitySurface
    stateCrossoverLaws : StateLaw.BrainStateCrossoverLawSurface
    dnaAttachment : Attach.CrossoverAttachmentSurface
    dnaAttachmentLaws : AttachLaw.CrossoverAttachmentLawSurface
    represent : ∀ {n} → BrainState n → Region.BrainRegion → BrainDnaRepresentation n
    semantics : ∀ {n} → BrainState n → Region.BrainRegion → BrainDnaRepresentationSemantics n

brainDnaRepresentationMapSurface : BrainDnaRepresentationMapSurface
brainDnaRepresentationMapSurface = record
  { themeConnector = Theme.brainThemeConnectorSurface
  ; packetCompatibility = PacketCompat.brainVocabularyPacketCompatibilitySurface
  ; stateCrossoverLaws = StateLaw.brainStateCrossoverLawSurface
  ; dnaAttachment = Attach.crossoverAttachmentSurface
  ; dnaAttachmentLaws = AttachLaw.crossoverAttachmentLawSurface
  ; represent = representationOf
  ; semantics = representationSemanticsOf
  }
