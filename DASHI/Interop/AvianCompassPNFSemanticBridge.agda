module DASHI.Interop.AvianCompassPNFSemanticBridge where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Biology.AvianCompassSurface as Avian
import DASHI.Interop.SensibLawResidualLattice as Residual

------------------------------------------------------------------------
-- PNF atoms emitted for avian-compass semantic interop.
--
-- These atoms are evidence wrappers over the avian surface vocabulary.  They
-- do not promote PNF text, compass-overlay descriptions, or qualia boundaries
-- into biological truth authority.

quantumMechanismPNFAtom : Residual.PredicatePNF
quantumMechanismPNFAtom =
  Residual.predicatePNF
    "avian-compass-quantum-mechanism-evidence"
    Residual.sig-agent-theme
    (Residual.opaqueArg "cryptochrome-4/radical-pair-chain")
    (Residual.opaqueArg "spin-evolution/singlet-triplet-yield")
    Residual.absent
    Residual.modal
    Residual.attributedEvidence
    "DASHI.Biology.AvianCompassSurface: BridgeLayer radicalPairLayer/spinEvolutionLayer/singletTripletYieldLayer"

visualOverlayPNFAtom : Residual.PredicatePNF
visualOverlayPNFAtom =
  Residual.predicatePNF
    "avian-compass-visual-overlay-evidence"
    Residual.sig-theme-only
    Residual.absent
    (Residual.opaqueArg "visual-cue/perceptual-geometry-overlay")
    Residual.absent
    Residual.modal
    Residual.attributedEvidence
    "DASHI.Biology.AvianCompassSurface: PerceptualGeometry and visualCue/navigationUse surface"

rfPerturbationPNFAtom : Residual.PredicatePNF
rfPerturbationPNFAtom =
  Residual.predicatePNF
    "avian-compass-rf-perturbation-evidence"
    Residual.sig-agent-theme
    (Residual.opaqueArg "oscillating-rf-field")
    (Residual.opaqueArg "orientation-effect/yield-change")
    Residual.absent
    Residual.modal
    Residual.attributedEvidence
    "DASHI.Biology.AvianCompassSurface: PerturbedCompassReceipt perturbation/yieldChanged/orientationEffect"

behaviorReceiptPNFAtom : Residual.PredicatePNF
behaviorReceiptPNFAtom =
  Residual.predicatePNF
    "avian-compass-behavior-receipt-evidence"
    Residual.sig-agent-theme
    (Residual.opaqueArg "navigation-policy")
    (Residual.opaqueArg "observable-orientation-cue")
    Residual.absent
    Residual.positive
    Residual.directEvidence
    "DASHI.Biology.AvianCompassSurface: AvianCompassBridgeReceipt promotedBiologicalObservable"

noQualiaBoundaryPNFAtom : Residual.PredicatePNF
noQualiaBoundaryPNFAtom =
  Residual.predicatePNF
    "avian-compass-no-qualia-boundary"
    Residual.sig-theme-only
    Residual.absent
    (Residual.opaqueArg "subjective-qualia-recovery")
    Residual.absent
    Residual.negated
    Residual.attributedEvidence
    "DASHI.Biology.AvianCompassSurface: ObservableNotQualiaBoundary/noSubjectiveQualiaRecovery"

canonicalAvianCompassPNFAtoms : List Residual.PredicatePNF
canonicalAvianCompassPNFAtoms =
  quantumMechanismPNFAtom
  ∷ visualOverlayPNFAtom
  ∷ rfPerturbationPNFAtom
  ∷ behaviorReceiptPNFAtom
  ∷ noQualiaBoundaryPNFAtom
  ∷ []

------------------------------------------------------------------------
-- Runtime-style emission receipts for the canonical bridge atoms.

avianCompassPNFReceipt :
  String → Residual.PredicatePNF → Residual.PNFEmissionReceipt
avianCompassPNFReceipt span atom =
  Residual.pnfEmissionReceipt
    "avian-compass-surface-to-pnf"
    "sensiblaw-residual-lattice/evidence-only"
    span
    atom

quantumMechanismPNFReceipt : Residual.PNFEmissionReceipt
quantumMechanismPNFReceipt =
  avianCompassPNFReceipt
    "quantum mechanism overlay claim"
    quantumMechanismPNFAtom

visualOverlayPNFReceipt : Residual.PNFEmissionReceipt
visualOverlayPNFReceipt =
  avianCompassPNFReceipt
    "visual overlay claim"
    visualOverlayPNFAtom

rfPerturbationPNFReceipt : Residual.PNFEmissionReceipt
rfPerturbationPNFReceipt =
  avianCompassPNFReceipt
    "radio-frequency perturbation claim"
    rfPerturbationPNFAtom

behaviorReceiptPNFReceipt : Residual.PNFEmissionReceipt
behaviorReceiptPNFReceipt =
  avianCompassPNFReceipt
    "observable behaviour receipt"
    behaviorReceiptPNFAtom

noQualiaBoundaryPNFReceipt : Residual.PNFEmissionReceipt
noQualiaBoundaryPNFReceipt =
  avianCompassPNFReceipt
    "no subjective qualia recovery boundary"
    noQualiaBoundaryPNFAtom

------------------------------------------------------------------------
-- Residual expectations.

mechanismQualiaResidual : Residual.ResidualLevel
mechanismQualiaResidual =
  Residual.computeResidual quantumMechanismPNFAtom noQualiaBoundaryPNFAtom

mechanismVisualResidual : Residual.ResidualLevel
mechanismVisualResidual =
  Residual.computeResidual quantumMechanismPNFAtom visualOverlayPNFAtom

mechanismRFResidual : Residual.ResidualLevel
mechanismRFResidual =
  Residual.computeResidual quantumMechanismPNFAtom rfPerturbationPNFAtom

rfBehaviorResidual : Residual.ResidualLevel
rfBehaviorResidual =
  Residual.computeResidual rfPerturbationPNFAtom behaviorReceiptPNFAtom

qualiaVisualResidual : Residual.ResidualLevel
qualiaVisualResidual =
  Residual.computeResidual noQualiaBoundaryPNFAtom visualOverlayPNFAtom

mechanismQualiaResidualIsNoTypedMeet :
  mechanismQualiaResidual ≡ Residual.noTypedMeet
mechanismQualiaResidualIsNoTypedMeet =
  refl

mechanismVisualResidualIsNoTypedMeet :
  mechanismVisualResidual ≡ Residual.noTypedMeet
mechanismVisualResidualIsNoTypedMeet =
  refl

mechanismRFResidualIsExact :
  mechanismRFResidual ≡ Residual.exact
mechanismRFResidualIsExact =
  refl

rfBehaviorResidualIsPartial :
  rfBehaviorResidual ≡ Residual.partial
rfBehaviorResidualIsPartial =
  refl

qualiaVisualResidualIsContradiction :
  qualiaVisualResidual ≡ Residual.contradiction
qualiaVisualResidualIsContradiction =
  refl

receiptMechanismQualiaResidualIsNoTypedMeet :
  Residual.receiptResidual
    quantumMechanismPNFReceipt
    noQualiaBoundaryPNFReceipt
  ≡
  Residual.noTypedMeet
receiptMechanismQualiaResidualIsNoTypedMeet =
  refl

------------------------------------------------------------------------
-- Evidence-only / non-promotion boundary.

pnfSemanticTruthAuthority : Bool
pnfSemanticTruthAuthority =
  false

pnfSemanticTruthAuthorityIsFalse :
  pnfSemanticTruthAuthority ≡ false
pnfSemanticTruthAuthorityIsFalse =
  refl

qualiaPromotion : Bool
qualiaPromotion =
  false

qualiaPromotionIsFalse :
  qualiaPromotion ≡ false
qualiaPromotionIsFalse =
  refl

data AvianCompassPNFBoundary : Set where
  evidenceOnlyPNFAtoms : AvianCompassPNFBoundary
  noPNFSemanticTruthAuthority : AvianCompassPNFBoundary
  noQualiaPromotion : AvianCompassPNFBoundary
  crossFibreMechanismQualiaNoTypedMeet : AvianCompassPNFBoundary
  observableBehaviourDoesNotRecoverSubjectiveQualia : AvianCompassPNFBoundary

canonicalAvianCompassPNFBoundaries : List AvianCompassPNFBoundary
canonicalAvianCompassPNFBoundaries =
  evidenceOnlyPNFAtoms
  ∷ noPNFSemanticTruthAuthority
  ∷ noQualiaPromotion
  ∷ crossFibreMechanismQualiaNoTypedMeet
  ∷ observableBehaviourDoesNotRecoverSubjectiveQualia
  ∷ []

record AvianCompassPNFSemanticBridge
    (receipt : Avian.AvianCompassBridgeReceipt) : Set₁ where
  field
    sourceReceipt :
      Avian.AvianCompassBridgeReceipt

    sourceReceiptIsInput :
      sourceReceipt ≡ receipt

    mechanismAtom :
      Residual.PredicatePNF

    visualOverlayAtom :
      Residual.PredicatePNF

    rfPerturbationAtom :
      Residual.PredicatePNF

    behaviorReceiptAtom :
      Residual.PredicatePNF

    noQualiaBoundaryAtom :
      Residual.PredicatePNF

    listedAtoms :
      List Residual.PredicatePNF

    listedAtomsAreCanonical :
      listedAtoms ≡ canonicalAvianCompassPNFAtoms

    mechanismWrapperIsAttributedEvidence :
      Residual.PredicatePNF.wrapper mechanismAtom
      ≡
      Residual.attributedEvidence

    visualOverlayWrapperIsAttributedEvidence :
      Residual.PredicatePNF.wrapper visualOverlayAtom
      ≡
      Residual.attributedEvidence

    rfPerturbationWrapperIsAttributedEvidence :
      Residual.PredicatePNF.wrapper rfPerturbationAtom
      ≡
      Residual.attributedEvidence

    noQualiaWrapperIsAttributedEvidence :
      Residual.PredicatePNF.wrapper noQualiaBoundaryAtom
      ≡
      Residual.attributedEvidence

    behaviorWrapperIsDirectEvidenceOnlyForObservableReceipt :
      Residual.PredicatePNF.wrapper behaviorReceiptAtom
      ≡
      Residual.directEvidence

    mechanismQualiaResidualLevel :
      Residual.ResidualLevel

    mechanismQualiaResidualComesFromPNFComputation :
      mechanismQualiaResidualLevel
      ≡
      Residual.computeResidual mechanismAtom noQualiaBoundaryAtom

    mechanismQualiaNoTypedMeet :
      mechanismQualiaResidualLevel ≡ Residual.noTypedMeet

    pnfSemanticTruthAuthorityField :
      Bool

    pnfSemanticTruthAuthorityFieldIsFalse :
      pnfSemanticTruthAuthorityField ≡ false

    qualiaPromotionField :
      Bool

    qualiaPromotionFieldIsFalse :
      qualiaPromotionField ≡ false

    sourceObservablePromoted :
      Avian.promotedBiologicalObservable receipt ≡ true

    sourceQualiaUnrecovered :
      Avian.subjectiveQualiaRecovered receipt ≡ false

    bridgeBoundaries :
      List AvianCompassPNFBoundary

    bridgeBoundariesAreCanonical :
      bridgeBoundaries ≡ canonicalAvianCompassPNFBoundaries

avianCompassPNFSemanticBridgeFromReceipt :
  (receipt : Avian.AvianCompassBridgeReceipt) →
  AvianCompassPNFSemanticBridge receipt
avianCompassPNFSemanticBridgeFromReceipt receipt =
  record
    { sourceReceipt =
        receipt
    ; sourceReceiptIsInput =
        refl
    ; mechanismAtom =
        quantumMechanismPNFAtom
    ; visualOverlayAtom =
        visualOverlayPNFAtom
    ; rfPerturbationAtom =
        rfPerturbationPNFAtom
    ; behaviorReceiptAtom =
        behaviorReceiptPNFAtom
    ; noQualiaBoundaryAtom =
        noQualiaBoundaryPNFAtom
    ; listedAtoms =
        canonicalAvianCompassPNFAtoms
    ; listedAtomsAreCanonical =
        refl
    ; mechanismWrapperIsAttributedEvidence =
        refl
    ; visualOverlayWrapperIsAttributedEvidence =
        refl
    ; rfPerturbationWrapperIsAttributedEvidence =
        refl
    ; noQualiaWrapperIsAttributedEvidence =
        refl
    ; behaviorWrapperIsDirectEvidenceOnlyForObservableReceipt =
        refl
    ; mechanismQualiaResidualLevel =
        mechanismQualiaResidual
    ; mechanismQualiaResidualComesFromPNFComputation =
        refl
    ; mechanismQualiaNoTypedMeet =
        mechanismQualiaResidualIsNoTypedMeet
    ; pnfSemanticTruthAuthorityField =
        pnfSemanticTruthAuthority
    ; pnfSemanticTruthAuthorityFieldIsFalse =
        pnfSemanticTruthAuthorityIsFalse
    ; qualiaPromotionField =
        qualiaPromotion
    ; qualiaPromotionFieldIsFalse =
        qualiaPromotionIsFalse
    ; sourceObservablePromoted =
        Avian.promotedBiologicalObservableIsTrue receipt
    ; sourceQualiaUnrecovered =
        Avian.subjectiveQualiaRecoveredIsFalse receipt
    ; bridgeBoundaries =
        canonicalAvianCompassPNFBoundaries
    ; bridgeBoundariesAreCanonical =
        refl
    }

record AvianCompassPNFSemanticBridgeCertificate : Set₁ where
  field
    receipt :
      Avian.AvianCompassBridgeReceipt

    bridge :
      AvianCompassPNFSemanticBridge receipt

    atomList :
      List Residual.PredicatePNF

    atomListMatchesBridge :
      atomList
      ≡
      AvianCompassPNFSemanticBridge.listedAtoms bridge

    mechanismQualiaBoundary :
      Residual.ResidualLevel

    mechanismQualiaBoundaryIsBridgeResidual :
      mechanismQualiaBoundary
      ≡
      AvianCompassPNFSemanticBridge.mechanismQualiaResidualLevel bridge

    pnfSemanticTruthAuthorityCertificate :
      Bool

    pnfSemanticTruthAuthorityCertificateIsFalse :
      pnfSemanticTruthAuthorityCertificate ≡ false

    qualiaPromotionCertificate :
      Bool

    qualiaPromotionCertificateIsFalse :
      qualiaPromotionCertificate ≡ false

avianCompassPNFSemanticBridgeCertificateFromReceipt :
  (receipt : Avian.AvianCompassBridgeReceipt) →
  AvianCompassPNFSemanticBridgeCertificate
avianCompassPNFSemanticBridgeCertificateFromReceipt receipt =
  record
    { receipt =
        receipt
    ; bridge =
        avianCompassPNFSemanticBridgeFromReceipt receipt
    ; atomList =
        canonicalAvianCompassPNFAtoms
    ; atomListMatchesBridge =
        refl
    ; mechanismQualiaBoundary =
        mechanismQualiaResidual
    ; mechanismQualiaBoundaryIsBridgeResidual =
        refl
    ; pnfSemanticTruthAuthorityCertificate =
        pnfSemanticTruthAuthority
    ; pnfSemanticTruthAuthorityCertificateIsFalse =
        pnfSemanticTruthAuthorityIsFalse
    ; qualiaPromotionCertificate =
        qualiaPromotion
    ; qualiaPromotionCertificateIsFalse =
        qualiaPromotionIsFalse
    }
