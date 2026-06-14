module DASHI.Interop.QualiaTranscriptPNFSemanticBridge where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.SensibLawResidualLattice as Residual

------------------------------------------------------------------------
-- Transcript-level qualitative-experience PNF surface.
--
-- The carrier below records that the source is a transcript with at least
-- two speakers discussing qualitative-experience vocabulary.  It does not
-- parse the transcript, identify the speakers' experiences, or recover
-- phenomenal content.

data TranscriptSpeakerMultiplicity : Set where
  twoSpeakers : TranscriptSpeakerMultiplicity
  moreThanTwoSpeakers : TranscriptSpeakerMultiplicity

data QualitativeExperienceTopic : Set where
  colorBreathing : QualitativeExperienceTopic
  timeNonlinearity : QualitativeExperienceTopic
  egoDissolution : QualitativeExperienceTopic
  ineffability : QualitativeExperienceTopic

record QualiaTranscriptSurface : Set where
  constructor qualiaTranscriptSurface
  field
    transcriptId : String
    speakerMultiplicity : TranscriptSpeakerMultiplicity
    discussedTopics : List QualitativeExperienceTopic
    evidenceSpan : String
    provenance : String

canonicalQualiaTranscriptSurface : QualiaTranscriptSurface
canonicalQualiaTranscriptSurface =
  qualiaTranscriptSurface
    "qualia-transcript-example"
    twoSpeakers
    (colorBreathing
     ∷ timeNonlinearity
     ∷ egoDissolution
     ∷ ineffability
     ∷ [])
    "two or more speakers discuss color breathing, nonlinear time, ego dissolution, and ineffability"
    "transcript-level qualitative-experience PNF bridge fixture"

------------------------------------------------------------------------
-- PNF atoms emitted for transcript qualitative-experience interop.

transcriptDiscussionPNFAtom : Residual.PredicatePNF
transcriptDiscussionPNFAtom =
  Residual.predicatePNF
    "qualia-transcript-discussion-evidence"
    Residual.sig-agent-theme
    (Residual.opaqueArg "two-or-more-speakers")
    (Residual.opaqueArg "qualitative-experience-discussion")
    Residual.absent
    Residual.positive
    Residual.attributedEvidence
    "QualiaTranscriptPNFSemanticBridge: transcript speakers discuss qualitative-experience vocabulary"

colorBreathingPNFAtom : Residual.PredicatePNF
colorBreathingPNFAtom =
  Residual.predicatePNF
    "qualia-transcript-color-breathing-evidence"
    Residual.sig-agent-theme
    (Residual.opaqueArg "speaker-report")
    (Residual.opaqueArg "color-breathing")
    Residual.absent
    Residual.modal
    Residual.attributedEvidence
    "QualiaTranscriptPNFSemanticBridge: reported color-breathing expression in transcript evidence"

timeNonlinearityPNFAtom : Residual.PredicatePNF
timeNonlinearityPNFAtom =
  Residual.predicatePNF
    "qualia-transcript-time-nonlinearity-evidence"
    Residual.sig-agent-theme
    (Residual.opaqueArg "speaker-report")
    (Residual.opaqueArg "time-nonlinearity")
    Residual.absent
    Residual.modal
    Residual.attributedEvidence
    "QualiaTranscriptPNFSemanticBridge: reported nonlinear-time expression in transcript evidence"

egoDissolutionPNFAtom : Residual.PredicatePNF
egoDissolutionPNFAtom =
  Residual.predicatePNF
    "qualia-transcript-ego-dissolution-evidence"
    Residual.sig-agent-theme
    (Residual.opaqueArg "speaker-report")
    (Residual.opaqueArg "ego-dissolution")
    Residual.absent
    Residual.modal
    Residual.attributedEvidence
    "QualiaTranscriptPNFSemanticBridge: reported ego-dissolution expression in transcript evidence"

ineffabilityPNFAtom : Residual.PredicatePNF
ineffabilityPNFAtom =
  Residual.predicatePNF
    "qualia-transcript-ineffability-evidence"
    Residual.sig-agent-theme
    (Residual.opaqueArg "speaker-report")
    (Residual.opaqueArg "ineffability")
    Residual.absent
    Residual.modal
    Residual.attributedEvidence
    "QualiaTranscriptPNFSemanticBridge: reported ineffability expression in transcript evidence"

noSemanticTruthAuthorityPNFAtom : Residual.PredicatePNF
noSemanticTruthAuthorityPNFAtom =
  Residual.predicatePNF
    "qualia-transcript-no-semantic-truth-authority"
    Residual.sig-theme-only
    Residual.absent
    (Residual.opaqueArg "semantic-truth-authority")
    Residual.absent
    Residual.negated
    Residual.attributedEvidence
    "QualiaTranscriptPNFSemanticBridge: PNF evidence does not authorize transcript semantic truth"

noSpeakerExperienceVerificationPNFAtom : Residual.PredicatePNF
noSpeakerExperienceVerificationPNFAtom =
  Residual.predicatePNF
    "qualia-transcript-no-speaker-experience-verification"
    Residual.sig-theme-only
    Residual.absent
    (Residual.opaqueArg "speaker-experience-verification")
    Residual.absent
    Residual.negated
    Residual.attributedEvidence
    "QualiaTranscriptPNFSemanticBridge: transcript evidence does not verify speaker experience"

noPhenomenalContentRecoveryPNFAtom : Residual.PredicatePNF
noPhenomenalContentRecoveryPNFAtom =
  Residual.predicatePNF
    "qualia-transcript-no-phenomenal-content-recovery"
    Residual.sig-theme-only
    Residual.absent
    (Residual.opaqueArg "phenomenal-content-recovery")
    Residual.absent
    Residual.negated
    Residual.attributedEvidence
    "QualiaTranscriptPNFSemanticBridge: transcript evidence does not recover phenomenal content"

canonicalQualiaTranscriptPNFAtoms : List Residual.PredicatePNF
canonicalQualiaTranscriptPNFAtoms =
  transcriptDiscussionPNFAtom
  ∷ colorBreathingPNFAtom
  ∷ timeNonlinearityPNFAtom
  ∷ egoDissolutionPNFAtom
  ∷ ineffabilityPNFAtom
  ∷ noSemanticTruthAuthorityPNFAtom
  ∷ noSpeakerExperienceVerificationPNFAtom
  ∷ noPhenomenalContentRecoveryPNFAtom
  ∷ []

------------------------------------------------------------------------
-- Transcript report quotient.
--
-- This quotient is over public report structure only. It records that ITIR
-- PNF can preserve transcript roles and comparison hooks without promoting
-- those reports into semantic truth, verified experience, or phenomenal
-- content.

record TranscriptReportQuotient
    (surface : QualiaTranscriptSurface) : Set where
  field
    transcriptPNF :
      List Residual.PredicatePNF

    transcriptPNFAreCanonical :
      transcriptPNF ≡ canonicalQualiaTranscriptPNFAtoms

    reportStructureConstrained :
      Bool

    reportStructureConstrainedIsTrue :
      reportStructureConstrained ≡ true

    reportQuotientPromoted :
      Bool

    reportQuotientPromotedIsFalse :
      reportQuotientPromoted ≡ false

    speakerExperienceVerified :
      Bool

    speakerExperienceVerifiedIsFalse :
      speakerExperienceVerified ≡ false

    phenomenalContentRecovered :
      Bool

    phenomenalContentRecoveredIsFalse :
      phenomenalContentRecovered ≡ false

    quotientReading :
      String

open TranscriptReportQuotient public

transcriptReportQuotient :
  (surface : QualiaTranscriptSurface) →
  TranscriptReportQuotient surface
transcriptReportQuotient surface =
  record
    { transcriptPNF =
        canonicalQualiaTranscriptPNFAtoms
    ; transcriptPNFAreCanonical =
        refl
    ; reportStructureConstrained =
        true
    ; reportStructureConstrainedIsTrue =
        refl
    ; reportQuotientPromoted =
        false
    ; reportQuotientPromotedIsFalse =
        refl
    ; speakerExperienceVerified =
        false
    ; speakerExperienceVerifiedIsFalse =
        refl
    ; phenomenalContentRecovered =
        false
    ; phenomenalContentRecoveredIsFalse =
        refl
    ; quotientReading =
        "Transcript PNF quotients public qualitative report structure while blocking semantic truth, speaker-experience verification, and phenomenal content recovery."
    }

------------------------------------------------------------------------
-- Runtime-style emission receipts for the canonical bridge atoms.

qualiaTranscriptPNFReceipt :
  String → Residual.PredicatePNF → Residual.PNFEmissionReceipt
qualiaTranscriptPNFReceipt span atom =
  Residual.pnfEmissionReceipt
    "qualia-transcript-to-pnf"
    "sensiblaw-residual-lattice/evidence-only"
    span
    atom

transcriptDiscussionPNFReceipt : Residual.PNFEmissionReceipt
transcriptDiscussionPNFReceipt =
  qualiaTranscriptPNFReceipt
    "two-or-more-speaker qualitative-experience transcript span"
    transcriptDiscussionPNFAtom

colorBreathingPNFReceipt : Residual.PNFEmissionReceipt
colorBreathingPNFReceipt =
  qualiaTranscriptPNFReceipt
    "color breathing report span"
    colorBreathingPNFAtom

timeNonlinearityPNFReceipt : Residual.PNFEmissionReceipt
timeNonlinearityPNFReceipt =
  qualiaTranscriptPNFReceipt
    "time nonlinearity report span"
    timeNonlinearityPNFAtom

egoDissolutionPNFReceipt : Residual.PNFEmissionReceipt
egoDissolutionPNFReceipt =
  qualiaTranscriptPNFReceipt
    "ego dissolution report span"
    egoDissolutionPNFAtom

ineffabilityPNFReceipt : Residual.PNFEmissionReceipt
ineffabilityPNFReceipt =
  qualiaTranscriptPNFReceipt
    "ineffability report span"
    ineffabilityPNFAtom

noSemanticTruthAuthorityPNFReceipt : Residual.PNFEmissionReceipt
noSemanticTruthAuthorityPNFReceipt =
  qualiaTranscriptPNFReceipt
    "semantic truth authority blocked span"
    noSemanticTruthAuthorityPNFAtom

noSpeakerExperienceVerificationPNFReceipt : Residual.PNFEmissionReceipt
noSpeakerExperienceVerificationPNFReceipt =
  qualiaTranscriptPNFReceipt
    "speaker experience verification blocked span"
    noSpeakerExperienceVerificationPNFAtom

noPhenomenalContentRecoveryPNFReceipt : Residual.PNFEmissionReceipt
noPhenomenalContentRecoveryPNFReceipt =
  qualiaTranscriptPNFReceipt
    "phenomenal content recovery blocked span"
    noPhenomenalContentRecoveryPNFAtom

------------------------------------------------------------------------
-- Evidence wrapper/provenance preservation.

record EvidenceWrappedTranscriptPNFAtom : Set where
  constructor evidenceWrappedTranscriptPNFAtom
  field
    atom : Residual.PredicatePNF
    preservedWrapper : Residual.WrapperState
    preservedProvenance : String
    wrapperPreserved :
      preservedWrapper ≡ Residual.PredicatePNF.wrapper atom
    provenancePreserved :
      preservedProvenance ≡ Residual.PredicatePNF.provenance atom

wrapTranscriptAtom :
  (atom : Residual.PredicatePNF) → EvidenceWrappedTranscriptPNFAtom
wrapTranscriptAtom atom =
  evidenceWrappedTranscriptPNFAtom
    atom
    (Residual.PredicatePNF.wrapper atom)
    (Residual.PredicatePNF.provenance atom)
    refl
    refl

canonicalWrappedQualiaTranscriptPNFAtoms :
  List EvidenceWrappedTranscriptPNFAtom
canonicalWrappedQualiaTranscriptPNFAtoms =
  wrapTranscriptAtom transcriptDiscussionPNFAtom
  ∷ wrapTranscriptAtom colorBreathingPNFAtom
  ∷ wrapTranscriptAtom timeNonlinearityPNFAtom
  ∷ wrapTranscriptAtom egoDissolutionPNFAtom
  ∷ wrapTranscriptAtom ineffabilityPNFAtom
  ∷ wrapTranscriptAtom noSemanticTruthAuthorityPNFAtom
  ∷ wrapTranscriptAtom noSpeakerExperienceVerificationPNFAtom
  ∷ wrapTranscriptAtom noPhenomenalContentRecoveryPNFAtom
  ∷ []

------------------------------------------------------------------------
-- Residual expectations.

colorTimeResidual : Residual.ResidualLevel
colorTimeResidual =
  Residual.computeResidual colorBreathingPNFAtom timeNonlinearityPNFAtom

colorTruthAuthorityResidual : Residual.ResidualLevel
colorTruthAuthorityResidual =
  Residual.computeResidual colorBreathingPNFAtom noSemanticTruthAuthorityPNFAtom

experienceVerificationContentRecoveryResidual : Residual.ResidualLevel
experienceVerificationContentRecoveryResidual =
  Residual.computeResidual
    noSpeakerExperienceVerificationPNFAtom
    noPhenomenalContentRecoveryPNFAtom

discussionColorResidual : Residual.ResidualLevel
discussionColorResidual =
  Residual.computeResidual transcriptDiscussionPNFAtom colorBreathingPNFAtom

colorTimeResidualIsExact :
  colorTimeResidual ≡ Residual.exact
colorTimeResidualIsExact =
  refl

colorTruthAuthorityResidualIsNoTypedMeet :
  colorTruthAuthorityResidual ≡ Residual.noTypedMeet
colorTruthAuthorityResidualIsNoTypedMeet =
  refl

experienceVerificationContentRecoveryResidualIsExact :
  experienceVerificationContentRecoveryResidual ≡ Residual.exact
experienceVerificationContentRecoveryResidualIsExact =
  refl

discussionColorResidualIsContradiction :
  discussionColorResidual ≡ Residual.contradiction
discussionColorResidualIsContradiction =
  refl

receiptColorTruthAuthorityResidualIsNoTypedMeet :
  Residual.receiptResidual
    colorBreathingPNFReceipt
    noSemanticTruthAuthorityPNFReceipt
  ≡
  Residual.noTypedMeet
receiptColorTruthAuthorityResidualIsNoTypedMeet =
  refl

------------------------------------------------------------------------
-- Evidence-only / non-authority boundary.

pnfSemanticTruthAuthority : Bool
pnfSemanticTruthAuthority =
  false

pnfSemanticTruthAuthorityIsFalse :
  pnfSemanticTruthAuthority ≡ false
pnfSemanticTruthAuthorityIsFalse =
  refl

speakerExperienceVerification : Bool
speakerExperienceVerification =
  false

speakerExperienceVerificationIsFalse :
  speakerExperienceVerification ≡ false
speakerExperienceVerificationIsFalse =
  refl

phenomenalContentRecovery : Bool
phenomenalContentRecovery =
  false

phenomenalContentRecoveryIsFalse :
  phenomenalContentRecovery ≡ false
phenomenalContentRecoveryIsFalse =
  refl

data QualiaTranscriptPNFBoundary : Set where
  evidenceOnlyTranscriptPNFAtoms : QualiaTranscriptPNFBoundary
  twoOrMoreSpeakerTranscriptSurface : QualiaTranscriptPNFBoundary
  noPNFSemanticTruthAuthority : QualiaTranscriptPNFBoundary
  noSpeakerExperienceVerification : QualiaTranscriptPNFBoundary
  noPhenomenalContentRecovery : QualiaTranscriptPNFBoundary
  crossFibreQualiaAuthorityNoTypedMeet : QualiaTranscriptPNFBoundary

canonicalQualiaTranscriptPNFBoundaries :
  List QualiaTranscriptPNFBoundary
canonicalQualiaTranscriptPNFBoundaries =
  evidenceOnlyTranscriptPNFAtoms
  ∷ twoOrMoreSpeakerTranscriptSurface
  ∷ noPNFSemanticTruthAuthority
  ∷ noSpeakerExperienceVerification
  ∷ noPhenomenalContentRecovery
  ∷ crossFibreQualiaAuthorityNoTypedMeet
  ∷ []

record QualiaTranscriptPNFSemanticBridge
    (surface : QualiaTranscriptSurface) : Set₁ where
  field
    sourceSurface :
      QualiaTranscriptSurface

    sourceSurfaceIsInput :
      sourceSurface ≡ surface

    transcriptAtom :
      Residual.PredicatePNF

    colorBreathingAtom :
      Residual.PredicatePNF

    timeNonlinearityAtom :
      Residual.PredicatePNF

    egoDissolutionAtom :
      Residual.PredicatePNF

    ineffabilityAtom :
      Residual.PredicatePNF

    noSemanticTruthAuthorityAtom :
      Residual.PredicatePNF

    noSpeakerExperienceVerificationAtom :
      Residual.PredicatePNF

    noPhenomenalContentRecoveryAtom :
      Residual.PredicatePNF

    listedAtoms :
      List Residual.PredicatePNF

    listedAtomsAreCanonical :
      listedAtoms ≡ canonicalQualiaTranscriptPNFAtoms

    wrappedAtoms :
      List EvidenceWrappedTranscriptPNFAtom

    wrappedAtomsAreCanonical :
      wrappedAtoms ≡ canonicalWrappedQualiaTranscriptPNFAtoms

    transcriptWrapperIsAttributedEvidence :
      Residual.PredicatePNF.wrapper transcriptAtom
      ≡
      Residual.attributedEvidence

    colorWrapperIsAttributedEvidence :
      Residual.PredicatePNF.wrapper colorBreathingAtom
      ≡
      Residual.attributedEvidence

    timeWrapperIsAttributedEvidence :
      Residual.PredicatePNF.wrapper timeNonlinearityAtom
      ≡
      Residual.attributedEvidence

    egoWrapperIsAttributedEvidence :
      Residual.PredicatePNF.wrapper egoDissolutionAtom
      ≡
      Residual.attributedEvidence

    ineffabilityWrapperIsAttributedEvidence :
      Residual.PredicatePNF.wrapper ineffabilityAtom
      ≡
      Residual.attributedEvidence

    noSemanticTruthAuthorityWrapperIsAttributedEvidence :
      Residual.PredicatePNF.wrapper noSemanticTruthAuthorityAtom
      ≡
      Residual.attributedEvidence

    noSpeakerExperienceVerificationWrapperIsAttributedEvidence :
      Residual.PredicatePNF.wrapper noSpeakerExperienceVerificationAtom
      ≡
      Residual.attributedEvidence

    noPhenomenalContentRecoveryWrapperIsAttributedEvidence :
      Residual.PredicatePNF.wrapper noPhenomenalContentRecoveryAtom
      ≡
      Residual.attributedEvidence

    colorProvenancePreserved :
      Residual.PredicatePNF.provenance colorBreathingAtom
      ≡
      "QualiaTranscriptPNFSemanticBridge: reported color-breathing expression in transcript evidence"

    timeProvenancePreserved :
      Residual.PredicatePNF.provenance timeNonlinearityAtom
      ≡
      "QualiaTranscriptPNFSemanticBridge: reported nonlinear-time expression in transcript evidence"

    egoProvenancePreserved :
      Residual.PredicatePNF.provenance egoDissolutionAtom
      ≡
      "QualiaTranscriptPNFSemanticBridge: reported ego-dissolution expression in transcript evidence"

    ineffabilityProvenancePreserved :
      Residual.PredicatePNF.provenance ineffabilityAtom
      ≡
      "QualiaTranscriptPNFSemanticBridge: reported ineffability expression in transcript evidence"

    colorTruthAuthorityResidualLevel :
      Residual.ResidualLevel

    colorTruthAuthorityResidualComesFromPNFComputation :
      colorTruthAuthorityResidualLevel
      ≡
      Residual.computeResidual
        colorBreathingAtom
        noSemanticTruthAuthorityAtom

    colorTruthAuthorityNoTypedMeet :
      colorTruthAuthorityResidualLevel ≡ Residual.noTypedMeet

    pnfSemanticTruthAuthorityField :
      Bool

    pnfSemanticTruthAuthorityFieldIsFalse :
      pnfSemanticTruthAuthorityField ≡ false

    speakerExperienceVerificationField :
      Bool

    speakerExperienceVerificationFieldIsFalse :
      speakerExperienceVerificationField ≡ false

    phenomenalContentRecoveryField :
      Bool

    phenomenalContentRecoveryFieldIsFalse :
      phenomenalContentRecoveryField ≡ false

    bridgeBoundaries :
      List QualiaTranscriptPNFBoundary

    bridgeBoundariesAreCanonical :
      bridgeBoundaries ≡ canonicalQualiaTranscriptPNFBoundaries

qualiaTranscriptPNFSemanticBridgeFromSurface :
  (surface : QualiaTranscriptSurface) →
  QualiaTranscriptPNFSemanticBridge surface
qualiaTranscriptPNFSemanticBridgeFromSurface surface =
  record
    { sourceSurface =
        surface
    ; sourceSurfaceIsInput =
        refl
    ; transcriptAtom =
        transcriptDiscussionPNFAtom
    ; colorBreathingAtom =
        colorBreathingPNFAtom
    ; timeNonlinearityAtom =
        timeNonlinearityPNFAtom
    ; egoDissolutionAtom =
        egoDissolutionPNFAtom
    ; ineffabilityAtom =
        ineffabilityPNFAtom
    ; noSemanticTruthAuthorityAtom =
        noSemanticTruthAuthorityPNFAtom
    ; noSpeakerExperienceVerificationAtom =
        noSpeakerExperienceVerificationPNFAtom
    ; noPhenomenalContentRecoveryAtom =
        noPhenomenalContentRecoveryPNFAtom
    ; listedAtoms =
        canonicalQualiaTranscriptPNFAtoms
    ; listedAtomsAreCanonical =
        refl
    ; wrappedAtoms =
        canonicalWrappedQualiaTranscriptPNFAtoms
    ; wrappedAtomsAreCanonical =
        refl
    ; transcriptWrapperIsAttributedEvidence =
        refl
    ; colorWrapperIsAttributedEvidence =
        refl
    ; timeWrapperIsAttributedEvidence =
        refl
    ; egoWrapperIsAttributedEvidence =
        refl
    ; ineffabilityWrapperIsAttributedEvidence =
        refl
    ; noSemanticTruthAuthorityWrapperIsAttributedEvidence =
        refl
    ; noSpeakerExperienceVerificationWrapperIsAttributedEvidence =
        refl
    ; noPhenomenalContentRecoveryWrapperIsAttributedEvidence =
        refl
    ; colorProvenancePreserved =
        refl
    ; timeProvenancePreserved =
        refl
    ; egoProvenancePreserved =
        refl
    ; ineffabilityProvenancePreserved =
        refl
    ; colorTruthAuthorityResidualLevel =
        colorTruthAuthorityResidual
    ; colorTruthAuthorityResidualComesFromPNFComputation =
        refl
    ; colorTruthAuthorityNoTypedMeet =
        colorTruthAuthorityResidualIsNoTypedMeet
    ; pnfSemanticTruthAuthorityField =
        pnfSemanticTruthAuthority
    ; pnfSemanticTruthAuthorityFieldIsFalse =
        pnfSemanticTruthAuthorityIsFalse
    ; speakerExperienceVerificationField =
        speakerExperienceVerification
    ; speakerExperienceVerificationFieldIsFalse =
        speakerExperienceVerificationIsFalse
    ; phenomenalContentRecoveryField =
        phenomenalContentRecovery
    ; phenomenalContentRecoveryFieldIsFalse =
        phenomenalContentRecoveryIsFalse
    ; bridgeBoundaries =
        canonicalQualiaTranscriptPNFBoundaries
    ; bridgeBoundariesAreCanonical =
        refl
    }

record QualiaTranscriptPNFSemanticBridgeCertificate : Set₁ where
  field
    surface :
      QualiaTranscriptSurface

    bridge :
      QualiaTranscriptPNFSemanticBridge surface

    atomList :
      List Residual.PredicatePNF

    atomListMatchesBridge :
      atomList
      ≡
      QualiaTranscriptPNFSemanticBridge.listedAtoms bridge

    wrappedAtomList :
      List EvidenceWrappedTranscriptPNFAtom

    wrappedAtomListMatchesBridge :
      wrappedAtomList
      ≡
      QualiaTranscriptPNFSemanticBridge.wrappedAtoms bridge

    semanticTruthAuthorityCertificate :
      Bool

    semanticTruthAuthorityCertificateIsFalse :
      semanticTruthAuthorityCertificate ≡ false

    speakerExperienceVerificationCertificate :
      Bool

    speakerExperienceVerificationCertificateIsFalse :
      speakerExperienceVerificationCertificate ≡ false

    phenomenalContentRecoveryCertificate :
      Bool

    phenomenalContentRecoveryCertificateIsFalse :
      phenomenalContentRecoveryCertificate ≡ false

qualiaTranscriptPNFSemanticBridgeCertificateFromSurface :
  (surface : QualiaTranscriptSurface) →
  QualiaTranscriptPNFSemanticBridgeCertificate
qualiaTranscriptPNFSemanticBridgeCertificateFromSurface surface =
  record
    { surface =
        surface
    ; bridge =
        qualiaTranscriptPNFSemanticBridgeFromSurface surface
    ; atomList =
        canonicalQualiaTranscriptPNFAtoms
    ; atomListMatchesBridge =
        refl
    ; wrappedAtomList =
        canonicalWrappedQualiaTranscriptPNFAtoms
    ; wrappedAtomListMatchesBridge =
        refl
    ; semanticTruthAuthorityCertificate =
        pnfSemanticTruthAuthority
    ; semanticTruthAuthorityCertificateIsFalse =
        pnfSemanticTruthAuthorityIsFalse
    ; speakerExperienceVerificationCertificate =
        speakerExperienceVerification
    ; speakerExperienceVerificationCertificateIsFalse =
        speakerExperienceVerificationIsFalse
    ; phenomenalContentRecoveryCertificate =
        phenomenalContentRecovery
    ; phenomenalContentRecoveryCertificateIsFalse =
        phenomenalContentRecoveryIsFalse
    }
