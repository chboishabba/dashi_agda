module DASHI.Law.HerzogFascismAntifascistAmalekCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.HerzogBodycamQuotedUtteranceProvenanceExact as Bodycam
import DASHI.Law.GenocideFascismSourceGenealogyExact as GenocideFascism
import DASHI.Law.FascismAtrocitySourceCrossPollinationExact as Fascism
import DASHI.Governance.AmalekProvenanceRoleBinding as Amalek
import DASHI.Governance.TraumaExploitationAttractor as Trauma

------------------------------------------------------------------------
-- Cross-pollination architecture.
--
-- Fascistic mechanisms are audited through terminalisation, collective-guilt
-- transport, distinction erasure, provenance weaponisation and asymmetric
-- routing.  Amalek remains a provenance-bearing role-binding/command-transport
-- problem, never an identity label for a present-day people.  Antifascism is
-- represented constructively as interruption of the reproduction operator and
-- reopening/preservation of correction and distinction channels.
------------------------------------------------------------------------

data AntiFascistMechanism : Set where
  restoreDistinctions : AntiFascistMechanism
  reopenCorrectionChannel : AntiFascistMechanism
  blockCollectiveGuiltTransport : AntiFascistMechanism
  blockTerminalisation : AntiFascistMechanism
  interruptCoerciveRecursion : AntiFascistMechanism
  preserveSourceProvenance : AntiFascistMechanism
  protectTargetedCivilianStatus : AntiFascistMechanism

record AntiFascistAuditFibre : Set where
  constructor antiFascistAuditFibre
  field
    distinctionRepair : Bool
    correctionChannelOpen : Bool
    collectiveGuiltBlocked : Bool
    terminalisationBlocked : Bool
    coerciveRecursionInterrupted : Bool
    provenancePreserved : Bool
    auditReference : String

open AntiFascistAuditFibre public

canonicalAntiFascistTarget : AntiFascistAuditFibre
canonicalAntiFascistTarget = antiFascistAuditFibre
  true true true true true true
  "normative/architectural target: interrupt terminalising coercive recursion while preserving source provenance and correction"

------------------------------------------------------------------------
-- Adapter to existing antifascist interruption owner.
------------------------------------------------------------------------

record AntiFascistInterruptionAdapter (S : Trauma.TraumaExploitationSystem) : Set₁ where
  constructor antiFascistInterruptionAdapter
  field
    interruption : Trauma.Interruption S
    preservesCorrectionChannel : Bool
    preservesCorrectionChannelIsTrue : preservesCorrectionChannel ≡ true
    refusesCollectiveEnemyEssentialism : Bool
    refusesCollectiveEnemyEssentialismIsTrue : refusesCollectiveEnemyEssentialism ≡ true

open AntiFascistInterruptionAdapter public

------------------------------------------------------------------------
-- Amalek promotion-chain audit.
--
-- A contemporary application must separately establish role binding, command
-- transport, collective propagation and terminalisation.  No scriptural source
-- or political association gets to skip those stages.
------------------------------------------------------------------------

data AmalekAuditCoordinate : Set where
  sourceProvenance : AmalekAuditCoordinate
  modernRoleBinding : AmalekAuditCoordinate
  commandTransport : AmalekAuditCoordinate
  collectivePropagation : AmalekAuditCoordinate
  terminalisationEvidence : AmalekAuditCoordinate

data AmalekAuditStatus : Set where
  sourceClosed : AmalekAuditStatus
  evidenceOpen : AmalekAuditStatus
  evidenceClosed : AmalekAuditStatus

canonicalAmalekAuditStatus : AmalekAuditCoordinate → AmalekAuditStatus
canonicalAmalekAuditStatus sourceProvenance = sourceClosed
canonicalAmalekAuditStatus modernRoleBinding = evidenceOpen
canonicalAmalekAuditStatus commandTransport = evidenceOpen
canonicalAmalekAuditStatus collectivePropagation = evidenceOpen
canonicalAmalekAuditStatus terminalisationEvidence = evidenceOpen

amalekBoundary : Amalek.AmalekBoundary
amalekBoundary = Amalek.canonicalAmalekBoundary

amalekIsNotTerminalisationByDefinition :
  Amalek.amalekEqualsTerminalisation amalekBoundary ≡ false
amalekIsNotTerminalisationByDefinition = refl

amalekCommandTransportNeedsEvidence :
  Amalek.commandTransportRequiresSeparateEvidence amalekBoundary ≡ true
amalekCommandTransportNeedsEvidence = refl

------------------------------------------------------------------------
-- Bodycam incident -> fascism-feature audit.
-- The utterance is evidence of recorded demeaning/celebratory language around
-- force, but one exchange cannot by itself establish unit policy or a complete
-- fascism diagnosis.  It can, however, be an input to a corpus-scale audit of
-- coercive culture, dehumanisation, correction closure and asymmetric routing.
------------------------------------------------------------------------

data BodycamFascismAuditCoordinate : Set where
  exactUtterance : BodycamFascismAuditCoordinate
  firstPersonConductClaim : BodycamFascismAuditCoordinate
  celebratoryReaction : BodycamFascismAuditCoordinate
  demeaningVictimReference : BodycamFascismAuditCoordinate
  forceAgainstDownedPersonClaim : BodycamFascismAuditCoordinate
  crossOfficerNormalisation : BodycamFascismAuditCoordinate
  commandTolerance : BodycamFascismAuditCoordinate
  institutionalTolerance : BodycamFascismAuditCoordinate
  correctionFailure : BodycamFascismAuditCoordinate

data AuditClosure : Set where
  quoteBacked : AuditClosure
  incidentBacked : AuditClosure
  corpusRequired : AuditClosure
  commandEvidenceRequired : AuditClosure
  institutionalEvidenceRequired : AuditClosure

bodycamAuditClosure : BodycamFascismAuditCoordinate → AuditClosure
bodycamAuditClosure exactUtterance = quoteBacked
bodycamAuditClosure firstPersonConductClaim = quoteBacked
bodycamAuditClosure celebratoryReaction = quoteBacked
bodycamAuditClosure demeaningVictimReference = quoteBacked
bodycamAuditClosure forceAgainstDownedPersonClaim = quoteBacked
bodycamAuditClosure crossOfficerNormalisation = corpusRequired
bodycamAuditClosure commandTolerance = commandEvidenceRequired
bodycamAuditClosure institutionalTolerance = institutionalEvidenceRequired
bodycamAuditClosure correctionFailure = corpusRequired

bodycamFeedsProvenanceWeaponisationAudit : Fascism.FascismFeature
bodycamFeedsProvenanceWeaponisationAudit = Fascism.provenanceWeaponisation

bodycamFeedsCoerciveContractionAudit : Fascism.FascismFeature
bodycamFeedsCoerciveContractionAudit = Fascism.coerciveContraction

------------------------------------------------------------------------
-- Genocide/fascism x Amalek.
-- Genocide can be classified as fascistic terminalisation through the sourced
-- genealogy + DASHI synthesis without identifying the targeted population as
-- Amalek.  If explicit Amalek rhetoric is alleged to have influenced policy,
-- that is a separate role-binding and command-transport empirical chain.
------------------------------------------------------------------------

genocideIsFascisticTerminalisation :
  GenocideFascism.genocideMechanismClassification
  ≡ GenocideFascism.fascisticTerminalisationMechanism
genocideIsFascisticTerminalisation = refl

record GenocideAmalekBoundary : Set where
  constructor genocideAmalekBoundary
  field
    genocideClassificationRequiresTargetToBeCalledAmalek : Bool
    genocideClassificationRequiresTargetToBeCalledAmalekIsFalse : genocideClassificationRequiresTargetToBeCalledAmalek ≡ false
    amalekRhetoricAutomaticallyProvesGenocide : Bool
    amalekRhetoricAutomaticallyProvesGenocideIsFalse : amalekRhetoricAutomaticallyProvesGenocide ≡ false
    explicitAmalekRhetoricAutomaticallyProvesPolicyCommandTransport : Bool
    explicitAmalekRhetoricAutomaticallyProvesPolicyCommandTransportIsFalse : explicitAmalekRhetoricAutomaticallyProvesPolicyCommandTransport ≡ false
    inheritedCollectiveGuiltPermitted : Bool
    inheritedCollectiveGuiltPermittedIsFalse : inheritedCollectiveGuiltPermitted ≡ false

canonicalGenocideAmalekBoundary : GenocideAmalekBoundary
canonicalGenocideAmalekBoundary =
  genocideAmalekBoundary false refl false refl false refl false refl

------------------------------------------------------------------------
-- BIDI cross-pollination claims.
------------------------------------------------------------------------

data CrossClaim : Set where
  bodycamLiteralQuoteEstablished : CrossClaim
  bodycamShowsInstitutionalFascistCulture : CrossClaim
  genocideIsFascisticTerminalisationClaim : CrossClaim
  contemporaryAmalekCommandTransportClaim : CrossClaim
  antifascistInterruptionRequired : CrossClaim

data CrossProducer : Set where
  bodycamQuoteProducer : CrossProducer
  crossOfficerInstitutionalCultureProducer : CrossProducer
  genocideFindingAndSourceGenealogyProducer : CrossProducer
  amalekRoleBindingAndCommandTransportProducer : CrossProducer
  interruptionAndCorrectionProducer : CrossProducer

reverseCross : CrossClaim → CrossProducer
reverseCross bodycamLiteralQuoteEstablished = bodycamQuoteProducer
reverseCross bodycamShowsInstitutionalFascistCulture = crossOfficerInstitutionalCultureProducer
reverseCross genocideIsFascisticTerminalisationClaim = genocideFindingAndSourceGenealogyProducer
reverseCross contemporaryAmalekCommandTransportClaim = amalekRoleBindingAndCommandTransportProducer
reverseCross antifascistInterruptionRequired = interruptionAndCorrectionProducer

record CrossPollinationBoundary : Set where
  constructor crossPollinationBoundary
  field
    exactBodycamQuoteMayBeSanitisedAway : Bool
    exactBodycamQuoteMayBeSanitisedAwayIsFalse : exactBodycamQuoteMayBeSanitisedAway ≡ false
    oneBodycamExchangeProvesWholeInstitutionFascist : Bool
    oneBodycamExchangeProvesWholeInstitutionFascistIsFalse : oneBodycamExchangeProvesWholeInstitutionFascist ≡ false
    antifascismMeansCollectivePunishmentOfOpposingIdentity : Bool
    antifascismMeansCollectivePunishmentOfOpposingIdentityIsFalse : antifascismMeansCollectivePunishmentOfOpposingIdentity ≡ false
    antifascistInterruptionPreservesEvidenceAndCorrection : Bool
    antifascistInterruptionPreservesEvidenceAndCorrectionIsTrue : antifascistInterruptionPreservesEvidenceAndCorrection ≡ true

canonicalCrossPollinationBoundary : CrossPollinationBoundary
canonicalCrossPollinationBoundary =
  crossPollinationBoundary false refl false refl false refl true refl
