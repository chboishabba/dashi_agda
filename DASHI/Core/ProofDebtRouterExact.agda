module DASHI.Core.ProofDebtRouterExact where

------------------------------------------------------------------------
-- PROOF-DEBT ROUTER
--
-- A missing local proof is not automatically missing mathematics.
-- Established-source mathematics, statement/transcription alignment, and
-- kernel certification are independent coordinates.
--
-- The critical firewall is constructive: a deferred source receipt below
-- contains provenance/alignment evidence but deliberately contains no
-- inhabitant of the theorem proposition T.  Downstream development may be
-- checked conditionally as T -> Result.  Promotion to a certified theorem
-- requires an actual inhabitant of T supplied separately.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

data ClaimKind : Set where
  deductiveTheorem empiricalPremise : ClaimKind

data MathematicalStatus : Set where
  novelOpen sourceEstablished experimentallySupportedPremise derivedInRepo : MathematicalStatus

data StatementStatus : Set where
  notTranscribed transcribedUnaligned sourceAligned : StatementStatus

data CertificationStatus : Set where
  uncertified proofDeferred leanKernelCertified agdaKernelCertified : CertificationStatus

data PreferredBackend : Set where
  localAgda externalLean aristotleLean sourceOnly : PreferredBackend

data DebtClass : Set where
  mathematicalDebt transcriptionDebt certificationDebt empiricalEvidenceDebt noDebt : DebtClass

routeDebt :
  ClaimKind -> MathematicalStatus -> StatementStatus -> CertificationStatus -> DebtClass
routeDebt _ novelOpen _ _ = mathematicalDebt
routeDebt _ sourceEstablished notTranscribed _ = transcriptionDebt
routeDebt _ sourceEstablished transcribedUnaligned _ = transcriptionDebt
routeDebt _ sourceEstablished sourceAligned uncertified = certificationDebt
routeDebt _ sourceEstablished sourceAligned proofDeferred = certificationDebt
routeDebt _ sourceEstablished sourceAligned leanKernelCertified = noDebt
routeDebt _ sourceEstablished sourceAligned agdaKernelCertified = noDebt
routeDebt _ derivedInRepo notTranscribed _ = transcriptionDebt
routeDebt _ derivedInRepo transcribedUnaligned _ = transcriptionDebt
routeDebt _ derivedInRepo sourceAligned uncertified = certificationDebt
routeDebt _ derivedInRepo sourceAligned proofDeferred = certificationDebt
routeDebt _ derivedInRepo sourceAligned leanKernelCertified = noDebt
routeDebt _ derivedInRepo sourceAligned agdaKernelCertified = noDebt
routeDebt deductiveTheorem experimentallySupportedPremise _ _ = mathematicalDebt
routeDebt empiricalPremise experimentallySupportedPremise notTranscribed _ = transcriptionDebt
routeDebt empiricalPremise experimentallySupportedPremise transcribedUnaligned _ = transcriptionDebt
routeDebt empiricalPremise experimentallySupportedPremise sourceAligned uncertified = empiricalEvidenceDebt
routeDebt empiricalPremise experimentallySupportedPremise sourceAligned proofDeferred = empiricalEvidenceDebt
routeDebt empiricalPremise experimentallySupportedPremise sourceAligned leanKernelCertified = noDebt
routeDebt empiricalPremise experimentallySupportedPremise sourceAligned agdaKernelCertified = noDebt

sourceEstablishedAlignedDeferredIsCertificationDebt :
  routeDebt deductiveTheorem sourceEstablished sourceAligned proofDeferred ≡ certificationDebt
sourceEstablishedAlignedDeferredIsCertificationDebt = refl

sourceEstablishedAlignedDeferredIsNotMathematicalDebt :
  ¬ (routeDebt deductiveTheorem sourceEstablished sourceAligned proofDeferred ≡ mathematicalDebt)
sourceEstablishedAlignedDeferredIsNotMathematicalDebt ()

experimentDoesNotTurnDeductiveTheoremIntoEstablishedTheorem :
  routeDebt deductiveTheorem experimentallySupportedPremise sourceAligned proofDeferred ≡ mathematicalDebt
experimentDoesNotTurnDeductiveTheoremIntoEstablishedTheorem = refl

record SourceIdentity : Set where
  constructor source-identity
  field
    responsibleBody : String
    title : String
    stableIdentifier : String
    exactCarrier : String
    inspectedRevisionOrDate : String

open SourceIdentity public

record StatementAlignmentReceipt : Set where
  constructor statement-alignment-receipt
  field
    exactSourceClaim : String
    exactLocalStatement : String
    hypothesesAligned : Bool
    quantifiersAligned : Bool
    domainAligned : Bool
    uniformityAligned : Bool
    conclusionDirectionAligned : Bool
    allRequiredCoordinatesAligned : Bool

open StatementAlignmentReceipt public

record FullyAligned (a : StatementAlignmentReceipt) : Set where
  constructor fully-aligned
  field
    hypothesesOK : hypothesesAligned a ≡ true
    quantifiersOK : quantifiersAligned a ≡ true
    domainOK : domainAligned a ≡ true
    uniformityOK : uniformityAligned a ≡ true
    conclusionOK : conclusionDirectionAligned a ≡ true
    allCoordinatesOK : allRequiredCoordinatesAligned a ≡ true

open FullyAligned public

record SourceAlignedDeferredTheorem (T : Set) : Set where
  constructor source-aligned-deferred-theorem
  field
    source : SourceIdentity
    alignment : StatementAlignmentReceipt
    alignmentVerified : FullyAligned alignment
    preferredBackend : PreferredBackend

open SourceAlignedDeferredTheorem public

-- Conditional development is kernel-checkable without manufacturing T.
ConditionalDevelopment : Set -> Set -> Set
ConditionalDevelopment T Result = T -> Result

runConditionalDevelopment :
  {T Result : Set} -> ConditionalDevelopment T Result -> T -> Result
runConditionalDevelopment downstream theorem = downstream theorem

record CertifiedKnownTheorem (T : Set) : Set where
  constructor certified-known-theorem
  field
    deferredReceipt : SourceAlignedDeferredTheorem T
    theorem : T
    backend : PreferredBackend
    certification : CertificationStatus

open CertifiedKnownTheorem public

-- There is intentionally no function SourceAlignedDeferredTheorem T -> T.
-- Certification can only be constructed after an actual theorem inhabitant
-- is supplied by a local proof or an externally kernel-checked proof import.
certifyDeferred :
  {T : Set} ->
  SourceAlignedDeferredTheorem T ->
  T ->
  PreferredBackend ->
  CertificationStatus ->
  CertifiedKnownTheorem T
certifyDeferred receipt proof backendUsed status =
  certified-known-theorem receipt proof backendUsed status

data AlignmentResidual : Set where
  missingSourceStatement
  missingHypothesisAlignment
  missingQuantifierAlignment
  missingDomainAlignment
  missingUniformityAlignment
  missingConclusionAlignment : AlignmentResidual

record ProofDebtRoutingReceipt : Set where
  constructor proof-debt-routing-receipt
  field
    claimKind : ClaimKind
    mathematicalStatus : MathematicalStatus
    statementStatus : StatementStatus
    certificationStatus : CertificationStatus
    scheduledBackend : PreferredBackend
    routedDebt : DebtClass
    routingExact : routedDebt ≡ routeDebt claimKind mathematicalStatus statementStatus certificationStatus

open ProofDebtRoutingReceipt public

canonicalEstablishedDeferredRoute : ProofDebtRoutingReceipt
canonicalEstablishedDeferredRoute =
  proof-debt-routing-receipt
    deductiveTheorem
    sourceEstablished
    sourceAligned
    proofDeferred
    externalLean
    certificationDebt
    refl

canonicalEstablishedDeferredRouteNotNovel :
  routedDebt canonicalEstablishedDeferredRoute ≡ certificationDebt
canonicalEstablishedDeferredRouteNotNovel = refl
