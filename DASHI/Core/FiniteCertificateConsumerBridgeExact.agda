module DASHI.Core.FiniteCertificateConsumerBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.FrontierRelationStrengthBidiExact as Relation
import DASHI.Analysis.DeBruijnNewman2026SourceWeldExact as DBN
import DASHI.Mathematics.NumberTheory.PrimePowerDiophantineTuple2026SourceExact as Dujella

------------------------------------------------------------------------
-- FINITE CERTIFICATE -> EXACT CONSUMER BRIDGE
--
-- Repository-native extraction of the common architecture seen in the 2026
-- DBN candidate and Dujella Appendix-A certificate.  This is DASHI machinery,
-- not a theorem attributed to either source.
--
-- A finite replay becomes theorem-relevant only after it is tied to the exact
-- source parameters/object and an interpretation theorem connects the replayed
-- finite predicate to the target mathematical consumer.
------------------------------------------------------------------------

record FiniteCertificateProblem : Set₁ where
  constructor finiteCertificateProblem
  field
    Parameter : Set
    Certificate : Set
    ReplayOutput : Set
    ConsumerClaim : Set
    parameterReference : Parameter → String
    certificateReference : Certificate → String
    replay : Parameter → Certificate → ReplayOutput
    accepted : ReplayOutput → Set
    targetConsumerReference : String

open FiniteCertificateProblem public

record SameParameterReceipt (problem : FiniteCertificateProblem) : Set₁ where
  constructor sameParameterReceipt
  field
    parameter : Parameter problem
    certificate : Certificate problem
    certificateBelongsToParameter : Set

open SameParameterReceipt public

record ExactReplayReceipt
    (problem : FiniteCertificateProblem)
    (same : SameParameterReceipt problem) : Set₁ where
  constructor exactReplayReceipt
  field
    replayAccepted : accepted problem
      (replay problem (parameter same) (certificate same))
    replayImplementationReference : String
    replayDependencyReference : String

open ExactReplayReceipt public

record ReplayInterpretation
    (problem : FiniteCertificateProblem)
    (same : SameParameterReceipt problem) : Set₁ where
  constructor replayInterpretation
  field
    claim : ConsumerClaim problem
    acceptedReplayImpliesClaim :
      accepted problem (replay problem (parameter same) (certificate same)) →
      Set
    interpretationReference : String

open ReplayInterpretation public

record CertificateConsumerClosure (problem : FiniteCertificateProblem) : Set₂ where
  constructor certificateConsumerClosure
  field
    same : SameParameterReceipt problem
    replayReceipt : ExactReplayReceipt problem same
    interpretation : ReplayInterpretation problem same
    exactConsumerMatch : Set
    sourceAuthorityAdequacy : Set

open CertificateConsumerClosure public

------------------------------------------------------------------------
-- The anti-promotion boundary is structural: replay alone has no constructor
-- for consumer closure.  Likewise a certificate schema shared across domains
-- carries reuse capability but no theorem-transfer capability.
------------------------------------------------------------------------

data CertificateEvidenceStage : Set where
  certificateDescribed
  certificateBytesRecovered
  replaySucceeded
  interpretationProved
  consumerClosed
  : CertificateEvidenceStage

replayNotConsumerClosure : replaySucceeded ≡ consumerClosed → ⊥
replayNotConsumerClosure ()

descriptionNotReplay : certificateDescribed ≡ replaySucceeded → ⊥
descriptionNotReplay ()

certificateReuseKind : Relation.RelationKind
certificateReuseKind = Relation.exactCertificateSchemaReuse

certificateReuseCapability : Relation.ReuseCapability certificateReuseKind
certificateReuseCapability = Relation.reuseExactCertificateSchema

certificateSchemaHasNoDirectTheoremTransfer :
  Relation.TheoremTransferCapability certificateReuseKind → ⊥
certificateSchemaHasNoDirectTheoremTransfer =
  Relation.certificateSchemaCannotDirectlyTransferTheorem

------------------------------------------------------------------------
-- Current 2026 instantiations remain external at the replay layer.
------------------------------------------------------------------------

dbnReplayOwnedHere : Bool
dbnReplayOwnedHere = DBN.candidateCertificateReplayOwnedInAgda

dbnReplayStillOpen : dbnReplayOwnedHere ≡ false
dbnReplayStillOpen = DBN.candidateCertificateReplayOwnedInAgdaIsFalse

dujellaReplayStage : Dujella.CertificateStage
dujellaReplayStage = Dujella.sourceAppendixCertificateStage

dujellaDescriptionNotAgdaReplay :
  dujellaReplayStage ≡ Dujella.replayedInsideAgda → ⊥
dujellaDescriptionNotAgdaReplay = Dujella.sourceDescriptionIsNotAgdaReplay

------------------------------------------------------------------------
-- Boundary used by RH/NS/YM: finite numerical work can close a finite leaf
-- only when an exact interpretation/same-object bridge exists.  It cannot by
-- itself replace an infinite-dimensional analytic or physical premise.
------------------------------------------------------------------------

record FiniteCertificateBoundary : Set where
  constructor finiteCertificateBoundary
  field
    exactReplayCanBeUseful : Bool
    exactReplayCanBeUsefulIsTrue : exactReplayCanBeUseful ≡ true
    replayAloneIsTheoremAuthority : Bool
    replayAloneIsTheoremAuthorityIsFalse : replayAloneIsTheoremAuthority ≡ false
    sameNumberImpliesSameConsumer : Bool
    sameNumberImpliesSameConsumerIsFalse : sameNumberImpliesSameConsumer ≡ false
    interpretationTheoremRequired : Bool
    interpretationTheoremRequiredIsTrue : interpretationTheoremRequired ≡ true
    sameParameterReceiptRequired : Bool
    sameParameterReceiptRequiredIsTrue : sameParameterReceiptRequired ≡ true

canonicalFiniteCertificateBoundary : FiniteCertificateBoundary
canonicalFiniteCertificateBoundary =
  finiteCertificateBoundary
    true refl
    false refl
    false refl
    true refl
    true refl
