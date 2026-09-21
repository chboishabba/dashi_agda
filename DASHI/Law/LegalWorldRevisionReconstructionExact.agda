module DASHI.Law.LegalWorldRevisionReconstructionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Core.AppendOnlyEvidenceResidualRevisionExact as Revision
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query

------------------------------------------------------------------------
-- S18: first-class legal worlds / authority validity / jurisdiction scope /
-- source revision invalidation / affected proof cone.
------------------------------------------------------------------------

data DemoTime : Set where t1 t2 : DemoTime
data DemoJurisdiction : Set where qld nsw : DemoJurisdiction
data DemoAuthority : Set where oldAuthority successorAuthority : DemoAuthority

record LegalWorld : Set where
  constructor legalWorld
  field
    worldRef : String
    matterRef : String
    jurisdiction : DemoJurisdiction
    asAt : DemoTime
    sourceRevisionRef : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false
    createsClaimTruth : Bool
    createsClaimTruthIsFalse :
      createsClaimTruth ≡ false

open LegalWorld public

record AuthorityValidity : Set where
  constructor authorityValidity
  field
    authority : DemoAuthority
    jurisdiction : DemoJurisdiction
    activeAtT1 : Bool
    activeAtT2 : Bool
    supersessionRef : String

open AuthorityValidity public

oldAuthorityValidity : AuthorityValidity
oldAuthorityValidity =
  authorityValidity oldAuthority qld true false "successorAuthority"

successorAuthorityValidity : AuthorityValidity
successorAuthorityValidity =
  authorityValidity successorAuthority qld false true "oldAuthority"

activeAt : AuthorityValidity → LegalWorld → Bool
activeAt validity world with AuthorityValidity.jurisdiction validity | LegalWorld.LegalWorld.jurisdiction world
... | qld | qld with asAt world
...   | t1 = activeAtT1 validity
...   | t2 = activeAtT2 validity
... | nsw | nsw with asAt world
...   | t1 = activeAtT1 validity
...   | t2 = activeAtT2 validity
... | qld | nsw = false
... | nsw | qld = false

qldT1World : LegalWorld
qldT1World =
  legalWorld "world:qld:t1" "matter:fixture" qld t1 "revision:1"
    true refl false refl false refl

qldT2World : LegalWorld
qldT2World =
  legalWorld "world:qld:t2" "matter:fixture" qld t2 "revision:2"
    true refl false refl false refl

nswT1World : LegalWorld
nswT1World =
  legalWorld "world:nsw:t1" "matter:fixture" nsw t1 "revision:1"
    true refl false refl false refl

oldAuthorityActiveAtT1 :
  activeAt oldAuthorityValidity qldT1World ≡ true
oldAuthorityActiveAtT1 = refl

oldAuthorityInactiveAtT2 :
  activeAt oldAuthorityValidity qldT2World ≡ false
oldAuthorityInactiveAtT2 = refl

oldAuthorityNotActiveInWrongJurisdiction :
  activeAt oldAuthorityValidity nswT1World ≡ false
oldAuthorityNotActiveInWrongJurisdiction = refl

------------------------------------------------------------------------
-- Jurisdiction-scoped query adequacy.
------------------------------------------------------------------------

data JurisdictionObservation : Set where qldSurface nswSurface : JurisdictionObservation
data JurisdictionQuery : Set where askQldOutcome : JurisdictionQuery
data JurisdictionAnswer : Set where qldAnswer nswAnswer : JurisdictionAnswer

jurisdictionProject : LegalWorld → JurisdictionObservation
jurisdictionProject world with LegalWorld.jurisdiction world
... | qld = qldSurface
... | nsw = nswSurface

jurisdictionAnswer : JurisdictionQuery → LegalWorld → JurisdictionAnswer
jurisdictionAnswer askQldOutcome world with LegalWorld.jurisdiction world
... | qld = qldAnswer
... | nsw = nswAnswer

jurisdictionSemantics :
  Query.QuerySemantics LegalWorld JurisdictionQuery JurisdictionAnswer
jurisdictionSemantics =
  Query.querySemantics jurisdictionAnswer

jurisdictionFactorisation :
  (world : LegalWorld) →
  jurisdictionAnswer askQldOutcome world
  ≡
  (λ { qldSurface → qldAnswer
     ; nswSurface → nswAnswer })
    (jurisdictionProject world)
jurisdictionFactorisation world with LegalWorld.jurisdiction world
... | qld = refl
... | nsw = refl

jurisdictionProjectionAdequate :
  Query.AdequateFor
    jurisdictionProject
    jurisdictionSemantics
    askQldOutcome
jurisdictionProjectionAdequate =
  Query.factorsForQuery
    (λ { qldSurface → qldAnswer
       ; nswSurface → nswAnswer })
    jurisdictionFactorisation

------------------------------------------------------------------------
-- Revision change -> exact dependency reopening path.
------------------------------------------------------------------------

data LegalArtifact : Set where
  sourceRevision propositionA propositionB queryProof : LegalArtifact

data Depends : LegalArtifact → LegalArtifact → Set where
  sourceToA : Depends sourceRevision propositionA
  aToB : Depends propositionA propositionB
  bToProof : Depends propositionB queryProof

sourceRevisionReopensA :
  Dependency.ReopeningObligation Depends sourceRevision propositionA
sourceRevisionReopensA =
  Dependency.oneEdgeCreatesReopeningObligation sourceToA

aReopensB :
  Dependency.ReopeningObligation Depends propositionA propositionB
aReopensB =
  Dependency.oneEdgeCreatesReopeningObligation aToB

bReopensProof :
  Dependency.ReopeningObligation Depends propositionB queryProof
bReopensProof =
  Dependency.oneEdgeCreatesReopeningObligation bToProof

sourceRevisionReopensProof :
  Dependency.ReopeningObligation Depends sourceRevision queryProof
sourceRevisionReopensProof =
  Dependency.obligationsCompose
    (Dependency.obligationsCompose sourceRevisionReopensA aReopensB)
    bReopensProof

appendOnlyRevisionBoundaryReused :
  Revision.AppendOnlyEvidenceRevisionBoundary
appendOnlyRevisionBoundaryReused =
  Revision.canonicalAppendOnlyEvidenceRevisionBoundary

data RevisionAutomaticallyRefutesPriorProposition : Set where
data WrongJurisdictionAutomaticallyPaysJurisdictionAxis : Set where

revisionDoesNotAutomaticallyRefutePriorProposition :
  RevisionAutomaticallyRefutesPriorProposition → ⊥
revisionDoesNotAutomaticallyRefutePriorProposition ()

wrongJurisdictionCannotAutomaticallyPayAxis :
  WrongJurisdictionAutomaticallyPaysJurisdictionAxis → ⊥
wrongJurisdictionCannotAutomaticallyPayAxis ()

record LegalWorldRevisionReconstructionBoundary : Set where
  constructor legalWorldRevisionReconstructionBoundary
  field
    legalWorldCarriesTimeJurisdictionAndRevision : Bool
    legalWorldCarriesTimeJurisdictionAndRevisionIsTrue :
      legalWorldCarriesTimeJurisdictionAndRevision ≡ true

    authorityValidityIsWorldRelative : Bool
    authorityValidityIsWorldRelativeIsTrue :
      authorityValidityIsWorldRelative ≡ true

    jurisdictionAxisMustMatchQueryWorld : Bool
    jurisdictionAxisMustMatchQueryWorldIsTrue :
      jurisdictionAxisMustMatchQueryWorld ≡ true

    sourceRevisionMayReopenDirectDependents : Bool
    sourceRevisionMayReopenDirectDependentsIsTrue :
      sourceRevisionMayReopenDirectDependents ≡ true

    sourceRevisionMayReopenProofConeTransitively : Bool
    sourceRevisionMayReopenProofConeTransitivelyIsTrue :
      sourceRevisionMayReopenProofConeTransitively ≡ true

    revisionAutomaticallyRefutesPriorEvidence : Bool
    revisionAutomaticallyRefutesPriorEvidenceIsFalse :
      revisionAutomaticallyRefutesPriorEvidence ≡ false

    revisionReopeningCreatesClaimTruth : Bool
    revisionReopeningCreatesClaimTruthIsFalse :
      revisionReopeningCreatesClaimTruth ≡ false

open LegalWorldRevisionReconstructionBoundary public

canonicalLegalWorldRevisionReconstructionBoundary :
  LegalWorldRevisionReconstructionBoundary
canonicalLegalWorldRevisionReconstructionBoundary =
  legalWorldRevisionReconstructionBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl