module DASHI.Interop.SLRConsumerRequirementV2Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRSpacyObservationWorldCompilerParityExact as Compiler

------------------------------------------------------------------------
-- SLRC V2 TYPED CONSUMER REQUIREMENTS
--
-- Runtime owner:
--   chboishabba/slr :: crates/sl-consumer-residual
--
-- Production SLRC version 2 adds an explicit requirement-class tag:
--   1 = parser/PNF fragment requirement
--   2 = substantive evidence-coordinate requirement
-- followed by the class-owned value tag and the existing source scope.
-- Legacy v1 remains decode-only for replay of paid smoke receipts.
------------------------------------------------------------------------

consumerWireVersion : Nat
consumerWireVersion = 2

legacyConsumerWireVersion : Nat
legacyConsumerWireVersion = 1

data RequirementClass : Set where
  pnfFragmentRequirement : RequirementClass
  evidenceCoordinateRequirement : RequirementClass

requirementClassTag : RequirementClass → Nat
requirementClassTag pnfFragmentRequirement = 1
requirementClassTag evidenceCoordinateRequirement = 2

data EvidenceCoordinateKind : Set where
  sourceIdentity : EvidenceCoordinateKind
  sameObject : EvidenceCoordinateKind
  authority : EvidenceCoordinateKind
  mechanism : EvidenceCoordinateKind
  quantification : EvidenceCoordinateKind
  probability : EvidenceCoordinateKind
  counterfactual : EvidenceCoordinateKind
  instrumentComparison : EvidenceCoordinateKind
  incidence : EvidenceCoordinateKind
  classification : EvidenceCoordinateKind

evidenceCoordinateTag : EvidenceCoordinateKind → Nat
evidenceCoordinateTag sourceIdentity = 1
evidenceCoordinateTag sameObject = 2
evidenceCoordinateTag authority = 3
evidenceCoordinateTag mechanism = 4
evidenceCoordinateTag quantification = 5
evidenceCoordinateTag probability = 6
evidenceCoordinateTag counterfactual = 7
evidenceCoordinateTag instrumentComparison = 8
evidenceCoordinateTag incidence = 9
evidenceCoordinateTag classification = 10

data RequirementNeed : Set where
  pnfFragment : Compiler.CompilerFragmentKind → RequirementNeed
  evidenceCoordinate : EvidenceCoordinateKind → RequirementNeed

requirementNeedClass : RequirementNeed → RequirementClass
requirementNeedClass (pnfFragment fragment) = pnfFragmentRequirement
requirementNeedClass (evidenceCoordinate coordinate) = evidenceCoordinateRequirement

requirementNeedValueTag : RequirementNeed → Nat
requirementNeedValueTag (pnfFragment fragment) = Compiler.compilerFragmentTag fragment
requirementNeedValueTag (evidenceCoordinate coordinate) = evidenceCoordinateTag coordinate

record ConsumerRequirementV2 : Set where
  constructor consumerRequirementV2
  field
    requirementReference : String
    need : RequirementNeed
    sourceScopeReference : String

open ConsumerRequirementV2 public

record ConsumerRequirementV2Parity : Set where
  constructor consumerRequirementV2Parity
  field
    productionWireVersionIsTwo : Bool
    legacyV1DecodeOnly : Bool
    pnfRequirementClassTagIsOne : Bool
    evidenceRequirementClassTagIsTwo : Bool
    evidenceTagsOneThroughTenExact : Bool
    fragmentRequirementMayBePaidByPNF : Bool
    evidenceRequirementMayBePaidByPNF : Bool
    unpaidFragmentUsesGAP1OBL1 : Bool
    unpaidEvidenceUsesGAP2OBL2 : Bool
    requirementScopeRetainedAcrossClasses : Bool
    evidenceRequirementCreatesClaimTruth : Bool
    evidenceRequirementCreatesSourceAuthority : Bool
    semanticPromotion : Bool

open ConsumerRequirementV2Parity public

canonicalConsumerRequirementV2Parity : ConsumerRequirementV2Parity
canonicalConsumerRequirementV2Parity =
  consumerRequirementV2Parity
    true true true true true true false true true true false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PNFDirectlyPaysEvidenceCoordinate : Set where
data EvidenceRequirementCreatesClaimTruth : Set where
data EvidenceRequirementCreatesSourceAuthority : Set where

pnfCannotDirectlyPayEvidenceCoordinate : PNFDirectlyPaysEvidenceCoordinate → ⊥
pnfCannotDirectlyPayEvidenceCoordinate ()

evidenceRequirementDoesNotCreateClaimTruth : EvidenceRequirementCreatesClaimTruth → ⊥
evidenceRequirementDoesNotCreateClaimTruth ()

evidenceRequirementDoesNotCreateSourceAuthority : EvidenceRequirementCreatesSourceAuthority → ⊥
evidenceRequirementDoesNotCreateSourceAuthority ()

------------------------------------------------------------------------
-- Concrete C029 consumer-coordinate fixture.  These are obligations, not
-- findings.  Their presence records what must be paid for consumer adequacy.
------------------------------------------------------------------------

record C029ConsumerCoordinateFixture : Set where
  constructor c029ConsumerCoordinateFixture
  field
    classifier : EvidenceCoordinateKind
    netIncidence : EvidenceCoordinateKind
    tradeMagnitude : EvidenceCoordinateKind
    consequenceMechanism : EvidenceCoordinateKind
    effectProbability : EvidenceCoordinateKind
    counterfactualCoordinate : EvidenceCoordinateKind
    instrumentComparator : EvidenceCoordinateKind

open C029ConsumerCoordinateFixture public

c029ConsumerCoordinates : C029ConsumerCoordinateFixture
c029ConsumerCoordinates =
  c029ConsumerCoordinateFixture
    classification incidence quantification mechanism probability counterfactual instrumentComparison
