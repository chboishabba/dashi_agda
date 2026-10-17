module DASHI.Reasoning.TrialecticT27PNF369RealizationASTExact where

------------------------------------------------------------------------
-- PNF/369 <-> graph-T27 SAME-OBJECT REALIZATION AST
--
-- This owner does NOT prove a same-object realization.  It turns the remaining
-- promotion frontier into one finite typed obligation language.
--
-- Existing paid facts:
--   * canonical PNF/369 source surface;
--   * independent exact 27-count receipts;
--   * one policy-completed T27 graph;
--   * exact projection of that graph to its free T18 data;
--   * source external-theorem promotion remains blocked.
--
-- Missing facts are no longer represented by an ambiguous Boolean.  Every
-- unproven invariant has a constructor below and the terminal realization type
-- requires a witness for every constructor.  In particular, 27 = 27 cannot
-- inhabit a coordinate map, an inverse, a C3 intertwiner, semantic agreement,
-- dynamics agreement, or empirical same-object attachment.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Interop.PNFHyperfabric369 as PNF369
import DASHI.Reasoning.TrialecticT9T18T27GraphExtensionExact as Tower
import DASHI.Reasoning.TrialecticT27C3CompletionPolicyExact as C3Policy
import DASHI.Reasoning.TrialecticT27Universal369HandoffExact as Handoff

------------------------------------------------------------------------
-- 1. Finite invariant language.
------------------------------------------------------------------------

data PNF369T27Invariant : Set where
  coordinateCarrierMap : PNF369T27Invariant
  coordinateCarrierInverse : PNF369T27Invariant
  coordinateRoundTripLeft : PNF369T27Invariant
  coordinateRoundTripRight : PNF369T27Invariant
  ternaryStructurePreserved : PNF369T27Invariant
  c3ActionIntertwined : PNF369T27Invariant
  completionGraphPreserved : PNF369T27Invariant
  t18ProjectionPreserved : PNF369T27Invariant
  pnfRoleSemanticsPreserved : PNF369T27Invariant
  documentTimeSemanticsPreserved : PNF369T27Invariant
  dynamicsEquivariance : PNF369T27Invariant
  actionHamiltonianAgreement : PNF369T27Invariant
  observableAgreement : PNF369T27Invariant
  empiricalSameObjectAttachment : PNF369T27Invariant

data InvariantStatus : Set where
  paid open forbidden : InvariantStatus

currentInvariantStatus : PNF369T27Invariant → InvariantStatus
currentInvariantStatus coordinateCarrierMap = open
currentInvariantStatus coordinateCarrierInverse = open
currentInvariantStatus coordinateRoundTripLeft = open
currentInvariantStatus coordinateRoundTripRight = open
currentInvariantStatus ternaryStructurePreserved = open
currentInvariantStatus c3ActionIntertwined = open
currentInvariantStatus completionGraphPreserved = open
currentInvariantStatus t18ProjectionPreserved = paid
currentInvariantStatus pnfRoleSemanticsPreserved = open
currentInvariantStatus documentTimeSemanticsPreserved = open
currentInvariantStatus dynamicsEquivariance = open
currentInvariantStatus actionHamiltonianAgreement = open
currentInvariantStatus observableAgreement = open
currentInvariantStatus empiricalSameObjectAttachment = open

------------------------------------------------------------------------
-- 2. Typed AST containing only already-owned structural facts.
------------------------------------------------------------------------

record PNF369T27RealizationAST
    (policy : Tower.T27CompletionPolicy) : Set₁ where
  constructor pnf369-t27-realization-ast
  field
    sourceSurface : PNF369.PNFHyperfabric369Surface
    sourceSurfaceIsCanonical :
      sourceSurface ≡ PNF369.canonicalPNFHyperfabric369Surface

    targetGraph : Tower.CompletedT27 policy
    targetAmbient : Tower.T27Coordinates
    targetAmbientIsCompletedGraph :
      targetAmbient ≡ Tower.completedCube targetGraph

    sourceAtomCountIsTwentySeven :
      PNF369.dialecticAtom sourceSurface ≡ 27
    targetAmbientCountIsTwentySeven :
      Tower.t27CoordinateCount ≡ 27

    targetProjectsToFreeT18 :
      Tower.projectT18 targetAmbient ≡ Tower.freeT18 targetGraph

    sourceExternalPromotionRemainsFalse :
      PNF369.externalTheoremPromotion
        sourceSurface
        PNF369.dialecticDiscussionAtom27
      ≡ false

    invariantStatus : PNF369T27Invariant → InvariantStatus
    invariantStatusIsCurrent :
      (invariant : PNF369T27Invariant) →
      invariantStatus invariant ≡ currentInvariantStatus invariant

open PNF369T27RealizationAST public

nativePolicy : Tower.T27CompletionPolicy
nativePolicy = C3Policy.nativeC3CompletionPolicy

canonicalHandoff : Handoff.Universal369T27Handoff nativePolicy
canonicalHandoff = Handoff.canonicalUniversal369T27Handoff nativePolicy

canonicalCandidateAST : PNF369T27RealizationAST nativePolicy
canonicalCandidateAST =
  pnf369-t27-realization-ast
    (Handoff.hyperfabricSurface canonicalHandoff)
    (Handoff.hyperfabricSurfaceIsCanonical canonicalHandoff)
    (Handoff.completedGraph canonicalHandoff)
    (Handoff.ambientGraph canonicalHandoff)
    (Handoff.ambientGraphIsCompletedCube canonicalHandoff)
    (Handoff.hyperfabricAtomCountIsTwentySeven canonicalHandoff)
    (Handoff.trialecticAmbientCountIsTwentySeven canonicalHandoff)
    (Handoff.completedGraphProjectsToFreeT18 canonicalHandoff)
    (Handoff.hyperfabricAtomExternalPromotionIsFalse canonicalHandoff)
    currentInvariantStatus
    (λ invariant → refl)

------------------------------------------------------------------------
-- 3. Concrete algebraic witness types.
--
-- The source-coordinate carrier itself is open.  A future owner must say what
-- the PNF atom coordinates actually are, map them into the mature T27 carrier,
-- and identify the canonical atom coordinate.  Merely knowing both sides have
-- count 27 cannot construct this record.
------------------------------------------------------------------------

record CoordinateCarrierMapWitness
    {policy : Tower.T27CompletionPolicy}
    (ast : PNF369T27RealizationAST policy) : Set₁ where
  constructor coordinate-carrier-map-witness
  field
    SourceCoordinate : Set
    sourceCanonicalAtomCoordinate : SourceCoordinate
    realizeCoordinate : SourceCoordinate → Tower.T27Coordinates
    realizesCanonicalTarget :
      realizeCoordinate sourceCanonicalAtomCoordinate ≡ targetAmbient ast

open CoordinateCarrierMapWitness public

record CoordinateCarrierInverseWitness
    {policy : Tower.T27CompletionPolicy}
    {ast : PNF369T27RealizationAST policy}
    (mapping : CoordinateCarrierMapWitness ast) : Set₁ where
  constructor coordinate-carrier-inverse-witness
  field
    inverseCoordinate : Tower.T27Coordinates → SourceCoordinate mapping
    leftRoundTrip :
      (source : SourceCoordinate mapping) →
      inverseCoordinate (realizeCoordinate mapping source) ≡ source
    rightRoundTrip :
      (target : Tower.T27Coordinates) →
      realizeCoordinate mapping (inverseCoordinate target) ≡ target

open CoordinateCarrierInverseWitness public

record C3IntertwinerWitness
    {policy : Tower.T27CompletionPolicy}
    {ast : PNF369T27RealizationAST policy}
    (mapping : CoordinateCarrierMapWitness ast) : Set₁ where
  constructor c3-intertwiner-witness
  field
    sourceC3 : SourceCoordinate mapping → SourceCoordinate mapping
    sourceC3OrderThree :
      (source : SourceCoordinate mapping) →
      sourceC3 (sourceC3 (sourceC3 source)) ≡ source
    targetC3 : Tower.T27Coordinates → Tower.T27Coordinates
    targetC3OrderThree :
      (target : Tower.T27Coordinates) →
      targetC3 (targetC3 (targetC3 target)) ≡ target
    intertwinesC3 :
      (source : SourceCoordinate mapping) →
      realizeCoordinate mapping (sourceC3 source)
      ≡ targetC3 (realizeCoordinate mapping source)

open C3IntertwinerWitness public

record CompletionGraphCompatibilityWitness
    {policy : Tower.T27CompletionPolicy}
    {ast : PNF369T27RealizationAST policy}
    (mapping : CoordinateCarrierMapWitness ast) : Set₁ where
  constructor completion-graph-compatibility-witness
  field
    sourceGraphCoordinate : SourceCoordinate mapping
    sourceGraphIsCanonicalAtom :
      sourceGraphCoordinate ≡ sourceCanonicalAtomCoordinate mapping
    realizedSourceSatisfiesGraph :
      Tower.GraphLaw policy (realizeCoordinate mapping sourceGraphCoordinate)

open CompletionGraphCompatibilityWitness public

------------------------------------------------------------------------
-- 4. Semantic / physical witness types intentionally have NO constructors.
--
-- These are not placeholders of type Top.  They are genuine open propositions.
-- A future owner must replace/bridge them with the relevant typed semantics or
-- dynamics before the terminal package can be inhabited.
------------------------------------------------------------------------

data TernaryStructurePreservationWitness
  {policy : Tower.T27CompletionPolicy}
  (ast : PNF369T27RealizationAST policy) : Set where

data PNFRoleSemanticCompatibilityWitness
  {policy : Tower.T27CompletionPolicy}
  (ast : PNF369T27RealizationAST policy) : Set where

data DocumentTimeSemanticCompatibilityWitness
  {policy : Tower.T27CompletionPolicy}
  (ast : PNF369T27RealizationAST policy) : Set where

data DynamicsEquivarianceWitness
  {policy : Tower.T27CompletionPolicy}
  (ast : PNF369T27RealizationAST policy) : Set where

data ActionHamiltonianAgreementWitness
  {policy : Tower.T27CompletionPolicy}
  (ast : PNF369T27RealizationAST policy) : Set where

data ObservableAgreementWitness
  {policy : Tower.T27CompletionPolicy}
  (ast : PNF369T27RealizationAST policy) : Set where

data EmpiricalSameObjectAttachmentWitness
  {policy : Tower.T27CompletionPolicy}
  (ast : PNF369T27RealizationAST policy) : Set where

------------------------------------------------------------------------
-- 5. Dependent meaning of every invariant constructor.
------------------------------------------------------------------------

InvariantMeaning :
  {policy : Tower.T27CompletionPolicy} →
  (ast : PNF369T27RealizationAST policy) →
  PNF369T27Invariant →
  Set₁
InvariantMeaning ast coordinateCarrierMap = CoordinateCarrierMapWitness ast
InvariantMeaning ast coordinateCarrierInverse =
  (mapping : CoordinateCarrierMapWitness ast) →
  CoordinateCarrierInverseWitness mapping
InvariantMeaning ast coordinateRoundTripLeft =
  (mapping : CoordinateCarrierMapWitness ast) →
  (inverse : CoordinateCarrierInverseWitness mapping) →
  (source : SourceCoordinate mapping) →
  inverseCoordinate inverse (realizeCoordinate mapping source) ≡ source
InvariantMeaning ast coordinateRoundTripRight =
  (mapping : CoordinateCarrierMapWitness ast) →
  (inverse : CoordinateCarrierInverseWitness mapping) →
  (target : Tower.T27Coordinates) →
  realizeCoordinate mapping (inverseCoordinate inverse target) ≡ target
InvariantMeaning ast ternaryStructurePreserved =
  TernaryStructurePreservationWitness ast
InvariantMeaning ast c3ActionIntertwined =
  (mapping : CoordinateCarrierMapWitness ast) → C3IntertwinerWitness mapping
InvariantMeaning ast completionGraphPreserved =
  (mapping : CoordinateCarrierMapWitness ast) →
  CompletionGraphCompatibilityWitness mapping
InvariantMeaning ast t18ProjectionPreserved =
  Tower.projectT18 (targetAmbient ast) ≡ Tower.freeT18 (targetGraph ast)
InvariantMeaning ast pnfRoleSemanticsPreserved =
  PNFRoleSemanticCompatibilityWitness ast
InvariantMeaning ast documentTimeSemanticsPreserved =
  DocumentTimeSemanticCompatibilityWitness ast
InvariantMeaning ast dynamicsEquivariance = DynamicsEquivarianceWitness ast
InvariantMeaning ast actionHamiltonianAgreement =
  ActionHamiltonianAgreementWitness ast
InvariantMeaning ast observableAgreement = ObservableAgreementWitness ast
InvariantMeaning ast empiricalSameObjectAttachment =
  EmpiricalSameObjectAttachmentWitness ast

------------------------------------------------------------------------
-- 6. Obligation AST nodes and the canonical current open ledger.
------------------------------------------------------------------------

data ObligationNode
    {policy : Tower.T27CompletionPolicy}
    (ast : PNF369T27RealizationAST policy)
    (invariant : PNF369T27Invariant) : Set₁ where
  paidNode : InvariantMeaning ast invariant → ObligationNode ast invariant
  openNode : ObligationNode ast invariant
  forbiddenNode :
    (InvariantMeaning ast invariant → ⊥) →
    ObligationNode ast invariant

record RealizationObligationLedger
    (policy : Tower.T27CompletionPolicy) : Set₁ where
  constructor realization-obligation-ledger
  field
    ast : PNF369T27RealizationAST policy
    node :
      (invariant : PNF369T27Invariant) →
      ObligationNode ast invariant

open RealizationObligationLedger public

canonicalOpenLedger : RealizationObligationLedger nativePolicy
canonicalOpenLedger =
  realization-obligation-ledger
    canonicalCandidateAST
    canonicalNode
  where
  canonicalNode :
    (invariant : PNF369T27Invariant) →
    ObligationNode canonicalCandidateAST invariant
  canonicalNode coordinateCarrierMap = openNode
  canonicalNode coordinateCarrierInverse = openNode
  canonicalNode coordinateRoundTripLeft = openNode
  canonicalNode coordinateRoundTripRight = openNode
  canonicalNode ternaryStructurePreserved = openNode
  canonicalNode c3ActionIntertwined = openNode
  canonicalNode completionGraphPreserved = openNode
  canonicalNode t18ProjectionPreserved =
    paidNode (targetProjectsToFreeT18 canonicalCandidateAST)
  canonicalNode pnfRoleSemanticsPreserved = openNode
  canonicalNode documentTimeSemanticsPreserved = openNode
  canonicalNode dynamicsEquivariance = openNode
  canonicalNode actionHamiltonianAgreement = openNode
  canonicalNode observableAgreement = openNode
  canonicalNode empiricalSameObjectAttachment = openNode

------------------------------------------------------------------------
-- 7. Terminal package.  This is the key OPEN lemma boundary.
--
-- The theorem that a fully-paid package implies a same-object realization is
-- trivial packaging.  The mathematically open statement is existence of the
-- fully-paid package for the canonical candidate AST.
------------------------------------------------------------------------

record AllRealizationObligationsPaid
    {policy : Tower.T27CompletionPolicy}
    (ast : PNF369T27RealizationAST policy) : Set₁ where
  constructor all-realization-obligations-paid
  field
    coordinateMapPaid : InvariantMeaning ast coordinateCarrierMap
    coordinateInversePaid : InvariantMeaning ast coordinateCarrierInverse
    coordinateLeftRoundTripPaid : InvariantMeaning ast coordinateRoundTripLeft
    coordinateRightRoundTripPaid : InvariantMeaning ast coordinateRoundTripRight
    ternaryStructurePaid : InvariantMeaning ast ternaryStructurePreserved
    c3IntertwinerPaid : InvariantMeaning ast c3ActionIntertwined
    completionGraphPaid : InvariantMeaning ast completionGraphPreserved
    t18ProjectionPaid : InvariantMeaning ast t18ProjectionPreserved
    pnfRoleSemanticsPaid : InvariantMeaning ast pnfRoleSemanticsPreserved
    documentTimeSemanticsPaid : InvariantMeaning ast documentTimeSemanticsPreserved
    dynamicsEquivariancePaid : InvariantMeaning ast dynamicsEquivariance
    actionHamiltonianAgreementPaid : InvariantMeaning ast actionHamiltonianAgreement
    observableAgreementPaid : InvariantMeaning ast observableAgreement
    empiricalSameObjectAttachmentPaid :
      InvariantMeaning ast empiricalSameObjectAttachment

open AllRealizationObligationsPaid public

record PNF369T27SameObjectRealization
    {policy : Tower.T27CompletionPolicy}
    (ast : PNF369T27RealizationAST policy) : Set₁ where
  constructor pnf369-t27-same-object-realization
  field
    obligations : AllRealizationObligationsPaid ast

sameObjectRealizationFromAllObligations :
  {policy : Tower.T27CompletionPolicy} →
  (ast : PNF369T27RealizationAST policy) →
  AllRealizationObligationsPaid ast →
  PNF369T27SameObjectRealization ast
sameObjectRealizationFromAllObligations ast paidPackage =
  pnf369-t27-same-object-realization paidPackage

-- KEY OPEN LEMMA: no inhabitant is supplied in this module.
PNF369T27SameObjectRealizationOpenLemma : Set₁
PNF369T27SameObjectRealizationOpenLemma =
  AllRealizationObligationsPaid canonicalCandidateAST

------------------------------------------------------------------------
-- 8. Promotion boundary.
------------------------------------------------------------------------

record PNF369T27RealizationASTBoundary : Set where
  constructor pnf369-t27-realization-ast-boundary
  field
    finiteInvariantSetEnumerated : Bool
    sameObjectRealizationExistenceLemmaStated : Bool
    exactTypedASTConstructed : Bool
    canonicalOpenLedgerConstructed : Bool
    t18ProjectionInvariantPaid : Bool
    coordinateRoundTripsPaid : Bool
    c3IntertwinerPaid : Bool
    semanticCompatibilityPaid : Bool
    physicalDynamicsCompatibilityPaid : Bool
    empiricalSameObjectAttachmentPaid : Bool
    terminalSameObjectRealizationClaimed : Bool

open PNF369T27RealizationASTBoundary public

canonicalPNF369T27RealizationASTBoundary : PNF369T27RealizationASTBoundary
canonicalPNF369T27RealizationASTBoundary =
  pnf369-t27-realization-ast-boundary
    true true true true true false false false false false false
