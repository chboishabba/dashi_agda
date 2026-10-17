module DASHI.Reasoning.TrialecticT27PNF369RealizationASTExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Interop.PNFHyperfabric369 as PNF369
import DASHI.Reasoning.TrialecticT9T18T27GraphExtensionExact as Tower
import DASHI.Reasoning.TrialecticT27C3CompletionPolicyExact as C3Policy
import DASHI.Reasoning.TrialecticT27Universal369HandoffExact as Handoff

data PNF369T27Invariant : Set where
  coordinateCarrierMap coordinateCarrierInverse : PNF369T27Invariant
  coordinateRoundTripLeft coordinateRoundTripRight : PNF369T27Invariant
  ternaryStructurePreserved c3ActionIntertwined : PNF369T27Invariant
  completionGraphPreserved t18ProjectionPreserved : PNF369T27Invariant
  pnfRoleSemanticsPreserved documentTimeSemanticsPreserved : PNF369T27Invariant
  dynamicsEquivariance actionHamiltonianAgreement : PNF369T27Invariant
  observableAgreement empiricalSameObjectAttachment : PNF369T27Invariant

data InvariantStatus : Set where paid open forbidden : InvariantStatus

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

record PNF369T27RealizationAST (policy : Tower.T27CompletionPolicy) : Set₁ where
  constructor pnf369-t27-realization-ast
  field
    sourceSurface : PNF369.PNFHyperfabric369Surface
    sourceSurfaceIsCanonical : sourceSurface ≡ PNF369.canonicalPNFHyperfabric369Surface
    targetGraph : Tower.CompletedT27 policy
    targetAmbient : Tower.T27Coordinates
    targetAmbientIsCompletedGraph : targetAmbient ≡ Tower.completedCube targetGraph
    sourceAtomCountIsTwentySeven : PNF369.dialecticAtom sourceSurface ≡ 27
    targetAmbientCountIsTwentySeven : Tower.t27CoordinateCount ≡ 27
    targetProjectsToFreeT18 : Tower.projectT18 targetAmbient ≡ Tower.freeT18 targetGraph
    sourceExternalPromotionRemainsFalse :
      PNF369.externalTheoremPromotion sourceSurface PNF369.dialecticDiscussionAtom27 ≡ false
    invariantStatus : PNF369T27Invariant → InvariantStatus
    invariantStatusIsCurrent :
      (invariant : PNF369T27Invariant) → invariantStatus invariant ≡ currentInvariantStatus invariant
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

record CoordinateCarrierMapWitness {policy : Tower.T27CompletionPolicy}
    (ast : PNF369T27RealizationAST policy) : Set₁ where
  constructor coordinate-carrier-map-witness
  field
    SourceCoordinate : Set
    sourceCanonicalAtomCoordinate : SourceCoordinate
    realizeCoordinate : SourceCoordinate → Tower.T27Coordinates
    realizesCanonicalTarget : realizeCoordinate sourceCanonicalAtomCoordinate ≡ targetAmbient ast
open CoordinateCarrierMapWitness public

record CoordinateCarrierInverseWitness {policy : Tower.T27CompletionPolicy}
    {ast : PNF369T27RealizationAST policy}
    (mapping : CoordinateCarrierMapWitness ast) : Set₁ where
  constructor coordinate-carrier-inverse-witness
  field
    inverseCoordinate : Tower.T27Coordinates → SourceCoordinate mapping
    leftRoundTrip : (source : SourceCoordinate mapping) → inverseCoordinate (realizeCoordinate mapping source) ≡ source
    rightRoundTrip : (target : Tower.T27Coordinates) → realizeCoordinate mapping (inverseCoordinate target) ≡ target
open CoordinateCarrierInverseWitness public

record LeftRoundTripWitness {policy : Tower.T27CompletionPolicy}
    {ast : PNF369T27RealizationAST policy}
    (mapping : CoordinateCarrierMapWitness ast)
    (inverse : CoordinateCarrierInverseWitness mapping) : Set₁ where
  constructor left-round-trip-witness
  field leftRoundTripHolds :
    (source : SourceCoordinate mapping) → inverseCoordinate inverse (realizeCoordinate mapping source) ≡ source

record RightRoundTripWitness {policy : Tower.T27CompletionPolicy}
    {ast : PNF369T27RealizationAST policy}
    (mapping : CoordinateCarrierMapWitness ast)
    (inverse : CoordinateCarrierInverseWitness mapping) : Set₁ where
  constructor right-round-trip-witness
  field rightRoundTripHolds :
    (target : Tower.T27Coordinates) → realizeCoordinate mapping (inverseCoordinate inverse target) ≡ target

record C3IntertwinerWitness {policy : Tower.T27CompletionPolicy}
    {ast : PNF369T27RealizationAST policy}
    (mapping : CoordinateCarrierMapWitness ast) : Set₁ where
  constructor c3-intertwiner-witness
  field
    sourceC3 : SourceCoordinate mapping → SourceCoordinate mapping
    sourceC3OrderThree : (source : SourceCoordinate mapping) → sourceC3 (sourceC3 (sourceC3 source)) ≡ source
    targetC3 : Tower.T27Coordinates → Tower.T27Coordinates
    targetC3OrderThree : (target : Tower.T27Coordinates) → targetC3 (targetC3 (targetC3 target)) ≡ target
    intertwinesC3 : (source : SourceCoordinate mapping) →
      realizeCoordinate mapping (sourceC3 source) ≡ targetC3 (realizeCoordinate mapping source)
open C3IntertwinerWitness public

record CompletionGraphCompatibilityWitness {policy : Tower.T27CompletionPolicy}
    {ast : PNF369T27RealizationAST policy}
    (mapping : CoordinateCarrierMapWitness ast) : Set₁ where
  constructor completion-graph-compatibility-witness
  field
    sourceGraphCoordinate : SourceCoordinate mapping
    sourceGraphIsCanonicalAtom : sourceGraphCoordinate ≡ sourceCanonicalAtomCoordinate mapping
    realizedSourceSatisfiesGraph : Tower.GraphLaw policy (realizeCoordinate mapping sourceGraphCoordinate)

record T18ProjectionPreservationWitness {policy : Tower.T27CompletionPolicy}
    (ast : PNF369T27RealizationAST policy) : Set₁ where
  constructor t18-projection-preservation-witness
  field projectionPreserved : Tower.projectT18 (targetAmbient ast) ≡ Tower.freeT18 (targetGraph ast)

data TernaryStructurePreservationWitness {policy : Tower.T27CompletionPolicy}
  (ast : PNF369T27RealizationAST policy) : Set₁ where

data PNFRoleSemanticCompatibilityWitness {policy : Tower.T27CompletionPolicy}
  (ast : PNF369T27RealizationAST policy) : Set₁ where

data DocumentTimeSemanticCompatibilityWitness {policy : Tower.T27CompletionPolicy}
  (ast : PNF369T27RealizationAST policy) : Set₁ where

data DynamicsEquivarianceWitness {policy : Tower.T27CompletionPolicy}
  (ast : PNF369T27RealizationAST policy) : Set₁ where

data ActionHamiltonianAgreementWitness {policy : Tower.T27CompletionPolicy}
  (ast : PNF369T27RealizationAST policy) : Set₁ where

data ObservableAgreementWitness {policy : Tower.T27CompletionPolicy}
  (ast : PNF369T27RealizationAST policy) : Set₁ where

data EmpiricalSameObjectAttachmentWitness {policy : Tower.T27CompletionPolicy}
  (ast : PNF369T27RealizationAST policy) : Set₁ where

InvariantMeaning : {policy : Tower.T27CompletionPolicy} →
  (ast : PNF369T27RealizationAST policy) → PNF369T27Invariant → Set₁
InvariantMeaning ast coordinateCarrierMap = CoordinateCarrierMapWitness ast
InvariantMeaning ast coordinateCarrierInverse =
  (mapping : CoordinateCarrierMapWitness ast) → CoordinateCarrierInverseWitness mapping
InvariantMeaning ast coordinateRoundTripLeft =
  (mapping : CoordinateCarrierMapWitness ast) →
  (inverse : CoordinateCarrierInverseWitness mapping) → LeftRoundTripWitness mapping inverse
InvariantMeaning ast coordinateRoundTripRight =
  (mapping : CoordinateCarrierMapWitness ast) →
  (inverse : CoordinateCarrierInverseWitness mapping) → RightRoundTripWitness mapping inverse
InvariantMeaning ast ternaryStructurePreserved = TernaryStructurePreservationWitness ast
InvariantMeaning ast c3ActionIntertwined =
  (mapping : CoordinateCarrierMapWitness ast) → C3IntertwinerWitness mapping
InvariantMeaning ast completionGraphPreserved =
  (mapping : CoordinateCarrierMapWitness ast) → CompletionGraphCompatibilityWitness mapping
InvariantMeaning ast t18ProjectionPreserved = T18ProjectionPreservationWitness ast
InvariantMeaning ast pnfRoleSemanticsPreserved = PNFRoleSemanticCompatibilityWitness ast
InvariantMeaning ast documentTimeSemanticsPreserved = DocumentTimeSemanticCompatibilityWitness ast
InvariantMeaning ast dynamicsEquivariance = DynamicsEquivarianceWitness ast
InvariantMeaning ast actionHamiltonianAgreement = ActionHamiltonianAgreementWitness ast
InvariantMeaning ast observableAgreement = ObservableAgreementWitness ast
InvariantMeaning ast empiricalSameObjectAttachment = EmpiricalSameObjectAttachmentWitness ast

data ObligationNode {policy : Tower.T27CompletionPolicy}
    (ast : PNF369T27RealizationAST policy)
    (invariant : PNF369T27Invariant) : Set₁ where
  paidNode : InvariantMeaning ast invariant → ObligationNode ast invariant
  openNode : ObligationNode ast invariant
  forbiddenNode : (InvariantMeaning ast invariant → ⊥) → ObligationNode ast invariant

record RealizationObligationLedger (policy : Tower.T27CompletionPolicy) : Set₁ where
  constructor realization-obligation-ledger
  field
    ast : PNF369T27RealizationAST policy
    node : (invariant : PNF369T27Invariant) → ObligationNode ast invariant
open RealizationObligationLedger public

canonicalOpenLedger : RealizationObligationLedger nativePolicy
canonicalOpenLedger = realization-obligation-ledger canonicalCandidateAST canonicalNode
  where
  canonicalNode : (invariant : PNF369T27Invariant) → ObligationNode canonicalCandidateAST invariant
  canonicalNode coordinateCarrierMap = openNode
  canonicalNode coordinateCarrierInverse = openNode
  canonicalNode coordinateRoundTripLeft = openNode
  canonicalNode coordinateRoundTripRight = openNode
  canonicalNode ternaryStructurePreserved = openNode
  canonicalNode c3ActionIntertwined = openNode
  canonicalNode completionGraphPreserved = openNode
  canonicalNode t18ProjectionPreserved =
    paidNode (t18-projection-preservation-witness (targetProjectsToFreeT18 canonicalCandidateAST))
  canonicalNode pnfRoleSemanticsPreserved = openNode
  canonicalNode documentTimeSemanticsPreserved = openNode
  canonicalNode dynamicsEquivariance = openNode
  canonicalNode actionHamiltonianAgreement = openNode
  canonicalNode observableAgreement = openNode
  canonicalNode empiricalSameObjectAttachment = openNode

record AllRealizationObligationsPaid {policy : Tower.T27CompletionPolicy}
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
    empiricalSameObjectAttachmentPaid : InvariantMeaning ast empiricalSameObjectAttachment
open AllRealizationObligationsPaid public

record PNF369T27SameObjectRealization {policy : Tower.T27CompletionPolicy}
    (ast : PNF369T27RealizationAST policy) : Set₁ where
  constructor pnf369-t27-same-object-realization
  field obligations : AllRealizationObligationsPaid ast

sameObjectRealizationFromAllObligations : {policy : Tower.T27CompletionPolicy} →
  (ast : PNF369T27RealizationAST policy) →
  AllRealizationObligationsPaid ast → PNF369T27SameObjectRealization ast
sameObjectRealizationFromAllObligations ast paidPackage =
  pnf369-t27-same-object-realization paidPackage

-- KEY OPEN LEMMA: no inhabitant is supplied here.
PNF369T27SameObjectRealizationOpenLemma : Set₁
PNF369T27SameObjectRealizationOpenLemma = AllRealizationObligationsPaid canonicalCandidateAST

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
  pnf369-t27-realization-ast-boundary true true true true true false false false false false false
