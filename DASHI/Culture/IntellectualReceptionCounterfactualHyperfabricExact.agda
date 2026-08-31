module DASHI.Culture.IntellectualReceptionCounterfactualHyperfabricExact where

------------------------------------------------------------------------
-- INTELLECTUAL RECEPTION / COUNTERFACTUAL HYPERFABRIC
--
-- Counterfactuals here are typed interventions on a path-qualified reception
-- state.  They are not asserted histories and they are not physical branches.
--
-- The owner composes:
--   arrival-history coordinate
--   selection-topology coordinate
--   admission-gate coordinate
--   relation/standing coordinate
--   admissible-transition receipt
--   coarse/fine future projections.
--
-- PR #666 remains inspiration only while open.  No Base369/Monster owner is
-- imported here; the finite order/nonfactorability theorems are DASHI-owned.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Unit using (⊤; tt)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AdmissibleTransitionHyperfabricExact as Admissible
import DASHI.Core.CubieFaceOrderHolonomyAnalogueExact as Holonomy
import DASHI.Culture.IntellectualReceptionAdmissibilityStratumWhatIfExact as Stratum

------------------------------------------------------------------------
-- 1. Fine counterfactual carrier.
------------------------------------------------------------------------

data RelationMode : Set where
  detachedCommentary
  institutionalAuthority
  movementSolidarity
  archivalRecoveryRelation
  : RelationMode

record CounterfactualReceptionState : Set where
  constructor counterfactual-reception-state
  field
    stratum : Stratum.ReceptionAdmissibilityStratum
    relation : RelationMode

open CounterfactualReceptionState public

seedState : CounterfactualReceptionState
seedState =
  counterfactual-reception-state
    Stratum.commentaryCanonStratum
    detachedCommentary

------------------------------------------------------------------------
-- 2. Coordinate interventions.
------------------------------------------------------------------------

data CounterfactualIntervention : Set where
  pluraliseTopology
  shiftToMovementHistory
  closeAdmissionGate
  recoverSourceHistory
  shiftRelationToInstitution
  : CounterfactualIntervention

applyIntervention :
  CounterfactualIntervention →
  CounterfactualReceptionState →
  CounterfactualReceptionState
applyIntervention pluraliseTopology state =
  counterfactual-reception-state
    (Stratum.applyWhatIf Stratum.whatIfPluralTopology (stratum state))
    (relation state)
applyIntervention shiftToMovementHistory state =
  counterfactual-reception-state
    (Stratum.applyWhatIf Stratum.whatIfMovementReception (stratum state))
    movementSolidarity
applyIntervention closeAdmissionGate state =
  counterfactual-reception-state
    (Stratum.applyWhatIf Stratum.whatIfCanonClosed (stratum state))
    (relation state)
applyIntervention recoverSourceHistory state =
  counterfactual-reception-state
    (Stratum.applyWhatIf Stratum.whatIfSourceRecovered (stratum state))
    archivalRecoveryRelation
applyIntervention shiftRelationToInstitution state =
  counterfactual-reception-state
    (stratum state)
    institutionalAuthority

applyTwo :
  CounterfactualIntervention →
  CounterfactualIntervention →
  CounterfactualReceptionState →
  CounterfactualReceptionState
applyTwo first second state =
  applyIntervention second (applyIntervention first state)

------------------------------------------------------------------------
-- 3. A literal counterfactual order defect.
--
-- pluraliseTopology opens the plural continuation; closeAdmissionGate then
-- closes the gate while keeping a canon-like coarse cone.  Reversing the order
-- reopens through pluralisation.  The endpoint gate therefore remembers order.
------------------------------------------------------------------------

pluralThenClose : CounterfactualReceptionState
pluralThenClose =
  applyTwo pluraliseTopology closeAdmissionGate seedState

closeThenPlural : CounterfactualReceptionState
closeThenPlural =
  applyTwo closeAdmissionGate pluraliseTopology seedState

pluralThenCloseGate : Stratum.AdmissionGate
pluralThenCloseGate = Stratum.gate (stratum pluralThenClose)

closeThenPluralGate : Stratum.AdmissionGate
closeThenPluralGate = Stratum.gate (stratum closeThenPlural)

counterfactualOrderChangesGate :
  pluralThenCloseGate ≡ closeThenPluralGate → ⊥
counterfactualOrderChangesGate ()

------------------------------------------------------------------------
-- 4. Coarse future can erase the order defect.
--
-- The coarse observer records only that both paths remain inside the same
-- present-vocabulary family.  The fine endpoint records the intervention order.
------------------------------------------------------------------------

data CounterfactualOrder : Set where
  pluralThenCloseOrder closeThenPluralOrder : CounterfactualOrder

data CoarseFutureSurface : Set where
  samePresentVocabularyFuture : CoarseFutureSurface

data FineCounterfactualEndpoint : Set where
  pluralThenCloseEndpoint closeThenPluralEndpoint : FineCounterfactualEndpoint

coarseFutureSurface : CounterfactualOrder → CoarseFutureSurface
coarseFutureSurface _ = samePresentVocabularyFuture

fineCounterfactualEndpoint : CounterfactualOrder → FineCounterfactualEndpoint
fineCounterfactualEndpoint pluralThenCloseOrder = pluralThenCloseEndpoint
fineCounterfactualEndpoint closeThenPluralOrder = closeThenPluralEndpoint

fineCounterfactualEndpointsDiffer :
  fineCounterfactualEndpoint pluralThenCloseOrder
  ≡ fineCounterfactualEndpoint closeThenPluralOrder → ⊥
fineCounterfactualEndpointsDiffer ()

coarseFutureCannotRecoverCounterfactualOrder :
  INF.FactorsThrough coarseFutureSurface fineCounterfactualEndpoint → ⊥
coarseFutureCannotRecoverCounterfactualOrder =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      pluralThenCloseOrder closeThenPluralOrder refl
      fineCounterfactualEndpointsDiffer)

------------------------------------------------------------------------
-- 5. Relation is an independent hidden axis.
------------------------------------------------------------------------

data SameStratumRelationState : Set where
  detachedAtCanon institutionalAtCanon : SameStratumRelationState

data SameStratumCode : Set where sameCanonStratum : SameStratumCode

data RelationEndpointCode : Set where detachedEndpoint institutionalEndpoint : RelationEndpointCode

sameStratumProjection : SameStratumRelationState → SameStratumCode
sameStratumProjection _ = sameCanonStratum

relationEndpoint : SameStratumRelationState → RelationEndpointCode
relationEndpoint detachedAtCanon = detachedEndpoint
relationEndpoint institutionalAtCanon = institutionalEndpoint

sameStratumCannotRecoverRelationMode :
  INF.FactorsThrough sameStratumProjection relationEndpoint → ⊥
sameStratumCannotRecoverRelationMode =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      detachedAtCanon institutionalAtCanon refl (λ ()))

------------------------------------------------------------------------
-- 6. Proof-relevant counterfactual admissibility.
------------------------------------------------------------------------

data CounterfactualParameter : Set where ordinaryCounterfactual : CounterfactualParameter

interventionEnabled :
  CounterfactualIntervention →
  CounterfactualParameter →
  CounterfactualReceptionState →
  Set
interventionEnabled pluraliseTopology ordinaryCounterfactual state with Stratum.gate (stratum state)
... | Stratum.openGate = ⊤
... | Stratum.pendingGate = ⊥
... | Stratum.closedGate = ⊥
interventionEnabled shiftToMovementHistory ordinaryCounterfactual state with Stratum.gate (stratum state)
... | Stratum.openGate = ⊤
... | Stratum.pendingGate = ⊥
... | Stratum.closedGate = ⊥
interventionEnabled closeAdmissionGate ordinaryCounterfactual state with Stratum.gate (stratum state)
... | Stratum.openGate = ⊤
... | Stratum.pendingGate = ⊤
... | Stratum.closedGate = ⊥
interventionEnabled recoverSourceHistory ordinaryCounterfactual state with Stratum.gate (stratum state)
... | Stratum.openGate = ⊤
... | Stratum.pendingGate = ⊤
... | Stratum.closedGate = ⊤
interventionEnabled shiftRelationToInstitution ordinaryCounterfactual state = ⊤

counterfactualTransitionSystem : Admissible.AdmissibleTransitionSystem
counterfactualTransitionSystem =
  Admissible.admissibleTransitionSystem
    CounterfactualReceptionState
    CounterfactualParameter
    CounterfactualIntervention
    interventionEnabled
    (λ move parameter state → applyIntervention move state)
    (λ _ → ⊤)
    (λ move parameter state enabledHere invariantHere → tt)
    "Finite path-qualified intellectual-reception counterfactual hyperfabric."

pluralisationAdmittedAtSeed :
  Admissible.AdmittedStep
    counterfactualTransitionSystem
    pluraliseTopology ordinaryCounterfactual seedState
pluralisationAdmittedAtSeed = Admissible.admittedStep tt tt

closedSeed : CounterfactualReceptionState
closedSeed = applyIntervention closeAdmissionGate seedState

pluralisationBlockedAfterClosure :
  Admissible.Enabled
    counterfactualTransitionSystem
    pluraliseTopology ordinaryCounterfactual closedSeed → ⊥
pluralisationBlockedAfterClosure impossible = impossible

sourceRecoveryStillAdmittedAfterClosure :
  Admissible.AdmittedStep
    counterfactualTransitionSystem
    recoverSourceHistory ordinaryCounterfactual closedSeed
sourceRecoveryStillAdmittedAfterClosure = Admissible.admittedStep tt tt

------------------------------------------------------------------------
-- 7. Alternative continuation composition is not historical assertion.
------------------------------------------------------------------------

data CounterfactualCompositionPromotesActualHistory : Set where
data OrderDefectPromotesNecessaryDialectic : Set where
data CoarseFuturePromotesUniqueFinePath : Set where
data ReceptionInterventionPromotesPhysicalBranch : Set where
data CounterfactualHolonomyPromotesGaugeCurvature : Set where

aCounterfactualCompositionIsNotActualHistory :
  CounterfactualCompositionPromotesActualHistory → ⊥
aCounterfactualCompositionIsNotActualHistory ()

orderDefectDoesNotPromoteNecessaryDialectic :
  OrderDefectPromotesNecessaryDialectic → ⊥
orderDefectDoesNotPromoteNecessaryDialectic ()

coarseFutureDoesNotPromoteUniqueFinePath :
  CoarseFuturePromotesUniqueFinePath → ⊥
coarseFutureDoesNotPromoteUniqueFinePath ()

receptionInterventionDoesNotPromotePhysicalBranch :
  ReceptionInterventionPromotesPhysicalBranch → ⊥
receptionInterventionDoesNotPromotePhysicalBranch ()

counterfactualHolonomyDoesNotPromoteGaugeCurvature :
  CounterfactualHolonomyPromotesGaugeCurvature → ⊥
counterfactualHolonomyDoesNotPromoteGaugeCurvature ()

holonomyPrecedentStillKeepsGaugeBoundary :
  Holonomy.CubieHolonomyBoundary.literalGaugeConnectionConstructed
    Holonomy.canonicalCubieHolonomyBoundary
  ≡ false
holonomyPrecedentStillKeepsGaugeBoundary = refl

------------------------------------------------------------------------
-- 8. Canonical boundary.
------------------------------------------------------------------------

record IntellectualReceptionCounterfactualHyperfabricBoundary : Set where
  constructor intellectual-reception-counterfactual-hyperfabric-boundary
  field
    interventionsAlwaysCommute : Bool
    coarseFutureDeterminesInterventionOrder : Bool
    stratumDeterminesRelationMode : Bool
    disabledInterventionIsLowProbabilityIntervention : Bool
    counterfactualCompositionIsActualHistory : Bool
    counterfactualBranchIsPhysicalBranch : Bool
    orderDefectIsGaugeCurvature : Bool
    interventionsCanAlterAdmissibleFuture : Bool
    compositionOrderCanMatter : Bool
    sourceAttributionBoundarySurvivesCounterfactuals : Bool

canonicalIntellectualReceptionCounterfactualHyperfabricBoundary :
  IntellectualReceptionCounterfactualHyperfabricBoundary
canonicalIntellectualReceptionCounterfactualHyperfabricBoundary =
  intellectual-reception-counterfactual-hyperfabric-boundary
    false false false false false false false true true true
