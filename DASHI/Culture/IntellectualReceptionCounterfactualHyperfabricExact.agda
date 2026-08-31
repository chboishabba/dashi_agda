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
-- 3. Raw operator order can matter even when the reverse path is not admitted.
--
-- This section is intentionally algebraic only.  Section 7 below gives the
-- stronger witness where both intervention orders are proof-relevantly admitted.
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

rawCounterfactualOrderChangesGate :
  pluralThenCloseGate ≡ closeThenPluralGate → ⊥
rawCounterfactualOrderChangesGate ()

------------------------------------------------------------------------
-- 4. A coarse present-vocabulary surface erases the raw order defect.
------------------------------------------------------------------------

data CounterfactualOrder : Set where
  pluralThenCloseOrder closeThenPluralOrder : CounterfactualOrder

data CoarseCounterfactualSurface : Set where
  samePresentVocabularySurface : CoarseCounterfactualSurface

data FineCounterfactualEndpoint : Set where
  pluralThenCloseEndpoint closeThenPluralEndpoint : FineCounterfactualEndpoint

coarseCounterfactualSurface : CounterfactualOrder → CoarseCounterfactualSurface
coarseCounterfactualSurface _ = samePresentVocabularySurface

fineCounterfactualEndpoint : CounterfactualOrder → FineCounterfactualEndpoint
fineCounterfactualEndpoint pluralThenCloseOrder = pluralThenCloseEndpoint
fineCounterfactualEndpoint closeThenPluralOrder = closeThenPluralEndpoint

fineCounterfactualEndpointsDiffer :
  fineCounterfactualEndpoint pluralThenCloseOrder
  ≡ fineCounterfactualEndpoint closeThenPluralOrder → ⊥
fineCounterfactualEndpointsDiffer ()

coarseSurfaceCannotRecoverCounterfactualOrder :
  INF.FactorsThrough coarseCounterfactualSurface fineCounterfactualEndpoint → ⊥
coarseSurfaceCannotRecoverCounterfactualOrder =
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
-- 7. Stronger admitted order defect inside one exact future-cone fibre.
--
-- M = shift to movement reception: sets the movement future cone and relation.
-- R = shift relation to institution: changes only the relation coordinate.
--
-- Both M;R and R;M are fully admitted from the seed.  They land in the exact
-- same encoded future cone, but their final relation modes differ because M
-- rewrites relation to movementSolidarity whereas R rewrites it to
-- institutionalAuthority.
------------------------------------------------------------------------

movementIntermediate : CounterfactualReceptionState
movementIntermediate = applyIntervention shiftToMovementHistory seedState

institutionIntermediate : CounterfactualReceptionState
institutionIntermediate = applyIntervention shiftRelationToInstitution seedState

movementThenInstitution : CounterfactualReceptionState
movementThenInstitution =
  applyIntervention shiftRelationToInstitution movementIntermediate

institutionThenMovement : CounterfactualReceptionState
institutionThenMovement =
  applyIntervention shiftToMovementHistory institutionIntermediate

movementFirstAdmitted :
  Admissible.AdmittedStep
    counterfactualTransitionSystem
    shiftToMovementHistory ordinaryCounterfactual seedState
movementFirstAdmitted = Admissible.admittedStep tt tt

institutionAfterMovementAdmitted :
  Admissible.AdmittedStep
    counterfactualTransitionSystem
    shiftRelationToInstitution ordinaryCounterfactual movementIntermediate
institutionAfterMovementAdmitted = Admissible.admittedStep tt tt

institutionFirstAdmitted :
  Admissible.AdmittedStep
    counterfactualTransitionSystem
    shiftRelationToInstitution ordinaryCounterfactual seedState
institutionFirstAdmitted = Admissible.admittedStep tt tt

movementAfterInstitutionAdmitted :
  Admissible.AdmittedStep
    counterfactualTransitionSystem
    shiftToMovementHistory ordinaryCounterfactual institutionIntermediate
movementAfterInstitutionAdmitted = Admissible.admittedStep tt tt

admittedOrderRelationsDiffer :
  relation movementThenInstitution ≡ relation institutionThenMovement → ⊥
admittedOrderRelationsDiffer ()

admittedOrdersShareExactFutureCone :
  Stratum.futureCone (stratum movementThenInstitution)
  ≡ Stratum.futureCone (stratum institutionThenMovement)
admittedOrdersShareExactFutureCone = refl

data AdmittedCounterfactualOrder : Set where
  movementThenInstitutionOrder
  institutionThenMovementOrder
  : AdmittedCounterfactualOrder

data AdmittedFineEndpoint : Set where
  movementThenInstitutionEndpoint
  institutionThenMovementEndpoint
  : AdmittedFineEndpoint

admittedFutureCone : AdmittedCounterfactualOrder → Stratum.FutureConeCode
admittedFutureCone movementThenInstitutionOrder =
  Stratum.futureCone (stratum movementThenInstitution)
admittedFutureCone institutionThenMovementOrder =
  Stratum.futureCone (stratum institutionThenMovement)

admittedFineEndpoint : AdmittedCounterfactualOrder → AdmittedFineEndpoint
admittedFineEndpoint movementThenInstitutionOrder = movementThenInstitutionEndpoint
admittedFineEndpoint institutionThenMovementOrder = institutionThenMovementEndpoint

admittedFineEndpointsDiffer :
  admittedFineEndpoint movementThenInstitutionOrder
  ≡ admittedFineEndpoint institutionThenMovementOrder → ⊥
admittedFineEndpointsDiffer ()

exactFutureConeCannotRecoverAdmittedTransportOrder :
  INF.FactorsThrough admittedFutureCone admittedFineEndpoint → ⊥
exactFutureConeCannotRecoverAdmittedTransportOrder =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      movementThenInstitutionOrder
      institutionThenMovementOrder
      admittedOrdersShareExactFutureCone
      admittedFineEndpointsDiffer)

------------------------------------------------------------------------
-- 8. Alternative continuation composition is not historical assertion.
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
-- 9. Canonical boundary.
------------------------------------------------------------------------

record IntellectualReceptionCounterfactualHyperfabricBoundary : Set where
  constructor intellectual-reception-counterfactual-hyperfabric-boundary
  field
    interventionsAlwaysCommute : Bool
    exactFutureConeDeterminesAdmittedInterventionOrder : Bool
    stratumDeterminesRelationMode : Bool
    disabledInterventionIsLowProbabilityIntervention : Bool
    rawOperatorOrderEqualsAdmittedPathOrder : Bool
    counterfactualCompositionIsActualHistory : Bool
    counterfactualBranchIsPhysicalBranch : Bool
    orderDefectIsGaugeCurvature : Bool
    interventionsCanAlterAdmissibleFuture : Bool
    admittedCompositionOrderCanMatter : Bool
    sourceAttributionBoundarySurvivesCounterfactuals : Bool

canonicalIntellectualReceptionCounterfactualHyperfabricBoundary :
  IntellectualReceptionCounterfactualHyperfabricBoundary
canonicalIntellectualReceptionCounterfactualHyperfabricBoundary =
  intellectual-reception-counterfactual-hyperfabric-boundary
    false false false false false false false false true true true
