module DASHI.Reasoning.LilaMonsterGeometricReasoningCrossPollinationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.MonsterSubgroupBranchingBenchmarksExact as Branching
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Moonshine.Monster3BFiniteSchrodingerFunctionModuleExact as Schrodinger
import DASHI.Moonshine.Monster3BFiniteSchrodingerHeisenbergActionExact as Action
import DASHI.Moonshine.Monster3BFiniteSchrodingerFullActionLawExact as FullAction
import DASHI.Reasoning.GeometricReasoningCandidateSelectionExact as Candidates
import DASHI.Wikimedia.IbrahimMonster3BT1WordT2ScalarRoutingSnowballExact as T1T2

monster3ANormalizer : Branching.ThreeLocalNormalizerKind
monster3ANormalizer = Branching.normalizerKind Branching.class3A

monster3BNormalizer : Branching.ThreeLocalNormalizerKind
monster3BNormalizer = Branching.normalizerKind Branching.class3B

monster3CNormalizer : Branching.ThreeLocalNormalizerKind
monster3CNormalizer = Branching.normalizerKind Branching.class3C

monster3BActionComposition :
  (g h : H.Heisenberg6) →
  (f : Schrodinger.SchrodingerFunction) →
  (x : G.X6) →
  Action.heisenbergAction (H.compose g h) f x
  ≡ Action.heisenbergAction g (Action.heisenbergAction h f) x
monster3BActionComposition = FullAction.actionCompositionPointwise

monster3BFullActionLawReceipt : Action.FullHeisenbergActionLawReceipt
monster3BFullActionLawReceipt = FullAction.canonicalFullHeisenbergActionLawReceipt

monster3BFullActionLawConsumed : Bool
monster3BFullActionLawConsumed = true

-- The exact central composition term is the semantic composition diagnostic we
-- discussed: the phase of g*h contains b_g . a_h in addition to the two
-- individual central phases.  This is a donor theorem about the finite 3B
-- candidate action, not evidence that model interventions realize it.
monster3BCentralCocycleDiagnostic :
  (g h : H.Heisenberg6) →
  H.centralPhase (H.compose g h)
  ≡ G._+3_
      (H.centralPhase g)
      (G._+3_
        (H.centralPhase h)
        (H.dot6
          (H.modulationPart (H.quotient g))
          (H.translationPart (H.quotient h))))
monster3BCentralCocycleDiagnostic g h = refl

record Monster3BSemanticActionFit
    (Intervention Input : Set)
    (encode : Input → Schrodinger.SchrodingerFunction)
    (intervene : Intervention → Input → Input) : Set₁ where
  constructor monster3b-semantic-action-fit
  field
    fittedElement : Intervention → H.Heisenberg6
    actionRealizesIntervention :
      (i : Intervention) →
      (x : Input) →
      (point : G.X6) →
      encode (intervene i x) point
      ≡ Action.heisenbergAction (fittedElement i) (encode x) point
    justification : String

open Monster3BSemanticActionFit public

record Monster3BCompositionFit
    (Intervention : Set)
    (fitElement : Intervention → H.Heisenberg6) : Set₁ where
  constructor monster3b-composition-fit
  field
    composeIntervention : Intervention → Intervention → Intervention
    labelsRespectHeisenbergComposition :
      (i j : Intervention) →
      fitElement (composeIntervention i j)
      ≡ H.compose (fitElement i) (fitElement j)
    provenance : String

record RelativeOrientationDiagnostic : Set where
  constructor relative-orientation-diagnostic
  field
    t1LiteralWordPaid : Bool
    t2CentralRolePaid : Bool
    t2ExactMatrixPaid : Bool
    exactScalarOrientationPaid : Bool
    qWordAlignmentPaid : Bool

canonicalRelativeOrientationDiagnostic : RelativeOrientationDiagnostic
canonicalRelativeOrientationDiagnostic =
  relative-orientation-diagnostic
    (T1T2.literalWordPaid T1T2.suzukiT1Receipt)
    (T1T2.centralSubgroupIdentityPaid T1T2.extraspecialT2Routing)
    (T1T2.exactMatrixElementPaid T1T2.extraspecialT2Routing)
    (T1T2.exactScalarOrientationPaid T1T2.extraspecialT2Routing)
    (T1T2.historicalQWordAlignmentPaid T1T2.extraspecialT2Routing)

record GeometricReasoningExperimentBoard : Set where
  constructor geometric-reasoning-experiment-board
  field
    baseline : Candidates.GeometricReasoningCandidate
    e8Prior : Candidates.GeometricReasoningCandidate
    monster3A : Candidates.GeometricReasoningCandidate
    monster3B : Candidates.GeometricReasoningCandidate
    monster3C : Candidates.GeometricReasoningCandidate
    pairedPerturbationsRequired : Bool
    nuisanceControlsRequired : Bool
    layerwiseTraceRequired : Bool
    compositionTestRequired : Bool
    cocycleTestRequired : Bool
    orientationTestRequired : Bool
    heldOutComparisonRequired : Bool

canonicalExperimentBoard : GeometricReasoningExperimentBoard
canonicalExperimentBoard =
  geometric-reasoning-experiment-board
    Candidates.unstructuredBaseline
    Candidates.lilaE8RootPrior
    Candidates.monster3ALocalGeometry
    Candidates.monster3BHeisenbergGeometry
    Candidates.monster3CLocalGeometry
    true true true true true true true

data Monster3BActionCreatesSemanticMechanism : Set where
data ThreeLocalLabelCreatesWinningModel : Set where
data T1T2RoleCreatesRelativeOrientation : Set where

monsterActionCannotCreateSemanticMechanism :
  Monster3BActionCreatesSemanticMechanism → ⊥
monsterActionCannotCreateSemanticMechanism ()

threeLocalLabelCannotCreateWinner :
  ThreeLocalLabelCreatesWinningModel → ⊥
threeLocalLabelCannotCreateWinner ()

t1t2RoleCannotCreateOrientation : T1T2RoleCreatesRelativeOrientation → ⊥
t1t2RoleCannotCreateOrientation ()

record LilaMonsterGeometricReasoningBoundary : Set where
  constructor lila-monster-geometric-reasoning-boundary
  field
    threeAThreeBThreeCDistinct : Bool
    monster3BFullActionLawPaid : Bool
    centralCocycleDiagnosticPaid : Bool
    semantic3BFitCandidateOnly : Bool
    t1LiteralWordPaid : Bool
    t2CentralRolePaid : Bool
    t2ExactMatrixPaid : Bool
    t2OrientationPaid : Bool
    modelSelectionRequiresExperiment : Bool
    semanticMonsterIdentityClaimed : Bool

canonicalLilaMonsterGeometricReasoningBoundary :
  LilaMonsterGeometricReasoningBoundary
canonicalLilaMonsterGeometricReasoningBoundary =
  lila-monster-geometric-reasoning-boundary
    true true true true true true false false true false
