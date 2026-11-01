module DASHI.Foundations.Base369MonsterSemanticCoordinateSystemExact where

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369MonsterNamedIdentityRegistryExact as Registry
import DASHI.Foundations.Base369JCoarseFineStableIdentityDisciplineExact as JIdentity
import DASHI.Foundations.Base369Completion54SituatedTriadBridgeExact as Completion
import DASHI.Foundations.Base369StableAlgebraicIdentityTowerExact as Stable

------------------------------------------------------------------------
-- MONSTER SEMANTIC COORDINATE SYSTEM
--
-- Meaning is attached as named projections/fibres over one underlying state.
-- We do NOT multiply all semantic coordinates together and thereby inflate the
-- carrier.  A state s is read through maps
--
--   m(s), j(s), d(s), i(s), h(s), r(s), f(s), ...
--
-- Some are literal product projections; others are supplied observer/fibre
-- coordinates whose attachment must be separately justified.
------------------------------------------------------------------------

SemanticBaseState : Set
SemanticBaseState = Registry.NamedMonsterDecisionState196830

------------------------------------------------------------------------
-- 1. Canonical literal projections already owned by the named 196830 carrier.
------------------------------------------------------------------------

modeOf : SemanticBaseState → Stable.FiveMode
modeOf = Registry.modeIdentity

situatedPerspectiveOf : SemanticBaseState → Completion.SituatedTriadRow
situatedPerspectiveOf = Registry.situatedPerspective

decisionConditionOf : SemanticBaseState → Registry.DecisionCondition27
decisionConditionOf = Registry.decisionCondition

appraisalOf : SemanticBaseState → Stable.Appraisal729
appraisalOf = Registry.appraisalState

------------------------------------------------------------------------
-- 2. Additional semantic coordinates are maps/fibres, not automatic factors.
------------------------------------------------------------------------

record SemanticCoordinateSystem
    (History Residual FutureCone : Set) : Set₁ where
  constructor semantic-coordinate-system
  field
    coarsePhaseOf : SemanticBaseState → JIdentity.JCoarse9
    historyOf : SemanticBaseState → History
    residualOf : SemanticBaseState → Residual
    futureConeOf : SemanticBaseState → FutureCone

open SemanticCoordinateSystem public

record SemanticReading
    {History Residual FutureCone : Set}
    (system : SemanticCoordinateSystem History Residual FutureCone)
    (state : SemanticBaseState) : Set where
  constructor semantic-reading
  field
    mode : Stable.FiveMode
    situatedPerspective : Completion.SituatedTriadRow
    coarsePhase : JIdentity.JCoarse9
    decisionCondition : Registry.DecisionCondition27
    appraisal : Stable.Appraisal729
    history : History
    residual : Residual
    futureCone : FutureCone

    modeExact : mode ≡ modeOf state
    situatedExact : situatedPerspective ≡ situatedPerspectiveOf state
    phaseExact : coarsePhase ≡ coarsePhaseOf system state
    decisionExact : decisionCondition ≡ decisionConditionOf state
    appraisalExact : appraisal ≡ appraisalOf state
    historyExact : history ≡ historyOf system state
    residualExact : residual ≡ residualOf system state
    futureExact : futureCone ≡ futureConeOf system state

canonicalReading :
  {History Residual FutureCone : Set} →
  (system : SemanticCoordinateSystem History Residual FutureCone) →
  (state : SemanticBaseState) →
  SemanticReading system state
canonicalReading system state =
  semantic-reading
    (modeOf state)
    (situatedPerspectiveOf state)
    (coarsePhaseOf system state)
    (decisionConditionOf state)
    (appraisalOf state)
    (historyOf system state)
    (residualOf system state)
    (futureConeOf system state)
    refl refl refl refl refl refl refl refl

------------------------------------------------------------------------
-- 3. An action becomes semantically interpretable by commuting with the named
-- coordinate projections.  This is the shape required from a future actual
-- Monster action/intertwiner.
------------------------------------------------------------------------

record SemanticActionIntertwiner
    {G History Residual FutureCone : Set}
    (system : SemanticCoordinateSystem History Residual FutureCone)
    (act : G → SemanticBaseState → SemanticBaseState) : Set₁ where
  field
    modeAction : G → Stable.FiveMode → Stable.FiveMode
    situatedAction :
      G → Completion.SituatedTriadRow → Completion.SituatedTriadRow
    phaseAction : G → JIdentity.JCoarse9 → JIdentity.JCoarse9
    decisionAction :
      G → Registry.DecisionCondition27 → Registry.DecisionCondition27
    appraisalAction : G → Stable.Appraisal729 → Stable.Appraisal729
    historyAction : G → History → History
    residualAction : G → Residual → Residual
    futureConeAction : G → FutureCone → FutureCone

    modeIntertwines :
      (g : G) → (s : SemanticBaseState) →
      modeOf (act g s) ≡ modeAction g (modeOf s)

    situatedIntertwines :
      (g : G) → (s : SemanticBaseState) →
      situatedPerspectiveOf (act g s)
      ≡ situatedAction g (situatedPerspectiveOf s)

    phaseIntertwines :
      (g : G) → (s : SemanticBaseState) →
      coarsePhaseOf system (act g s)
      ≡ phaseAction g (coarsePhaseOf system s)

    decisionIntertwines :
      (g : G) → (s : SemanticBaseState) →
      decisionConditionOf (act g s)
      ≡ decisionAction g (decisionConditionOf s)

    appraisalIntertwines :
      (g : G) → (s : SemanticBaseState) →
      appraisalOf (act g s)
      ≡ appraisalAction g (appraisalOf s)

    historyIntertwines :
      (g : G) → (s : SemanticBaseState) →
      historyOf system (act g s)
      ≡ historyAction g (historyOf system s)

    residualIntertwines :
      (g : G) → (s : SemanticBaseState) →
      residualOf system (act g s)
      ≡ residualAction g (residualOf system s)

    futureConeIntertwines :
      (g : G) → (s : SemanticBaseState) →
      futureConeOf system (act g s)
      ≡ futureConeAction g (futureConeOf system s)

open SemanticActionIntertwiner public

------------------------------------------------------------------------
-- 4. Identity action fixture: verifies the shape without fabricating a Monster
-- action.  All semantic coordinates are retained definitionally.
------------------------------------------------------------------------

data IdentityAction : Set where identityAction : IdentityAction

identityOnBase : IdentityAction → SemanticBaseState → SemanticBaseState
identityOnBase identityAction state = state

identitySemanticIntertwiner :
  {History Residual FutureCone : Set} →
  (system : SemanticCoordinateSystem History Residual FutureCone) →
  SemanticActionIntertwiner system identityOnBase
identitySemanticIntertwiner system = record
  { modeAction = λ _ x → x
  ; situatedAction = λ _ x → x
  ; phaseAction = λ _ x → x
  ; decisionAction = λ _ x → x
  ; appraisalAction = λ _ x → x
  ; historyAction = λ _ x → x
  ; residualAction = λ _ x → x
  ; futureConeAction = λ _ x → x
  ; modeIntertwines = λ _ _ → refl
  ; situatedIntertwines = λ _ _ → refl
  ; phaseIntertwines = λ _ _ → refl
  ; decisionIntertwines = λ _ _ → refl
  ; appraisalIntertwines = λ _ _ → refl
  ; historyIntertwines = λ _ _ → refl
  ; residualIntertwines = λ _ _ → refl
  ; futureConeIntertwines = λ _ _ → refl
  }

------------------------------------------------------------------------
-- 5. Boundaries.
------------------------------------------------------------------------

data SemanticFieldsAreIndependentProductFactors : Set where
data CoarsePhaseCardinalityCreatesAttachment : Set where
data SemanticIntertwinerCreatesMonsterAction : Set where
data EqualCoordinateCodesMeanEqualHistories : Set where

semanticFieldsNeedNotBeIndependentFactors :
  SemanticFieldsAreIndependentProductFactors → ⊥
semanticFieldsNeedNotBeIndependentFactors ()

coarsePhaseCardinalityDoesNotCreateAttachment :
  CoarsePhaseCardinalityCreatesAttachment → ⊥
coarsePhaseCardinalityDoesNotCreateAttachment ()

semanticIntertwinerShapeDoesNotCreateMonsterAction :
  SemanticIntertwinerCreatesMonsterAction → ⊥
semanticIntertwinerShapeDoesNotCreateMonsterAction ()

equalCoordinateCodesNeedNotMeanEqualHistories :
  EqualCoordinateCodesMeanEqualHistories → ⊥
equalCoordinateCodesNeedNotMeanEqualHistories ()

record MonsterSemanticCoordinateBoundary : Set where
  constructor monster-semantic-coordinate-boundary
  field
    base196830StateRetained : Bool
    literalModeProjectionNamed : Bool
    literalDecisionProjectionNamed : Bool
    literalAppraisalProjectionNamed : Bool
    phaseHistoryResidualFutureAreAttachableFibres : Bool
    semanticReadingDoesNotInflateCarrier : Bool
    actionIntertwinerRequiresEightCommutingCoordinates : Bool
    identityFixtureConstructed : Bool
    coordinateNamingAloneCreatesMonsterAction : Bool

canonicalMonsterSemanticCoordinateBoundary : MonsterSemanticCoordinateBoundary
canonicalMonsterSemanticCoordinateBoundary =
  monster-semantic-coordinate-boundary
    true true true true true true true true false
