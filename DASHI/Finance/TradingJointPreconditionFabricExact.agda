module DASHI.Finance.TradingJointPreconditionFabricExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Stable transition first; scalar size/exposure are observations of it.
------------------------------------------------------------------------

record TransitionCarrier : Set₁ where
  constructor transitionCarrier
  field
    Transition : Set
    grossExposure : Transition → Nat
    turnover : Transition → Nat
    transitionLabel : Transition → String

open TransitionCarrier public

------------------------------------------------------------------------
-- Full, dependent precondition fabric.
--
-- Each axis is indexed by the SAME state and SAME candidate transition.
-- Pairwise/marginal satisfiability does not imply joint admissibility: the
-- final JointCompatibility field is an irreducible relational receipt.
------------------------------------------------------------------------

record TradingPreconditionFabric
    (State : Set)
    (carrier : TransitionCarrier) : Set₁ where
  field
    UniversePIT : State → Transition carrier → Set
    MarketDataPIT : State → Transition carrier → Set
    FactorResidualValid : State → Transition carrier → Set
    InventoryCompatible : State → Transition carrier → Set
    LiquidityCapacity : State → Transition carrier → Set
    RiskBudget : State → Transition carrier → Set
    Neutrality : State → Transition carrier → Set
    TurnoverBudget : State → Transition carrier → Set
    CostImpactViable : State → Transition carrier → Set
    ExecutionFeasible : State → Transition carrier → Set
    AuthorityCurrent : State → Transition carrier → Set

    -- This is intentionally not derived from the marginal fields.  It can
    -- express coupled conditions such as liquidity x size x turnover x
    -- neutrality, or inventory x crowding x execution interaction.
    JointCompatibility : State → Transition carrier → Set

open TradingPreconditionFabric public

record JointlyAdmissible
    {State : Set}
    {carrier : TransitionCarrier}
    (fabric : TradingPreconditionFabric State carrier)
    (state : State)
    (delta : Transition carrier) : Set where
  constructor jointlyAdmissible
  field
    universePIT : UniversePIT fabric state delta
    marketDataPIT : MarketDataPIT fabric state delta
    factorResidualValid : FactorResidualValid fabric state delta
    inventoryCompatible : InventoryCompatible fabric state delta
    liquidityCapacity : LiquidityCapacity fabric state delta
    riskBudget : RiskBudget fabric state delta
    neutrality : Neutrality fabric state delta
    turnoverBudget : TurnoverBudget fabric state delta
    costImpactViable : CostImpactViable fabric state delta
    executionFeasible : ExecutionFeasible fabric state delta
    authorityCurrent : AuthorityCurrent fabric state delta
    jointCompatibility : JointCompatibility fabric state delta

open JointlyAdmissible public

AdmissibleTransitionFibre :
  {State : Set} →
  {carrier : TransitionCarrier} →
  TradingPreconditionFabric State carrier →
  State → Set
AdmissibleTransitionFibre {carrier = carrier} fabric state =
  Σ (Transition carrier) (λ delta → JointlyAdmissible fabric state delta)

------------------------------------------------------------------------
-- Size and exposure are cardinal/numeric shadows of an already-identified
-- transition. They are not free policy outputs.
------------------------------------------------------------------------

admissibleGrossExposure :
  {State : Set}
  {carrier : TransitionCarrier}
  {fabric : TradingPreconditionFabric State carrier}
  {state : State} →
  AdmissibleTransitionFibre fabric state → Nat
admissibleGrossExposure {carrier = carrier} candidate =
  grossExposure carrier (proj₁ candidate)

admissibleTurnover :
  {State : Set}
  {carrier : TransitionCarrier}
  {fabric : TradingPreconditionFabric State carrier}
  {state : State} →
  AdmissibleTransitionFibre fabric state → Nat
admissibleTurnover {carrier = carrier} candidate =
  turnover carrier (proj₁ candidate)

------------------------------------------------------------------------
-- Exact finite witness: every marginal stratum can be satisfied while the
-- joint interaction still blocks the larger transition.
------------------------------------------------------------------------

data DemoState : Set where
  liveState : DemoState

data DemoTransition : Set where
  conservativeTransition expansiveTransition : DemoTransition

demoCarrier : TransitionCarrier
demoCarrier = transitionCarrier DemoTransition exposure turn label
  where
    exposure : DemoTransition → Nat
    exposure conservativeTransition = 1
    exposure expansiveTransition = 3

    turn : DemoTransition → Nat
    turn conservativeTransition = 1
    turn expansiveTransition = 3

    label : DemoTransition → String
    label conservativeTransition = "conservative transition"
    label expansiveTransition = "expansive transition"

data MarginalOK : DemoState → DemoTransition → Set where
  conservativeMarginalOK : MarginalOK liveState conservativeTransition
  expansiveMarginalOK : MarginalOK liveState expansiveTransition

data JointOK : DemoState → DemoTransition → Set where
  conservativeJointOK : JointOK liveState conservativeTransition

demoFabric : TradingPreconditionFabric DemoState demoCarrier
demoFabric = record
  { UniversePIT = MarginalOK
  ; MarketDataPIT = MarginalOK
  ; FactorResidualValid = MarginalOK
  ; InventoryCompatible = MarginalOK
  ; LiquidityCapacity = MarginalOK
  ; RiskBudget = MarginalOK
  ; Neutrality = MarginalOK
  ; TurnoverBudget = MarginalOK
  ; CostImpactViable = MarginalOK
  ; ExecutionFeasible = MarginalOK
  ; AuthorityCurrent = MarginalOK
  ; JointCompatibility = JointOK
  }

conservativeAdmissible :
  JointlyAdmissible demoFabric liveState conservativeTransition
conservativeAdmissible =
  jointlyAdmissible
    conservativeMarginalOK
    conservativeMarginalOK
    conservativeMarginalOK
    conservativeMarginalOK
    conservativeMarginalOK
    conservativeMarginalOK
    conservativeMarginalOK
    conservativeMarginalOK
    conservativeMarginalOK
    conservativeMarginalOK
    conservativeMarginalOK
    conservativeJointOK

allMarginalsHoldForExpansive :
  MarginalOK liveState expansiveTransition
allMarginalsHoldForExpansive = expansiveMarginalOK

expansiveNotJointlyAdmissible :
  JointlyAdmissible demoFabric liveState expansiveTransition → ⊥
expansiveNotJointlyAdmissible receipt =
  noExpansiveJoint (jointCompatibility receipt)
  where
    noExpansiveJoint : JointOK liveState expansiveTransition → ⊥
    noExpansiveJoint ()

record JointPreconditionBoundary : Set where
  constructor jointPreconditionBoundary
  field
    marginalChecksDetermineAdmissibility : Bool
    marginalChecksDetermineAdmissibilityIsFalse :
      marginalChecksDetermineAdmissibility ≡ false
    sizeChosenAfterAdmissibility : Bool
    sizeChosenAfterAdmissibilityIsFalse :
      sizeChosenAfterAdmissibility ≡ false
    transitionIdentityPrecedesNumericSize : Bool
    transitionIdentityPrecedesNumericSizeIsTrue :
      transitionIdentityPrecedesNumericSize ≡ true
    jointRelationalReceiptRequired : Bool
    jointRelationalReceiptRequiredIsTrue :
      jointRelationalReceiptRequired ≡ true

canonicalJointPreconditionBoundary : JointPreconditionBoundary
canonicalJointPreconditionBoundary =
  jointPreconditionBoundary false refl false refl true refl true refl

boundaryStatement : String
boundaryStatement =
  "Exposure and size are projections of a stable candidate portfolio transition. A transition is admissible only when every state-indexed precondition and the irreducible joint-compatibility stratum are inhabited; satisfying all marginal checks separately does not authorize the transition or its size."
