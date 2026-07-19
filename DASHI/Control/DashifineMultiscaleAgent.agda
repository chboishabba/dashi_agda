module DASHI.Control.DashifineMultiscaleAgent where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

------------------------------------------------------------------------
-- Stage 3 -> 6: direction evidence and an unsigned actionability order
------------------------------------------------------------------------

record DirectionEvidence : Set where
  constructor directionEvidence
  field
    supportsSell : Bool
    supportsBuy  : Bool

open DirectionEvidence public

-- Both directions may coexist before control closure.  A conflict is retained
-- in DirectionEvidence; its collapsed direction is neutral rather than an
-- arbitrary vote.
collapseDirection : DirectionEvidence → Trit
collapseDirection (directionEvidence false false) = zer
collapseDirection (directionEvidence false true)  = pos
collapseDirection (directionEvidence true false)  = neg
collapseDirection (directionEvidence true true)   = zer

conflictMask : DirectionEvidence → Bool
conflictMask (directionEvidence false false) = false
conflictMask (directionEvidence false true)  = false
conflictMask (directionEvidence true false)  = false
conflictMask (directionEvidence true true)   = true

data ActionabilityBand : Set where
  low middle high : ActionabilityBand

-- The order is the control-relevant quotient of an underlying [0,1]-valued
-- actionability functional.  It is unsigned and monotone.
data _≤band_ : ActionabilityBand → ActionabilityBand → Set where
  low≤    : ∀ {a} → low ≤band a
  middle≤ : ∀ {a} → middle ≤band a → high ≤band a
  high≤   : high ≤band high

bandRefl : (a : ActionabilityBand) → a ≤band a
bandRefl low = low≤
bandRefl middle = middle≤ high≤
bandRefl high = high≤

bandTrans : ∀ {a b c} → a ≤band b → b ≤band c → a ≤band c
bandTrans low≤ _ = low≤
bandTrans (middle≤ high≤) (middle≤ high≤) = middle≤ high≤
bandTrans (middle≤ high≤) high≤ = middle≤ high≤
bandTrans high≤ high≤ = high≤

minBand : ActionabilityBand → ActionabilityBand → ActionabilityBand
minBand low _ = low
minBand _ low = low
minBand middle _ = middle
minBand _ middle = middle
minBand high high = high

------------------------------------------------------------------------
-- A valuation functional separates raw evidence from its actionability band.
------------------------------------------------------------------------

record ActionabilityValuation (Evidence : Set) : Set₁ where
  field
    _refines_ : Evidence → Evidence → Set
    valuation : Evidence → ActionabilityBand
    refinementMonotone :
      ∀ {coarse fine} → coarse refines fine →
      valuation coarse ≤band valuation fine

------------------------------------------------------------------------
-- Vertical order-ternary planes: 001 = low, 011 = middle, 111 = high.
-- P is the strongest threshold, Q the middle threshold, N the ground plane.
------------------------------------------------------------------------

record PQN : Set where
  constructor pqn
  field
    P Q N : Bool

open PQN public

encodePQN : ActionabilityBand → PQN
encodePQN low    = pqn false false true
encodePQN middle = pqn false true  true
encodePQN high   = pqn true  true  true

decodePQN : PQN → ActionabilityBand
decodePQN (pqn true  _     _) = high
decodePQN (pqn false true  _) = middle
decodePQN (pqn false false _) = low

decodeEncodePQN : (a : ActionabilityBand) → decodePQN (encodePQN a) ≡ a
decodeEncodePQN low = refl
decodeEncodePQN middle = refl
decodeEncodePQN high = refl

OrderField : Set → Set
OrderField X = X → PQN

P-mask : {X : Set} → OrderField X → X → Bool
P-mask field x = P (field x)

Q-mask : {X : Set} → OrderField X → X → Bool
Q-mask field x = Q (field x)

N-mask : {X : Set} → OrderField X → X → Bool
N-mask field x = N (field x)

------------------------------------------------------------------------
-- Stage 6 -> 9: memoryful control closure.
------------------------------------------------------------------------

data ControlState : Set where
  HOLD BUY SELL : ControlState

-- Exact hysteresis automaton over the three actionability bands.
-- low exits, middle preserves the prior state, and high admits a clear
-- direction or preserves the prior state when the evidence is unresolved.
stepControl : ActionabilityBand → Trit → ControlState → ControlState
stepControl low    _   _     = HOLD
stepControl middle _   prior = prior
stepControl high   neg _     = SELL
stepControl high   zer prior = prior
stepControl high   pos _     = BUY

lowAlwaysHolds : (d : Trit) (prior : ControlState) →
  stepControl low d prior ≡ HOLD
lowAlwaysHolds d prior = refl

middlePreserves : (d : Trit) (prior : ControlState) →
  stepControl middle d prior ≡ prior
middlePreserves d prior = refl

highBuyCloses : (prior : ControlState) →
  stepControl high pos prior ≡ BUY
highBuyCloses prior = refl

highSellCloses : (prior : ControlState) →
  stepControl high neg prior ≡ SELL
highSellCloses prior = refl

-- Hysteresis is a real state dimension: the same instantaneous observation
-- produces distinct results from distinct prior states.
middleMemoryWitness₁ : stepControl middle pos HOLD ≡ HOLD
middleMemoryWitness₁ = refl

middleMemoryWitness₂ : stepControl middle pos BUY ≡ BUY
middleMemoryWitness₂ = refl

------------------------------------------------------------------------
-- Multiscale composition before closure.
------------------------------------------------------------------------

record ScaleCell : Set where
  constructor scaleCell
  field
    direction     : DirectionEvidence
    actionability : ActionabilityBand

open ScaleCell public

fuseDirection : Trit → Trit → Trit
fuseDirection zer d = d
fuseDirection d zer = d
fuseDirection neg neg = neg
fuseDirection pos pos = pos
fuseDirection neg pos = zer
fuseDirection pos neg = zer

combineCells : ScaleCell → ScaleCell → ScaleCell
combineCells a b =
  scaleCell
    (directionEvidence sell buy)
    (minBand (actionability a) (actionability b))
  where
    fused : Trit
    fused = fuseDirection (collapseDirection (direction a))
                          (collapseDirection (direction b))

    sell : Bool
    sell with fused
    ... | neg = true
    ... | zer = false
    ... | pos = false

    buy : Bool
    buy with fused
    ... | neg = false
    ... | zer = false
    ... | pos = true

closeCell : ScaleCell → ControlState → ControlState
closeCell cell prior =
  stepControl (actionability cell)
              (collapseDirection (direction cell))
              prior

combinedActionabilityIsBottleneck : (a b : ScaleCell) →
  actionability (combineCells a b) ≡
  minBand (actionability a) (actionability b)
combinedActionabilityIsBottleneck a b = refl
