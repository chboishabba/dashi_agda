module DASHI.Control.LearnedAbstentionBoundary where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

------------------------------------------------------------------------
-- Belief, abstention, and execution are distinct semantic layers.
------------------------------------------------------------------------

data Direction : Set where
  down neutral up : Direction

data Action : Set where
  sell hold buy flatten : Action

record Decision : Set where
  constructor decision
  field
    direction : Direction
    abstain   : Bool

compileDecision : Decision → Action
compileDecision (decision down    false) = sell
compileDecision (decision neutral false) = hold
compileDecision (decision up      false) = buy
compileDecision (decision down    true)  = hold
compileDecision (decision neutral true)  = hold
compileDecision (decision up      true)  = hold

-- Flattening is a separate risk-control request.  It is not the third value
-- of a directional carrier and cannot be produced by compileDecision.
data RiskDirective : Set where
  preserveExposure closeExposure : RiskDirective

compileRisk : RiskDirective → Action → Action
compileRisk preserveExposure a = a
compileRisk closeExposure    a = flatten

abstentionCompilesToHold : (d : Direction) →
  compileDecision (decision d true) ≡ hold
abstentionCompilesToHold down    = refl
abstentionCompilesToHold neutral = refl
abstentionCompilesToHold up      = refl

neutralDoesNotFlatten :
  compileDecision (decision neutral false) ≡ hold
neutralDoesNotFlatten = refl

onlyRiskClosesExposure : (a : Action) →
  compileRisk closeExposure a ≡ flatten
onlyRiskClosesExposure a = refl

------------------------------------------------------------------------
-- Execution contract: HOLD is observational identity; FLAT is explicit.
------------------------------------------------------------------------

record ExecutionSemantics (Exposure : Set) : Set₁ where
  field
    applySell    : Exposure → Exposure
    applyBuy     : Exposure → Exposure
    flatExposure : Exposure

execute : {Exposure : Set} →
  ExecutionSemantics Exposure → Action → Exposure → Exposure
execute E sell    x = ExecutionSemantics.applySell E x
execute E hold    x = x
execute E buy     x = ExecutionSemantics.applyBuy E x
execute E flatten x = ExecutionSemantics.flatExposure E

holdPreservesExposure :
  {Exposure : Set} (E : ExecutionSemantics Exposure) (x : Exposure) →
  execute E hold x ≡ x
holdPreservesExposure E x = refl

flattenIsExplicit :
  {Exposure : Set} (E : ExecutionSemantics Exposure) (x : Exposure) →
  execute E flatten x ≡ ExecutionSemantics.flatExposure E
flattenIsExplicit E x = refl

abstentionPreservesExposure :
  {Exposure : Set} (E : ExecutionSemantics Exposure)
  (d : Direction) (x : Exposure) →
  execute E (compileDecision (decision d true)) x ≡ x
abstentionPreservesExposure E down    x = refl
abstentionPreservesExposure E neutral x = refl
abstentionPreservesExposure E up      x = refl

------------------------------------------------------------------------
-- Ternary carrier projection.  The carrier represents direction only;
-- abstention remains an independent proposition.
------------------------------------------------------------------------

tritDirection : Trit → Direction
tritDirection neg = down
tritDirection zer = neutral
tritDirection pos = up

record TernaryBelief : Set where
  constructor ternaryBelief
  field
    carrier  : Trit
    abstain  : Bool

compileTernaryBelief : TernaryBelief → Action
compileTernaryBelief (ternaryBelief t a) =
  compileDecision (decision (tritDirection t) a)

ternaryAbstentionIsHold : (t : Trit) →
  compileTernaryBelief (ternaryBelief t true) ≡ hold
ternaryAbstentionIsHold neg = refl
ternaryAbstentionIsHold zer = refl
ternaryAbstentionIsHold pos = refl

zeroCarrierIsNotClose :
  compileTernaryBelief (ternaryBelief zer false) ≡ hold
zeroCarrierIsNotClose = refl

------------------------------------------------------------------------
-- Learned knobs are certificates over a frozen candidate family.
--
-- This deliberately does not assert that any objective is economically
-- correct.  A calibration result must carry its validation relation and a
-- proof/certificate that the chosen candidate is no worse than every member
-- of the declared candidate family.
------------------------------------------------------------------------

record CalibrationProblem : Set₁ where
  field
    Knob       : Set
    Loss       : Set
    _≤loss_    : Loss → Loss → Set
    validation : Knob → Loss

record LearnedKnob (P : CalibrationProblem) : Set₁ where
  open CalibrationProblem P
  field
    chosen  : Knob
    optimal : (candidate : Knob) →
      validation chosen ≤loss validation candidate

record WalkForwardBoundary : Set₁ where
  field
    Time          : Set
    Knob          : Set
    available     : Time → Knob → Set
    selected      : Time → Knob
    selectedIsPastAvailable : (t : Time) → available t (selected t)

-- A learned boundary is therefore not a literal constant embedded in the
-- strategy.  It is a time-indexed, leakage-constrained selection carrying a
-- validation certificate supplied by the implementation or audit layer.
record CertifiedBoundary : Set₁ where
  field
    calibration : CalibrationProblem
    learned     : LearnedKnob calibration
    walkForward : WalkForwardBoundary
