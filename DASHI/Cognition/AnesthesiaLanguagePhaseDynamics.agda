module DASHI.Cognition.AnesthesiaLanguagePhaseDynamics where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_≤_; z≤n; s≤s)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Cognition.DashiCognitiveSystem as Cognitive

------------------------------------------------------------------------
-- Exact fixed-point control recurrence.
--
-- effectNext = persistence * effect + plasmaGain * plasma
--
-- A physical calibration supplies the scale.  The Agda layer proves the
-- algebraic control structure without pretending arbitrary Nat literals are
-- concentrations in clinical units.
------------------------------------------------------------------------

record EffectSiteModel : Set where
  constructor effectSiteModel
  field
    persistence : Nat
    plasmaGain  : Nat

record EffectSiteState : Set where
  constructor effectSiteState
  field
    plasma : Nat
    effect : Nat

open EffectSiteModel public
open EffectSiteState public

effectSiteStep : EffectSiteModel → EffectSiteState → EffectSiteState
effectSiteStep model state =
  effectSiteState
    (plasma state)
    (persistence model * effect state + plasmaGain model * plasma state)

iterate : ∀ {A : Set} → Nat → (A → A) → A → A
iterate zero f x = x
iterate (suc n) f x = iterate n f (f x)

effectSiteTrajectory : Nat → EffectSiteModel → EffectSiteState → EffectSiteState
effectSiteTrajectory steps model = iterate steps (effectSiteStep model)

------------------------------------------------------------------------
-- Compensation-versus-impairment margin.
--
-- A linear compensatory term followed by a cubic impairment term gives the
-- observed small upward kink before collapse without inserting a hand-drawn
-- GELU.  It is the finite polynomial normal form
--
--   support(Ce)    = baseline + compensation * Ce + coupling
--   impairment(Ce) = anesthetic * Ce^3 + obligation * stackDepth.
------------------------------------------------------------------------

pow : Nat → Nat → Nat
pow x zero = 1
pow x (suc n) = x * pow x n

cube : Nat → Nat
cube x = pow x 3

record MarginDynamics : Set where
  constructor marginDynamics
  field
    baselineSupport   : Nat
    compensationGain : Nat
    anestheticGain    : Nat
    obligationPenalty : Nat

open MarginDynamics public

compareMargin : Nat → Nat → Cognitive.SignedMargin
compareMargin zero zero = Cognitive.boundaryMargin
compareMargin zero (suc negative) = Cognitive.negativeMargin (suc negative)
compareMargin (suc positive) zero = Cognitive.positiveMargin (suc positive)
compareMargin (suc support) (suc impairment) = compareMargin support impairment

supportAt : MarginDynamics → Nat → Nat → Nat
supportAt dynamics effect coupling =
  baselineSupport dynamics + compensationGain dynamics * effect + coupling

impairmentAt : MarginDynamics → Nat → Nat → Nat
impairmentAt dynamics effect stackDepth =
  anestheticGain dynamics * cube effect
  + obligationPenalty dynamics * stackDepth

marginAt : MarginDynamics → Nat → Nat → Nat → Cognitive.SignedMargin
marginAt dynamics effect stackDepth coupling =
  compareMargin
    (supportAt dynamics effect coupling)
    (impairmentAt dynamics effect stackDepth)

canonicalKinkDynamics : MarginDynamics
canonicalKinkDynamics = marginDynamics 10 4 1 0

marginStartsPositive :
  marginAt canonicalKinkDynamics 0 0 0 ≡ Cognitive.positiveMargin 10
marginStartsPositive = refl

marginInitiallyRises :
  marginAt canonicalKinkDynamics 1 0 0 ≡ Cognitive.positiveMargin 13
marginInitiallyRises = refl

marginTurnsDownBeforeCollapse :
  marginAt canonicalKinkDynamics 2 0 0 ≡ Cognitive.positiveMargin 10
marginTurnsDownBeforeCollapse = refl

marginCrossesNegative :
  marginAt canonicalKinkDynamics 3 0 0 ≡ Cognitive.negativeMargin 5
marginCrossesNegative = refl

couplingRaisesSupportExactly :
  marginAt canonicalKinkDynamics 3 0 6 ≡ Cognitive.positiveMargin 1
couplingRaisesSupportExactly = refl

------------------------------------------------------------------------
-- Continuous/graded control can be observed through a ternary control band:
-- inactive/projective, compensatory-positive, impairment-negative.
------------------------------------------------------------------------

data NatOrdering : Set where
  less equal greater : NatOrdering

compareNat : Nat → Nat → NatOrdering
compareNat zero zero = equal
compareNat zero (suc _) = less
compareNat (suc _) zero = greater
compareNat (suc m) (suc n) = compareNat m n

controlTrit : Nat → Nat → Nat → BT.Trit
controlTrit lower upper control with compareNat control lower
... | less = BT.zero
... | equal = BT.pos
... | greater with compareNat control upper
...   | less = BT.pos
...   | equal = BT.neg
...   | greater = BT.neg

controlBelowLowerIsProjective : controlTrit 2 5 1 ≡ BT.zero
controlBelowLowerIsProjective = refl

controlBetweenThresholdsIsPositive : controlTrit 2 5 3 ≡ BT.pos
controlBetweenThresholdsIsPositive = refl

controlAboveUpperIsNegative : controlTrit 2 5 7 ≡ BT.neg
controlAboveUpperIsNegative = refl

------------------------------------------------------------------------
-- Schmitt-style phase gate with stack rebuilding.  This is the exact finite
-- hysteresis mechanism: descent and ascent use different thresholds, and a
-- collapsed system cannot recover until its obligation scaffold is rebuilt.
------------------------------------------------------------------------

record HysteresisThresholds : Set where
  constructor hysteresisThresholds
  field
    collapseThreshold : Nat
    recoveryThreshold : Nat
    recoveryBelowCollapse : recoveryThreshold ≤ collapseThreshold

open HysteresisThresholds public

data ControlPhase : Set where
  productive : ControlPhase
  collapsed : ControlPhase

atLeast : Nat → Nat → Bool
atLeast zero required with required
... | zero = true
... | suc _ = false
atLeast (suc actual) zero = true
atLeast (suc actual) (suc required) = atLeast actual required

atMost : Nat → Nat → Bool
atMost actual limit = atLeast limit actual

phaseStep :
  HysteresisThresholds →
  ControlPhase →
  Nat →
  Nat →
  Nat →
  ControlPhase
phaseStep thresholds productive control openStack requiredStack with
  atLeast control (collapseThreshold thresholds)
... | true = collapsed
... | false = productive
phaseStep thresholds collapsed control openStack requiredStack with
  atMost control (recoveryThreshold thresholds) | atLeast openStack requiredStack
... | true | true = productive
... | _ | _ = collapsed

canonicalThresholds : HysteresisThresholds
canonicalThresholds = hysteresisThresholds 3 1 (s≤s z≤n)

collapseAtUpperThreshold :
  phaseStep canonicalThresholds productive 3 3 3 ≡ collapsed
collapseAtUpperThreshold = refl

recoveryBlockedUntilStackRebuilt :
  phaseStep canonicalThresholds collapsed 1 2 3 ≡ collapsed
recoveryBlockedUntilStackRebuilt = refl

recoveryAfterStackRebuilt :
  phaseStep canonicalThresholds collapsed 1 3 3 ≡ productive
recoveryAfterStackRebuilt = refl

sameControlDifferentPath :
  phaseStep canonicalThresholds productive 2 3 3
  ≡ productive
sameControlDifferentPath = refl

sameControlCollapsedPathRemainsCollapsed :
  phaseStep canonicalThresholds collapsed 2 3 3
  ≡ collapsed
sameControlCollapsedPathRemainsCollapsed = refl

------------------------------------------------------------------------
-- Cusp discriminant boundary.
-- For x^3 - r x - h = 0, repeated roots occur at
--
--   4 r^3 = 27 h^2.
--
-- The coefficient 27 is literally 3^3, but it arises from eliminating x
-- between the cubic and its derivative, not from the ternary cognitive gate.
------------------------------------------------------------------------

CuspBoundary : Nat → Nat → Set
CuspBoundary r h = 4 * pow r 3 ≡ 27 * pow h 2

twentySevenIsThreeCubed : 27 ≡ 3 * 3 * 3
twentySevenIsThreeCubed = refl

canonicalCuspBoundary : CuspBoundary 3 2
canonicalCuspBoundary = refl
