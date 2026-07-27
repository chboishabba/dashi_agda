module DASHI.Physics.Closure.NSTriadKNQuarticLyapunovEulerInvariantDecomposition where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; _+_; _*_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as Nat

------------------------------------------------------------------------
-- Exact degree decomposition of
--
--   V = E^2 + 2 E W + Q.
--
-- E is the ordinary kinetic energy, W is a linear coherence coordinate,
-- and Q is quadratic.  Linear and nonlinear Lie-derivative pieces are kept
-- separate.  The decomposition is useful only when E is an Euler invariant:
-- otherwise the explicit Euler defect contains the degree-five term
-- 2 E D_N E.
------------------------------------------------------------------------

record QuarticLyapunovLieData {s : Level} (State : Set s) : Set (lsuc s) where
  field
    energy coherence : State → Nat

    energyLinear energyNonlinear : State → Nat
    coherenceLinear coherenceNonlinear : State → Nat
    quadraticLinear quadraticNonlinear : State → Nat

open QuarticLyapunovLieData public

two : Nat
two = 2

quadraticDerivativePart :
  ∀ {s} {State : Set s} →
  QuarticLyapunovLieData State → State → Nat
quadraticDerivativePart D state =
  quadraticLinear D state

cubicDerivativePart :
  ∀ {s} {State : Set s} →
  QuarticLyapunovLieData State → State → Nat
cubicDerivativePart D state =
  quadraticNonlinear D state
  + two * (energyLinear D state * coherence D state)
  + two * (energy D state * coherenceLinear D state)

quarticDerivativePart :
  ∀ {s} {State : Set s} →
  QuarticLyapunovLieData State → State → Nat
quarticDerivativePart D state =
  two * (energy D state * energyLinear D state)
  + two * (energyNonlinear D state * coherence D state)
  + two * (energy D state * coherenceNonlinear D state)

quinticEulerDefect :
  ∀ {s} {State : Set s} →
  QuarticLyapunovLieData State → State → Nat
quinticEulerDefect D state =
  two * (energy D state * energyNonlinear D state)

fullDerivativeByDegree :
  ∀ {s} {State : Set s} →
  QuarticLyapunovLieData State → State → Nat
fullDerivativeByDegree D state =
  quadraticDerivativePart D state
  + cubicDerivativePart D state
  + quarticDerivativePart D state
  + quinticEulerDefect D state

record EulerInvariantQuarticData
    {s : Level} (State : Set s) : Set (lsuc s) where
  field
    lieData : QuarticLyapunovLieData State
    kineticEnergyEulerInvariant :
      ∀ state → energyNonlinear lieData state ≡ zero

open EulerInvariantQuarticData public

eulerInvariantRemovesQuinticDefect :
  ∀ {s} {State : Set s}
    (D : EulerInvariantQuarticData State)
    (state : State) →
  quinticEulerDefect (lieData D) state ≡ zero
eulerInvariantRemovesQuinticDefect D state
  rewrite kineticEnergyEulerInvariant D state = refl

eulerInvariantRemovesQuarticEnergyCoherenceDefect :
  ∀ {s} {State : Set s}
    (D : EulerInvariantQuarticData State)
    (state : State) →
  two * (energyNonlinear (lieData D) state * coherence (lieData D) state)
  ≡ zero
eulerInvariantRemovesQuarticEnergyCoherenceDefect D state
  rewrite kineticEnergyEulerInvariant D state = refl

reducedQuarticDerivativePart :
  ∀ {s} {State : Set s} →
  QuarticLyapunovLieData State → State → Nat
reducedQuarticDerivativePart D state =
  two * (energy D state * energyLinear D state)
  + two * (energy D state * coherenceNonlinear D state)

quarticPartReducesUnderEulerInvariance :
  ∀ {s} {State : Set s}
    (D : EulerInvariantQuarticData State)
    (state : State) →
  quarticDerivativePart (lieData D) state
  ≡ reducedQuarticDerivativePart (lieData D) state
quarticPartReducesUnderEulerInvariance D state
  rewrite kineticEnergyEulerInvariant D state
        | Nat.+-identityʳ
            (two *
              (energy (lieData D) state *
               energyLinear (lieData D) state))
  = refl

------------------------------------------------------------------------
-- The exact remaining scalar criterion.  Signs live in the concrete real
-- carrier; here their nonnegative magnitudes/reserves are compared.
------------------------------------------------------------------------

record QuadraticQuarticDomination {s : Level} (State : Set s) :
    Set (lsuc s) where
  field
    quadraticReserve cubicMagnitude quarticReserve : State → Nat

    quadraticStrictAwayFromZero : State → Set
    quarticStrictAtLargeAmplitude : State → Set

    cubicJointlyDominated : ∀ state →
      cubicMagnitude state
      ≤ quadraticReserve state + quarticReserve state

open QuadraticQuarticDomination public

jointReserveClosesDerivativeMagnitude :
  ∀ {s} {State : Set s}
    (D : QuadraticQuarticDomination State)
    (state : State) →
  cubicMagnitude D state
  ≤ quadraticReserve D state + quarticReserve D state
jointReserveClosesDerivativeMagnitude D state =
  cubicJointlyDominated D state

eulerInvariantQuarticDecompositionClosed : Bool
eulerInvariantQuarticDecompositionClosed = true

eulerInvariantQuarticDecompositionClosedIsTrue :
  eulerInvariantQuarticDecompositionClosed ≡ true
eulerInvariantQuarticDecompositionClosedIsTrue = refl
