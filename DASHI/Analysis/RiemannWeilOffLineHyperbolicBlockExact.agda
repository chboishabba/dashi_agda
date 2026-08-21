module DASHI.Analysis.RiemannWeilOffLineHyperbolicBlockExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Levent Alpöge and Ralph Furman,
-- "More than two thirds of the zeta zeros are simple and on the critical line",
-- arXiv:2608.13637 (2026), especially Proposition 4.1 and Lemma 3.1.
-- DOI: 10.48550/arXiv.2608.13637.
--
-- SOURCE-NATIVE SHAPE
--
-- For an off-line functional-equation pair {rho,1-conj(rho)}, write the
-- evaluation vector v_rho = a + i b.  The paired contribution is
--
--   m_rho (v v^T_bar + v_bar v^T)
--     = 2 m_rho (a a^T - b b^T),
--
-- a pull-back of the hyperbolic form
--
--   m_rho * diag(1,-1).
--
-- Hence the pre-pullback pair has one positive and one negative direction;
-- inertia under pull-back gives at most one positive direction per pair.
--
-- DASHI CONTRIBUTION / BOUNDARY
--
-- We encode the exact finite signature ledger and its consequence that the
-- positive-index BUDGET depends on pair count, not on transverse displacement.
-- We additionally prove a non-factorability theorem: the source signature
-- observer cannot determine the squared reflection defect, because two states
-- with the same signature have distinct defects.
--
-- We do not reprove Sylvester inertia for arbitrary Hermitian forms here and
-- do not identify a Nat defect with the analytic beta-1/2 displacement.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannReflectionOrbitDefectExact as Orbit

------------------------------------------------------------------------
-- Small equality combinators kept local so the no-factor theorem does not
-- depend on a larger algebraic import surface.
------------------------------------------------------------------------

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

------------------------------------------------------------------------
-- One source-native hyperbolic pair block.
------------------------------------------------------------------------

data HyperbolicDirection : Set where
  positiveDirection negativeDirection : HyperbolicDirection

record HyperbolicPairBlock : Set where
  constructor hyperbolicPairBlock
  field
    multiplicityPredecessor : Nat

open HyperbolicPairBlock public

multiplicity : HyperbolicPairBlock → Nat
multiplicity b = suc (multiplicityPredecessor b)

positiveIndexBeforePullback : HyperbolicPairBlock → Nat
positiveIndexBeforePullback b = 1

negativeIndexBeforePullback : HyperbolicPairBlock → Nat
negativeIndexBeforePullback b = 1

hyperbolicPairHasOnePositiveDirection :
  (b : HyperbolicPairBlock) → positiveIndexBeforePullback b ≡ 1
hyperbolicPairHasOnePositiveDirection b = refl

hyperbolicPairHasOneNegativeDirection :
  (b : HyperbolicPairBlock) → negativeIndexBeforePullback b ≡ 1
hyperbolicPairHasOneNegativeDirection b = refl

------------------------------------------------------------------------
-- Population-level inertia budget.
--
-- The paper's analytic Lemma 3.1 supplies the inequality after pull-back.
-- The exact finite combinatorics needed by that lemma is simply:
--
--   #off = pairCount + pairCount,
--   positive-index source budget = pairCount.
------------------------------------------------------------------------

sourcePositiveIndexBudget : Orbit.ReflectionPopulation → Nat
sourcePositiveIndexBudget p = Orbit.pairCount p

sourceNegativeIndexBudget : Orbit.ReflectionPopulation → Nat
sourceNegativeIndexBudget p = Orbit.pairCount p

offLineCountIsTwoSourcePositiveBudgets :
  (p : Orbit.ReflectionPopulation) →
  Orbit.nonFixedCount p
    ≡ sourcePositiveIndexBudget p + sourcePositiveIndexBudget p
offLineCountIsTwoSourcePositiveBudgets p = refl

sourcePositiveAndNegativeBudgetsEqual :
  (p : Orbit.ReflectionPopulation) →
  sourcePositiveIndexBudget p ≡ sourceNegativeIndexBudget p
sourcePositiveAndNegativeBudgetsEqual p = refl

------------------------------------------------------------------------
-- High-alpha obstruction: the source inertia ledger is displacement-blind.
--
-- Two reflection orbits with different squared defects are assigned the same
-- one-positive/one-negative source signature.  Thus a bound on a weighted
-- moment sum(alpha^2) cannot be read off from THIS signature count alone.
------------------------------------------------------------------------

nearOrbit : Orbit.CentredReflectionState
nearOrbit = Orbit.offLine Orbit.left 0

farOrbit : Orbit.CentredReflectionState
farOrbit = Orbit.offLine Orbit.right 2

nearOrbitDefectIsOne : Orbit.squaredDefect nearOrbit ≡ 1
nearOrbitDefectIsOne = refl

farOrbitDefectIsNine : Orbit.squaredDefect farOrbit ≡ 9
farOrbitDefectIsNine = refl

nearSourceBlock : HyperbolicPairBlock
nearSourceBlock = hyperbolicPairBlock 0

farSourceBlock : HyperbolicPairBlock
farSourceBlock = hyperbolicPairBlock 0

nearFarPositiveIndexBudgetsCollide :
  positiveIndexBeforePullback nearSourceBlock
    ≡ positiveIndexBeforePullback farSourceBlock
nearFarPositiveIndexBudgetsCollide = refl

nearFarNegativeIndexBudgetsCollide :
  negativeIndexBeforePullback nearSourceBlock
    ≡ negativeIndexBeforePullback farSourceBlock
nearFarNegativeIndexBudgetsCollide = refl

-- Coarse code for exactly the information retained by the bare fixed/pair
-- signature observer: centre versus non-fixed inverse pair.
sourceSignatureCode : Orbit.CentredReflectionState → Nat
sourceSignatureCode Orbit.criticalCentre = zero
sourceSignatureCode (Orbit.offLine _ _) = 1

nearFarSourceSignatureCollide :
  sourceSignatureCode nearOrbit ≡ sourceSignatureCode farOrbit
nearFarSourceSignatureCollide = refl

oneIsNotNine : 1 ≡ 9 → ⊥
oneIsNotNine ()

-- Stronger than a prose warning: no decoder from the bare source signature can
-- reconstruct squared displacement defect on all reflection states.
sourceSignatureCannotDetermineSquaredDefect :
  (decode : Nat → Nat) →
  ((x : Orbit.CentredReflectionState) →
    decode (sourceSignatureCode x) ≡ Orbit.squaredDefect x) →
  ⊥
sourceSignatureCannotDetermineSquaredDefect decode rec =
  oneIsNotNine
    (trans
      (sym nearOrbitDefectIsOne)
      (trans
        (sym (rec nearOrbit))
        (trans
          (rec farOrbit)
          farOrbitDefectIsNine)))

------------------------------------------------------------------------
-- Explicit next-frontier contract.
--
-- A distance-sensitive strengthening needs an additional analytic observable
-- beyond the bare hyperbolic signature count.  The record does not assert such
-- an observable exists for the current Weil compression; it states what must
-- be produced before a transverse-moment promotion is legitimate.
------------------------------------------------------------------------

record DistanceSensitiveOffLineAdapter : Set₁ where
  field
    AnalyticPair : Set
    reflectPair : AnalyticPair → AnalyticPair
    orbitState : AnalyticPair → Orbit.CentredReflectionState
    orbitStateIntertwinesReflection :
      (x : AnalyticPair) →
      orbitState (reflectPair x) ≡ Orbit.reflect (orbitState x)
    analyticDefectObservable : AnalyticPair → Nat
    analyticDefectIsOrbitSquaredDefect :
      (x : AnalyticPair) →
      analyticDefectObservable x ≡ Orbit.squaredDefect (orbitState x)

record WeilOffLineHyperbolicBoundary : Set where
  field
    sourceHyperbolicPairSignatureEncoded : Bool
    sourcePairCountBudgetEncoded : Bool
    displacementBlindnessWitnessConstructed : Bool
    signatureToDefectFactorizationRefuted : Bool
    arbitraryHermitianPullbackInertiaReprovedHere : Bool
    actualDistanceSensitiveWeilObservableConstructed : Bool
    weightedTransverseMomentBoundProved : Bool

weilOffLineHyperbolicBoundary : WeilOffLineHyperbolicBoundary
weilOffLineHyperbolicBoundary = record
  { sourceHyperbolicPairSignatureEncoded = true
  ; sourcePairCountBudgetEncoded = true
  ; displacementBlindnessWitnessConstructed = true
  ; signatureToDefectFactorizationRefuted = true
  ; arbitraryHermitianPullbackInertiaReprovedHere = false
  ; actualDistanceSensitiveWeilObservableConstructed = false
  ; weightedTransverseMomentBoundProved = false
  }
