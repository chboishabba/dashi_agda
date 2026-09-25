{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsWilsonContinuumClusteringRound551Exact where

------------------------------------------------------------------------
-- GOAL-1 B / ROUND551:
-- DIRECT WILSON WEXT -> SAME-FAMILY CONTINUUM HALF-RATE CLUSTERING
--
-- The source-correct B producer is R491, not the historical printed-J carrier.
-- R491 already gives, at every finite RG scale,
--
--   |Cov(W_L,W_R)| <= 1/4 * (1/2)^d(W_L,W_R).
--
-- To pass this to the continuum we need only:
--
--   * the SAME Wilson pair has a continuum correlation limit;
--   * Euclidean time translation has support distance = time;
--   * the scalar order is closed under that limit.
--
-- No printed-J = Wilson identification is reintroduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanWilsonTwoInsertionConnectedShellRound491Exact as WEXT
import DASHI.Physics.YangMills.BalabanCMP116TwoSourceConnectedClusteringRound274Exact as R274
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power

record WilsonContinuumClusteringInputs
    {Scale Volume Root State Observable : Set}
    (finite :
      WEXT.WilsonTwoInsertionConnectedShell
        Scale Volume Root State Observable)
    : Set₁ where
  field
    timeTranslate : Observable → Nat → Observable

    continuumConnectedCovarianceMagnitude :
      Observable → Observable → Nat → ℚ

    Converges : (Nat → ℚ) → ℚ → Set

    sameFamilyWilsonCorrelationConverges :
      ∀ left right time →
      Converges
        (λ cutoff →
          WEXT.connectedCovarianceMagnitude finite
            (WEXT.stateAtScale finite cutoff)
            left
            (timeTranslate right time))
        (continuumConnectedCovarianceMagnitude left right time)

    supportDistanceIsEuclideanTime :
      ∀ left right time →
      WEXT.physicalDistance finite left (timeTranslate right time)
      ≡ time

    orderClosedUnderContinuumLimit :
      ∀ sequence target upper →
      Converges sequence target →
      (∀ cutoff → sequence cutoff ≤ upper) →
      target ≤ upper

open WilsonContinuumClusteringInputs public

finiteWilsonHalfRateBound :
  ∀ {Scale Volume Root State Observable}
    {finite :
      WEXT.WilsonTwoInsertionConnectedShell
        Scale Volume Root State Observable}
    (inputs : WilsonContinuumClusteringInputs finite)
    cutoff left right time →
  WEXT.connectedCovarianceMagnitude finite
    (WEXT.stateAtScale finite cutoff)
    left
    (timeTranslate inputs right time)
  ≤
  Shell.quarter * Power.rationalPower Geo.half time
finiteWilsonHalfRateBound {finite = finite} inputs cutoff left right time =
  let
    geometric =
      R274.connectedCovarianceGeometricBound
        (WEXT.asR274TwoSourceConnectedRootedShellData finite)
        (WEXT.stateAtScale finite cutoff)
        left
        (timeTranslate inputs right time)
  in
  subst
    (λ distance →
      WEXT.connectedCovarianceMagnitude finite
        (WEXT.stateAtScale finite cutoff)
        left
        (timeTranslate inputs right time)
      ≤
      Shell.quarter * Power.rationalPower Geo.half distance)
    (supportDistanceIsEuclideanTime inputs left right time)
    geometric
  where
  open import Relation.Binary.PropositionalEquality using (subst)

continuumWilsonHalfRateBound :
  ∀ {Scale Volume Root State Observable}
    {finite :
      WEXT.WilsonTwoInsertionConnectedShell
        Scale Volume Root State Observable}
    (inputs : WilsonContinuumClusteringInputs finite)
    left right time →
  continuumConnectedCovarianceMagnitude inputs left right time
  ≤
  Shell.quarter * Power.rationalPower Geo.half time
continuumWilsonHalfRateBound {finite = finite} inputs left right time =
  orderClosedUnderContinuumLimit inputs
    (λ cutoff →
      WEXT.connectedCovarianceMagnitude finite
        (WEXT.stateAtScale finite cutoff)
        left
        (timeTranslate inputs right time))
    (continuumConnectedCovarianceMagnitude inputs left right time)
    (Shell.quarter * Power.rationalPower Geo.half time)
    (sameFamilyWilsonCorrelationConverges inputs left right time)
    (λ cutoff →
      finiteWilsonHalfRateBound inputs cutoff left right time)

round551FiniteWEXTToHalfRateCompilerLevel : ProofLevel
round551FiniteWEXTToHalfRateCompilerLevel =
  WEXT.round491R274CompilerReuseLevel

round551ContinuumOrderClosureCompilerLevel : ProofLevel
round551ContinuumOrderClosureCompilerLevel = machineChecked

literalRound551SameFamilyWilsonCorrelationConvergenceLevel : ProofLevel
literalRound551SameFamilyWilsonCorrelationConvergenceLevel = conditional

literalRound551WilsonTimeDistanceMeaningLevel : ProofLevel
literalRound551WilsonTimeDistanceMeaningLevel = conditional

printedJPresentationRequired : Bool
printedJPresentationRequired = false
