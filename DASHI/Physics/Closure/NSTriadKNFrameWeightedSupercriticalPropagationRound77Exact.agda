module DASHI.Physics.Closure.NSTriadKNFrameWeightedSupercriticalPropagationRound77Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- DOI: 10.1063/1.858309.
-- Uses: source guidance for where amplifying helical triads may be found.
-- No statistical transfer claim is promoted to a deterministic inequality.
--
-- Authors: Jindrich Necas; Michael Ruzicka; Vladimir Sverak.
-- Title: "On Leray's self-similar solutions of the Navier-Stokes equations".
-- DOI: 10.1007/BF02551584.
--
-- Author: Tai-Peng Tsai.
-- Title: "On Leray's self-similar solutions of the Navier-Stokes equations
-- satisfying local energy estimates".
-- DOI: 10.1007/s002050050099.
-- Uses: rigidity calibration at the exactly self-similar boundary only.
-- Their Liouville theorems do NOT imply positive excess for the finite DASHI
-- propagation tree.
--
-- ROUND77 / C2+D2 FUSION
--
-- Round75 used unweighted squared floor mass mu^2 and therefore the threshold
--
--   sum_i r_i^2 > 1.
--
-- Round77's periodic-scaling audit shows that the literal fixed-output frame
-- product B_e should not be set to one by an ad-hoc dyadic zoom.  If rho_e is
-- the explicit reciprocal frame weight, the charge-admissible floor is
--
--   floor_e = rho_e mu_e^2.
--
-- For children satisfying mu_i >= r_i mu_e, the exact guaranteed child floor
-- factors as
--
--   sum_i rho_i (r_i mu_e)^2
--     = mu_e^2 sum_i rho_i r_i^2.
--
-- Hence the physically correct supercritical threshold is
--
--   sum_i rho_i r_i^2 = rho_e + epsilon_e,
--
-- and exact one-step growth is
--
--   guaranteedChildMass
--     = parentMass + mu_e^2 epsilon_e.
--
-- This is the scale-aware replacement for D2.  It is division-free and uses
-- the same reciprocal weight that turns Round75's Q*B estimate into an
-- admissible Q-funded floor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

------------------------------------------------------------------------
-- One physical child, indexed by the parent amplitude whose amplification
-- lower bound it consumes.
------------------------------------------------------------------------

record FrameWeightedChild (parentAmplitude : ℚ) : Set where
  constructor weighted-child
  field
    ratio : ℚ
    childWeight : ℚ
    childAmplitude : ℚ
    ratioNonnegative : 0ℚ ≤ ratio
    childWeightNonnegative : 0ℚ ≤ childWeight
    childAmplitudeNonnegative : 0ℚ ≤ childAmplitude
    amplificationLowerBound : ratio * parentAmplitude ≤ childAmplitude

open FrameWeightedChild public

weightedRatioAtom : ∀ {parentAmplitude} → FrameWeightedChild parentAmplitude → ℚ
weightedRatioAtom child = childWeight child * L2.square (ratio child)

guaranteedChildFloor :
  ∀ {parentAmplitude} → FrameWeightedChild parentAmplitude → ℚ
guaranteedChildFloor {parentAmplitude} child =
  childWeight child * L2.square (ratio child * parentAmplitude)

actualChildFloor :
  ∀ {parentAmplitude} → FrameWeightedChild parentAmplitude → ℚ
actualChildFloor child = childWeight child * L2.square (childAmplitude child)

sumWeightedRatios :
  ∀ {parentAmplitude} → List (FrameWeightedChild parentAmplitude) → ℚ
sumWeightedRatios [] = 0ℚ
sumWeightedRatios (child ∷ rest) =
  weightedRatioAtom child + sumWeightedRatios rest

sumGuaranteedChildFloors :
  ∀ {parentAmplitude} → List (FrameWeightedChild parentAmplitude) → ℚ
sumGuaranteedChildFloors [] = 0ℚ
sumGuaranteedChildFloors (child ∷ rest) =
  guaranteedChildFloor child + sumGuaranteedChildFloors rest

sumActualChildFloors :
  ∀ {parentAmplitude} → List (FrameWeightedChild parentAmplitude) → ℚ
sumActualChildFloors [] = 0ℚ
sumActualChildFloors (child ∷ rest) =
  actualChildFloor child + sumActualChildFloors rest

------------------------------------------------------------------------
-- Literal amplification lower bounds imply the guaranteed frame-weighted
-- floor is below the actual child floor.
------------------------------------------------------------------------

guaranteedChildFloorBelowActual :
  ∀ {parentAmplitude}
    (parentNN : 0ℚ ≤ parentAmplitude)
    (child : FrameWeightedChild parentAmplitude) →
  guaranteedChildFloor child ≤ actualChildFloor child
guaranteedChildFloorBelowActual {parentAmplitude} parentNN child =
  let
    scaledNN : 0ℚ ≤ ratio child * parentAmplitude
    scaledNN = ℚP.0≤*0≤ (ratioNonnegative child) parentNN

    squareBound :
      L2.square (ratio child * parentAmplitude)
      ≤ L2.square (childAmplitude child)
    squareBound =
      L2.nonnegativeProductMonotone
        scaledNN scaledNN
        (childAmplitudeNonnegative child) (childAmplitudeNonnegative child)
        (amplificationLowerBound child) (amplificationLowerBound child)

    guaranteedNN = L2.squareNonnegative (ratio child * parentAmplitude)
    actualNN = L2.squareNonnegative (childAmplitude child)
  in
  L2.nonnegativeProductMonotone
    (childWeightNonnegative child) guaranteedNN
    (childWeightNonnegative child) actualNN
    ℚP.≤-refl squareBound

sumGuaranteedBelowActual :
  ∀ {parentAmplitude}
    (parentNN : 0ℚ ≤ parentAmplitude)
    (children : List (FrameWeightedChild parentAmplitude)) →
  sumGuaranteedChildFloors children ≤ sumActualChildFloors children
sumGuaranteedBelowActual parentNN [] = ℚP.≤-refl
sumGuaranteedBelowActual parentNN (child ∷ rest) =
  ℚP.+-mono-≤
    (guaranteedChildFloorBelowActual parentNN child)
    (sumGuaranteedBelowActual parentNN rest)

------------------------------------------------------------------------
-- Exact factorisation of the whole guaranteed child antichain.
------------------------------------------------------------------------

sumGuaranteedFactorsThroughParentSquare :
  ∀ {parentAmplitude}
    (children : List (FrameWeightedChild parentAmplitude)) →
  sumGuaranteedChildFloors children
  ≡ L2.square parentAmplitude * sumWeightedRatios children
sumGuaranteedFactorsThroughParentSquare [] = solve []
sumGuaranteedFactorsThroughParentSquare {parentAmplitude} (child ∷ rest) =
  trans
    (cong (guaranteedChildFloor child +_)
      (sumGuaranteedFactorsThroughParentSquare rest))
    (solve
      ( childWeight child
      ∷ ratio child
      ∷ parentAmplitude
      ∷ sumWeightedRatios rest
      ∷ []))

weightedParentMass : ℚ → ℚ → ℚ
weightedParentMass parentWeight parentAmplitude =
  parentWeight * L2.square parentAmplitude

record FrameWeightedSupercriticalRow : Set where
  constructor weighted-supercritical-row
  field
    parentAmplitude : ℚ
    parentWeight : ℚ
    children : List (FrameWeightedChild parentAmplitude)
    excess : ℚ
    parentAmplitudeNonnegative : 0ℚ ≤ parentAmplitude
    parentWeightNonnegative : 0ℚ ≤ parentWeight
    excessPositive : 0ℚ < excess
    weightedSupercriticalExact :
      sumWeightedRatios children ≡ parentWeight + excess

open FrameWeightedSupercriticalRow public

weightedSupercriticalGuaranteedGrowthExact :
  ∀ row →
  sumGuaranteedChildFloors (children row)
  ≡ weightedParentMass (parentWeight row) (parentAmplitude row)
      + L2.square (parentAmplitude row) * excess row
weightedSupercriticalGuaranteedGrowthExact row =
  trans
    (sumGuaranteedFactorsThroughParentSquare (children row))
    (trans
      (cong (L2.square (parentAmplitude row) *_)
        (weightedSupercriticalExact row))
      (solve
        ( L2.square (parentAmplitude row)
        ∷ parentWeight row
        ∷ excess row
        ∷ [])))

weightedSupercriticalActualChildrenDominateGuaranteed :
  ∀ row →
  sumGuaranteedChildFloors (children row)
  ≤ sumActualChildFloors (children row)
weightedSupercriticalActualChildrenDominateGuaranteed row =
  sumGuaranteedBelowActual
    (parentAmplitudeNonnegative row)
    (children row)

------------------------------------------------------------------------
-- Exact critical boundary.  The old unweighted condition sum r_i^2 = 1 is
-- recovered only when every child and parent reciprocal frame weight is the
-- same.  With varying physical frame products, the weighted sum is the invariant
-- consumed by the charge ledger.
------------------------------------------------------------------------

record FrameWeightedCriticalRow : Set where
  constructor weighted-critical-row
  field
    criticalParentAmplitude : ℚ
    criticalParentWeight : ℚ
    criticalChildren : List (FrameWeightedChild criticalParentAmplitude)
    weightedCriticalExact :
      sumWeightedRatios criticalChildren ≡ criticalParentWeight

open FrameWeightedCriticalRow public

weightedCriticalGuaranteedMassPreserved :
  ∀ row →
  sumGuaranteedChildFloors (criticalChildren row)
  ≡ weightedParentMass
      (criticalParentWeight row)
      (criticalParentAmplitude row)
weightedCriticalGuaranteedMassPreserved row =
  trans
    (sumGuaranteedFactorsThroughParentSquare (criticalChildren row))
    (trans
      (cong (L2.square (criticalParentAmplitude row) *_)
        (weightedCriticalExact row))
      (solve
        ( L2.square (criticalParentAmplitude row)
        ∷ criticalParentWeight row
        ∷ [])))

round77CorrectD2ThresholdIsFrameWeighted : Bool
round77CorrectD2ThresholdIsFrameWeighted = true

round77UnitNormalizationNeededForD2 : Bool
round77UnitNormalizationNeededForD2 = false

round77FrameWeightedOneStepGrowthCompilerConstructed : Bool
round77FrameWeightedOneStepGrowthCompilerConstructed = true

round77PhysicalNSChildrenSatisfyWeightedSupercriticality : Bool
round77PhysicalNSChildrenSatisfyWeightedSupercriticality = false

round77NRSOrTsaiImpliesPositiveWeightedExcess : Bool
round77NRSOrTsaiImpliesPositiveWeightedExcess = false

round77WaleffeClassificationImpliesPointwiseWeightedExcess : Bool
round77WaleffeClassificationImpliesPointwiseWeightedExcess = false

round77CorrectD2ThresholdIsFrameWeightedIsTrue :
  round77CorrectD2ThresholdIsFrameWeighted ≡ true
round77CorrectD2ThresholdIsFrameWeightedIsTrue = refl

round77NRSOrTsaiImpliesPositiveWeightedExcessIsFalse :
  round77NRSOrTsaiImpliesPositiveWeightedExcess ≡ false
round77NRSOrTsaiImpliesPositiveWeightedExcessIsFalse = refl
