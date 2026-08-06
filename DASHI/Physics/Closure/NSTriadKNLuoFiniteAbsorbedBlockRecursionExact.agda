module DASHI.Physics.Closure.NSTriadKNLuoFiniteAbsorbedBlockRecursionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Continue the finite hard-analysis chain past Section 4:
--
--   cutoff inequality
--     -> exact four-piece Schur majorant
--     -> small-gradient absorption
--     -> fixed-block recursion.
--
-- The final theorem proves
--
--   E_out + D <= r A_prev
--
-- from explicit boundary and weighted-energy comparisons and the scalar
-- inequality q + theta <= r.  Neither the absorbed cutoff inequality nor the
-- block recursion is taken as a primitive field.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteFourInteractionSchurBoundsExact as Four
import DASHI.Physics.Closure.NSTriadKNLuoFiniteCutoffSection4RecursionExact as Cutoff
import DASHI.Physics.Closure.NSTriadKNLuoFiniteSmallGradientAbsorptionExact as Absorb

record FiniteAbsorbedCutoffData : Set where
  constructor finite-absorbed-cutoff
  field
    cutoffData : Cutoff.FiniteCutoffSection4Data

    smallness absorptionCoefficient : ℚ
    absorptionCoefficientNonnegative :
      0ℚ ≤ absorptionCoefficient

    lowGradientBelowSmallness :
      Four.lowGradient
        (Cutoff.interactions cutoffData)
      ≤ smallness

    aggregateSmallnessBelowAbsorption :
      Four.section4AggregateConstant * smallness
      ≤ absorptionCoefficient

open FiniteAbsorbedCutoffData public

absorbedPhysicalSchurMajorant :
  (data : FiniteAbsorbedCutoffData) →
  Four.section4AggregateConstant
    * Four.section4CommonFactor
        (Cutoff.interactions (cutoffData data))
  ≤ absorptionCoefficient data
      * Four.weightedEnergy
          (Cutoff.interactions (cutoffData data))
absorbedPhysicalSchurMajorant data =
  Absorb.smallGradientAbsorption
    (Four.lowGradient
      (Cutoff.interactions (cutoffData data)))
    (Four.weightedEnergy
      (Cutoff.interactions (cutoffData data)))
    (smallness data)
    (absorptionCoefficient data)
    (Four.weightedEnergyNonnegative
      (Cutoff.interactions (cutoffData data)))
    (lowGradientBelowSmallness data)
    (aggregateSmallnessBelowAbsorption data)

finiteAbsorbedCutoffInequality :
  (data : FiniteAbsorbedCutoffData) →
  Cutoff.outputEnergy (cutoffData data)
    + Cutoff.dissipation (cutoffData data)
  ≤ Cutoff.boundaryEnergy (cutoffData data)
      + absorptionCoefficient data
          * Four.weightedEnergy
              (Cutoff.interactions (cutoffData data))
finiteAbsorbedCutoffInequality data =
  ℚₚ.≤-trans
    (Cutoff.finiteCutoffSection4Recursion
      (cutoffData data))
    (ℚₚ.+-mono-≤
      ℚₚ.≤-refl
      (absorbedPhysicalSchurMajorant data))

record FiniteBlockRecursionData : Set where
  constructor finite-block-recursion
  field
    absorbedCutoff : FiniteAbsorbedCutoffData

    predecessorMajorant boundaryCoefficient targetCoefficient : ℚ
    predecessorMajorantNonnegative :
      0ℚ ≤ predecessorMajorant

    boundaryEnergyBelowPredecessor :
      Cutoff.boundaryEnergy
        (cutoffData absorbedCutoff)
      ≤ boundaryCoefficient * predecessorMajorant

    weightedEnergyBelowPredecessor :
      Four.weightedEnergy
        (Cutoff.interactions (cutoffData absorbedCutoff))
      ≤ predecessorMajorant

    combinedCoefficientBelowTarget :
      boundaryCoefficient
        + absorptionCoefficient absorbedCutoff
      ≤ targetCoefficient

open FiniteBlockRecursionData public

finiteCombinedCoefficientRecursion :
  (data : FiniteBlockRecursionData) →
  Cutoff.outputEnergy
      (cutoffData (absorbedCutoff data))
    + Cutoff.dissipation
        (cutoffData (absorbedCutoff data))
  ≤ (boundaryCoefficient data
      + absorptionCoefficient (absorbedCutoff data))
      * predecessorMajorant data
finiteCombinedCoefficientRecursion data =
  let
    absorbed = absorbedCutoff data
    predecessor = predecessorMajorant data
    theta = absorptionCoefficient absorbed

    absorptionPartBelow :
      theta
        * Four.weightedEnergy
            (Cutoff.interactions (cutoffData absorbed))
      ≤ theta * predecessor
    absorptionPartBelow =
      let
        instance
          thetaIsNonnegative =
            nonNegative
              (absorptionCoefficientNonnegative absorbed)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        theta
        (weightedEnergyBelowPredecessor data)

    sumBelow :
      Cutoff.boundaryEnergy (cutoffData absorbed)
        + theta
            * Four.weightedEnergy
                (Cutoff.interactions (cutoffData absorbed))
      ≤ boundaryCoefficient data * predecessor
          + theta * predecessor
    sumBelow =
      ℚₚ.+-mono-≤
        (boundaryEnergyBelowPredecessor data)
        absorptionPartBelow

    factorPredecessor :
      boundaryCoefficient data * predecessor
        + theta * predecessor
      ≡ (boundaryCoefficient data + theta) * predecessor
    factorPredecessor =
      solve
        (boundaryCoefficient data
        ∷ theta
        ∷ predecessor
        ∷ [])

    toFactored :
      Cutoff.outputEnergy (cutoffData absorbed)
        + Cutoff.dissipation (cutoffData absorbed)
      ≤ (boundaryCoefficient data + theta) * predecessor
    toFactored =
      subst
        (λ upper →
          Cutoff.outputEnergy (cutoffData absorbed)
            + Cutoff.dissipation (cutoffData absorbed)
          ≤ upper)
        factorPredecessor
        (ℚₚ.≤-trans
          (finiteAbsorbedCutoffInequality absorbed)
          sumBelow)
  in
  toFactored

finiteTargetBlockRecursion :
  (data : FiniteBlockRecursionData) →
  Cutoff.outputEnergy
      (cutoffData (absorbedCutoff data))
    + Cutoff.dissipation
        (cutoffData (absorbedCutoff data))
  ≤ targetCoefficient data * predecessorMajorant data
finiteTargetBlockRecursion data =
  let
    targetScaling :
      (boundaryCoefficient data
        + absorptionCoefficient (absorbedCutoff data))
        * predecessorMajorant data
      ≤ targetCoefficient data * predecessorMajorant data
    targetScaling =
      let
        instance
          predecessorIsNonnegative =
            nonNegative (predecessorMajorantNonnegative data)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (predecessorMajorant data)
        (combinedCoefficientBelowTarget data)
  in
  ℚₚ.≤-trans
    (finiteCombinedCoefficientRecursion data)
    targetScaling

finiteAbsorbedCutoffChainClosed : Bool
finiteAbsorbedCutoffChainClosed = true

finiteTargetBlockRecursionClosed : Bool
finiteTargetBlockRecursionClosed = true

finiteAbsorbedCutoffChainClosedIsTrue :
  finiteAbsorbedCutoffChainClosed ≡ true
finiteAbsorbedCutoffChainClosedIsTrue = refl

finiteTargetBlockRecursionClosedIsTrue :
  finiteTargetBlockRecursionClosed ≡ true
finiteTargetBlockRecursionClosedIsTrue = refl
