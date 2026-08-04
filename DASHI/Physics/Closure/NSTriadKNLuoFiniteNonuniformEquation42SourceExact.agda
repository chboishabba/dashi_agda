module DASHI.Physics.Closure.NSTriadKNLuoFiniteNonuniformEquation42SourceExact where

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
-- Give the finite nonuniform-time analogue of Luo equation (4.2) an exact
-- source decomposition.  Starting from the step inequality
--
--   E_{n+1}-E_n + h_n D_n <= h_n Pi_n
--
-- and a proved identity Pi_n=J1_n+J2_n, this module derives the integrated
-- cutoff inequality with the right-hand side split into the two weighted
-- source folds.  Neither the integrated inequality nor the J1/J2 sum is a
-- primitive field.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _-_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Sum
import DASHI.Physics.Closure.NSTriadKNLuoDiscreteCutoffEnergyExact as Cutoff
import DASHI.Physics.Closure.NSTriadKNLuoFiniteNonuniformCutoffEnergyExact as Nonuniform

record NonuniformEquation42SourceData : Set₁ where
  field
    cutoffEnergy : Nonuniform.NonuniformCutoffEnergyData
    J1 J2 : Nat → ℚ

    fluxMeaning :
      (step : Nat) →
      Nonuniform.flux cutoffEnergy step ≡ J1 step + J2 step

open NonuniformEquation42SourceData public

sourceResolvedCutoffData :
  NonuniformEquation42SourceData →
  Nonuniform.NonuniformCutoffEnergyData
sourceResolvedCutoffData data = record
  { energy = Nonuniform.energy (cutoffEnergy data)
  ; dissipation = Nonuniform.dissipation (cutoffEnergy data)
  ; flux = λ step → J1 data step + J2 data step
  ; cutoff = Nonuniform.cutoff (cutoffEnergy data)
  ; stepLength = Nonuniform.stepLength (cutoffEnergy data)
  ; lastStep = Nonuniform.lastStep (cutoffEnergy data)
  ; cutoffNonnegative =
      Nonuniform.cutoffNonnegative (cutoffEnergy data)
  ; stepLengthNonnegative =
      Nonuniform.stepLengthNonnegative (cutoffEnergy data)
  ; nonuniformStepEnergyInequality = λ step →
      subst
        (λ right →
          Cutoff.energyIncrement
              (Nonuniform.energy (cutoffEnergy data)) step
            + Nonuniform.stepLength (cutoffEnergy data) step
              * Nonuniform.dissipation (cutoffEnergy data) step
          ≤ right)
        (cong
          (Nonuniform.stepLength (cutoffEnergy data) step *_)
          (fluxMeaning data step))
        (Nonuniform.nonuniformStepEnergyInequality
          (cutoffEnergy data) step)
  }

sourceWeight : NonuniformEquation42SourceData → Nat → ℚ
sourceWeight data step =
  Nonuniform.cutoff (cutoffEnergy data) step
  * Nonuniform.stepLength (cutoffEnergy data) step

weightedJ1 : NonuniformEquation42SourceData → ℚ
weightedJ1 data =
  Sum.sumTo
    (λ step → sourceWeight data step * J1 data step)
    (Nonuniform.lastStep (cutoffEnergy data))

weightedJ2 : NonuniformEquation42SourceData → ℚ
weightedJ2 data =
  Sum.sumTo
    (λ step → sourceWeight data step * J2 data step)
    (Nonuniform.lastStep (cutoffEnergy data))

associatedWeightedFlux : NonuniformEquation42SourceData → ℚ
associatedWeightedFlux data =
  Sum.sumTo
    (λ step → sourceWeight data step * (J1 data step + J2 data step))
    (Nonuniform.lastStep (cutoffEnergy data))

sumToCong :
  (left right : Nat → ℚ) →
  (cutoff : Nat) →
  ((step : Nat) → left step ≡ right step) →
  Sum.sumTo left cutoff ≡ Sum.sumTo right cutoff
sumToCong left right zero pointwise = pointwise zero
sumToCong left right (suc cutoff) pointwise
  rewrite pointwise (suc cutoff)
        | sumToCong left right cutoff pointwise = refl

weightedFluxAssociation :
  (data : NonuniformEquation42SourceData) →
  Nonuniform.nonuniformWeightedFlux (sourceResolvedCutoffData data)
  ≡ associatedWeightedFlux data
weightedFluxAssociation data =
  sumToCong
    (λ step →
      Nonuniform.cutoff (cutoffEnergy data) step
      * (Nonuniform.stepLength (cutoffEnergy data) step
        * (J1 data step + J2 data step)))
    (λ step → sourceWeight data step * (J1 data step + J2 data step))
    (Nonuniform.lastStep (cutoffEnergy data))
    (λ step →
      solve
        ( Nonuniform.cutoff (cutoffEnergy data) step
        ∷ Nonuniform.stepLength (cutoffEnergy data) step
        ∷ J1 data step
        ∷ J2 data step
        ∷ []
        ))

sourceResolvedWeightedFluxSplit :
  (data : NonuniformEquation42SourceData) →
  Nonuniform.nonuniformWeightedFlux (sourceResolvedCutoffData data)
  ≡ weightedJ1 data + weightedJ2 data
sourceResolvedWeightedFluxSplit data =
  trans
    (weightedFluxAssociation data)
    (Cutoff.sumWeightedAdditiveSplit
      (sourceWeight data)
      (J1 data)
      (J2 data)
      (Nonuniform.lastStep (cutoffEnergy data)))

finiteNonuniformEquation42SourceBound :
  (data : NonuniformEquation42SourceData) →
  Nonuniform.cutoff (cutoffEnergy data)
      (Nonuniform.lastStep (cutoffEnergy data))
      * Nonuniform.energy (cutoffEnergy data)
          (suc (Nonuniform.lastStep (cutoffEnergy data)))
    - Nonuniform.cutoff (cutoffEnergy data) zero
        * Nonuniform.energy (cutoffEnergy data) zero
    - Cutoff.cutoffDifferenceError
        (Nonuniform.cutoff (cutoffEnergy data))
        (Nonuniform.energy (cutoffEnergy data))
        (Nonuniform.lastStep (cutoffEnergy data))
    + Nonuniform.nonuniformWeightedDissipation
        (sourceResolvedCutoffData data)
  ≤ weightedJ1 data + weightedJ2 data
finiteNonuniformEquation42SourceBound data =
  subst
    (λ right →
      Nonuniform.cutoff (cutoffEnergy data)
          (Nonuniform.lastStep (cutoffEnergy data))
          * Nonuniform.energy (cutoffEnergy data)
              (suc (Nonuniform.lastStep (cutoffEnergy data)))
        - Nonuniform.cutoff (cutoffEnergy data) zero
            * Nonuniform.energy (cutoffEnergy data) zero
        - Cutoff.cutoffDifferenceError
            (Nonuniform.cutoff (cutoffEnergy data))
            (Nonuniform.energy (cutoffEnergy data))
            (Nonuniform.lastStep (cutoffEnergy data))
        + Nonuniform.nonuniformWeightedDissipation
            (sourceResolvedCutoffData data)
      ≤ right)
    (sourceResolvedWeightedFluxSplit data)
    (Nonuniform.finiteNonuniformIntegratedCutoffEnergy
      (sourceResolvedCutoffData data))

finiteNonuniformEquation42SourceClosed : Bool
finiteNonuniformEquation42SourceClosed = true

finiteNonuniformEquation42SourceClosedIsTrue :
  finiteNonuniformEquation42SourceClosed ≡ true
finiteNonuniformEquation42SourceClosedIsTrue = refl
