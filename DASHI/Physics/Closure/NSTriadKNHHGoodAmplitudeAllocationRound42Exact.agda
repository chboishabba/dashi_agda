module DASHI.Physics.Closure.NSTriadKNHHGoodAmplitudeAllocationRound42Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- Indiana University Mathematics Journal 42 (1993), 775--789.
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Round 41 proved that the tempting uniform shortcut
--
--   W <= C X D
--
-- cannot hold for the literal HH-good weight
--
--   W(a,b) = a^2 b^4,
--
-- because W is degree six under common amplitude scaling whereas X D is
-- degree four.  This file performs the scale-compatible repair at the literal
-- monomial level rather than hiding it in interpolation.
--
-- There are exactly two natural ways to spend one quadratic data-energy
-- factor:
--
--   left-energy allocation:   a^2 b^4 = a^2 (b^2 b^2),
--   right-energy allocation:  a^2 b^4 = b^2 (a^2 b^2).
--
-- A physical proof may choose whichever leg is actually controlled by the
-- global/data energy E0.  The remaining quartic core must then be identified
-- with the critical*dissipation resource.  The finite weighted theorem proves
-- exactly
--
--   sum k_i W_i <= E0 * sum k_i Q_i
--
-- and hence, if
--
--   sum k_i Q_i <= X D,
--
-- then
--
--   sum k_i W_i <= E0 X D.
--
-- This is the missing amplitude-allocation algebra required by the Round-41
-- Young owner.  The only remaining physical theorem is the same-object
-- identification of one selected quadratic leg with E0 and of the residual
-- quartic core with the actual critical/dissipation product.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalDirectionalDefectExact as Physical
import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHGoodPhysicalThresholdStretchingRound38Exact as Stretch
import DASHI.Physics.Closure.NSTriadKNHHGoodFiniteKernelCauchyRound40Exact as Good
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner

data DataEnergyLeg : Set where
  leftEnergyLeg rightEnergyLeg : DataEnergyLeg

allocatedEnergySquare :
  DataEnergyLeg → Physical.PhysicalVorticityPair → ℚ
allocatedEnergySquare leftEnergyLeg pair =
  L2.square (Physical.leftAmplitude pair)
allocatedEnergySquare rightEnergyLeg pair =
  L2.square (Physical.rightAmplitude pair)

criticalQuarticCore :
  DataEnergyLeg → Physical.PhysicalVorticityPair → ℚ
criticalQuarticCore leftEnergyLeg pair =
  L2.square (Physical.rightAmplitude pair)
    * L2.square (Physical.rightAmplitude pair)
criticalQuarticCore rightEnergyLeg pair =
  L2.square (Physical.leftAmplitude pair)
    * L2.square (Physical.rightAmplitude pair)

allocatedEnergySquareNonnegative :
  ∀ leg pair → 0ℚ ≤ allocatedEnergySquare leg pair
allocatedEnergySquareNonnegative leftEnergyLeg pair =
  L2.squareNonnegative (Physical.leftAmplitude pair)
allocatedEnergySquareNonnegative rightEnergyLeg pair =
  L2.squareNonnegative (Physical.rightAmplitude pair)

criticalQuarticCoreNonnegative :
  ∀ leg pair → 0ℚ ≤ criticalQuarticCore leg pair
criticalQuarticCoreNonnegative leftEnergyLeg pair =
  let
    squareNN = L2.squareNonnegative (Physical.rightAmplitude pair)
    instance
      leftNN = nonNegative squareNN
      rightNN = nonNegative squareNN
      productNN = ℚP.nonNeg*nonNeg⇒nonNeg
        (L2.square (Physical.rightAmplitude pair))
        (L2.square (Physical.rightAmplitude pair))
  in
  ℚP.nonNegative⁻¹ (criticalQuarticCore leftEnergyLeg pair)
criticalQuarticCoreNonnegative rightEnergyLeg pair =
  let
    leftNN0 = L2.squareNonnegative (Physical.leftAmplitude pair)
    rightNN0 = L2.squareNonnegative (Physical.rightAmplitude pair)
    instance
      leftNN = nonNegative leftNN0
      rightNN = nonNegative rightNN0
      productNN = ℚP.nonNeg*nonNeg⇒nonNeg
        (L2.square (Physical.leftAmplitude pair))
        (L2.square (Physical.rightAmplitude pair))
  in
  ℚP.nonNegative⁻¹ (criticalQuarticCore rightEnergyLeg pair)

literalAmplitudeWeightAllocation :
  ∀ leg pair →
  Stretch.amplitudeQuarticWeight pair
  ≡ allocatedEnergySquare leg pair * criticalQuarticCore leg pair
literalAmplitudeWeightAllocation leftEnergyLeg pair =
  solve
    ( L2.square (Physical.leftAmplitude pair)
    ∷ L2.square (Physical.rightAmplitude pair)
    ∷ [])
literalAmplitudeWeightAllocation rightEnergyLeg pair =
  solve
    ( L2.square (Physical.leftAmplitude pair)
    ∷ L2.square (Physical.rightAmplitude pair)
    ∷ [])

record HHGoodAmplitudeAllocation
    (parameter : Threshold.PositiveThreshold) : Set where
  field
    selectedEnergyLeg : DataEnergyLeg
    dataEnergyFactor : ℚ
    dataEnergyFactorNonnegative : 0ℚ ≤ dataEnergyFactor

    pairOf : Good.HHGoodKernelSample parameter →
      Physical.PhysicalVorticityPair

    localWeightIsLiteralPhysicalWeight :
      (sample : Good.HHGoodKernelSample parameter) →
      Good.localWeight sample
      ≡ Stretch.amplitudeQuarticWeight (pairOf sample)

    selectedEnergySquareBelowDataEnergy :
      (sample : Good.HHGoodKernelSample parameter) →
      allocatedEnergySquare selectedEnergyLeg (pairOf sample)
      ≤ dataEnergyFactor

open HHGoodAmplitudeAllocation public

sampleCriticalQuarticCore :
  ∀ {parameter} →
  HHGoodAmplitudeAllocation parameter →
  Good.HHGoodKernelSample parameter → ℚ
sampleCriticalQuarticCore allocation sample =
  criticalQuarticCore
    (selectedEnergyLeg allocation)
    (pairOf allocation sample)

sampleLocalWeightBelowDataEnergyQuarticCore :
  ∀ {parameter}
    (allocation : HHGoodAmplitudeAllocation parameter)
    (sample : Good.HHGoodKernelSample parameter) →
  Good.localWeight sample
  ≤ dataEnergyFactor allocation
      * sampleCriticalQuarticCore allocation sample
sampleLocalWeightBelowDataEnergyQuarticCore allocation sample =
  let
    leg = selectedEnergyLeg allocation
    pair = pairOf allocation sample
    energySquare = allocatedEnergySquare leg pair
    core = criticalQuarticCore leg pair

    coreNN = criticalQuarticCoreNonnegative leg pair

    scaled : energySquare * core ≤ dataEnergyFactor allocation * core
    scaled =
      let instance coreNNI = nonNegative coreNN
      in ℚP.*-monoʳ-≤-nonNeg core
        (selectedEnergySquareBelowDataEnergy allocation sample)

    physicalBound :
      Stretch.amplitudeQuarticWeight pair
      ≤ dataEnergyFactor allocation * core
    physicalBound =
      subst
        (λ lower → lower ≤ dataEnergyFactor allocation * core)
        (sym (literalAmplitudeWeightAllocation leg pair))
        scaled
  in
  subst
    (λ lower →
      lower ≤ dataEnergyFactor allocation
        * sampleCriticalQuarticCore allocation sample)
    (sym (localWeightIsLiteralPhysicalWeight allocation sample))
    physicalBound

weightedQuarticCore :
  ∀ {parameter} →
  HHGoodAmplitudeAllocation parameter →
  List (Good.HHGoodKernelSample parameter) → ℚ
weightedQuarticCore allocation [] = 0ℚ
weightedQuarticCore allocation (sample ∷ rest) =
  Good.kernelMagnitude sample * sampleCriticalQuarticCore allocation sample
  + weightedQuarticCore allocation rest

weightedQuarticCoreNonnegative :
  ∀ {parameter}
    (allocation : HHGoodAmplitudeAllocation parameter)
    (samples : List (Good.HHGoodKernelSample parameter)) →
  0ℚ ≤ weightedQuarticCore allocation samples
weightedQuarticCoreNonnegative allocation [] = ℚP.≤-refl
weightedQuarticCoreNonnegative allocation (sample ∷ rest) =
  let
    coreNN = criticalQuarticCoreNonnegative
      (selectedEnergyLeg allocation)
      (pairOf allocation sample)
    productNN :
      0ℚ ≤ Good.kernelMagnitude sample
        * sampleCriticalQuarticCore allocation sample
    productNN =
      let
        instance
          kernelNN = nonNegative (Good.kernelMagnitudeNonnegative sample)
          coreNNI = nonNegative coreNN
          resultNN = ℚP.nonNeg*nonNeg⇒nonNeg
            (Good.kernelMagnitude sample)
            (sampleCriticalQuarticCore allocation sample)
      in
      ℚP.nonNegative⁻¹
        (Good.kernelMagnitude sample
          * sampleCriticalQuarticCore allocation sample)
  in
  L2.addNonnegative productNN
    (weightedQuarticCoreNonnegative allocation rest)

weightedLocalMassBelowDataEnergyQuarticCore :
  ∀ {parameter}
    (allocation : HHGoodAmplitudeAllocation parameter)
    (samples : List (Good.HHGoodKernelSample parameter)) →
  Good.weightedLocalMass samples
  ≤ dataEnergyFactor allocation * weightedQuarticCore allocation samples
weightedLocalMassBelowDataEnergyQuarticCore allocation [] =
  subst
    (λ upper → 0ℚ ≤ upper)
    (solve (dataEnergyFactor allocation ∷ []))
    ℚP.≤-refl
weightedLocalMassBelowDataEnergyQuarticCore allocation (sample ∷ rest) =
  let
    sampleBound = sampleLocalWeightBelowDataEnergyQuarticCore allocation sample

    localScaled :
      Good.kernelMagnitude sample * Good.localWeight sample
      ≤ Good.kernelMagnitude sample
          * (dataEnergyFactor allocation
              * sampleCriticalQuarticCore allocation sample)
    localScaled =
      let instance
        kernelNN = nonNegative (Good.kernelMagnitudeNonnegative sample)
      in
      ℚP.*-monoˡ-≤-nonNeg (Good.kernelMagnitude sample) sampleBound

    restBound = weightedLocalMassBelowDataEnergyQuarticCore allocation rest
    added = ℚP.+-mono-≤ localScaled restBound

    rightMeaning :
      Good.kernelMagnitude sample
          * (dataEnergyFactor allocation
              * sampleCriticalQuarticCore allocation sample)
      + dataEnergyFactor allocation * weightedQuarticCore allocation rest
      ≡ dataEnergyFactor allocation
          * weightedQuarticCore allocation (sample ∷ rest)
    rightMeaning =
      solve
        ( Good.kernelMagnitude sample
        ∷ dataEnergyFactor allocation
        ∷ sampleCriticalQuarticCore allocation sample
        ∷ weightedQuarticCore allocation rest
        ∷ [])
  in
  subst
    (λ upper → Good.weightedLocalMass (sample ∷ rest) ≤ upper)
    rightMeaning
    added

record HHGoodCriticalDissipationAllocation
    (environment : Owner.TaxEnvironment)
    (parameter : Threshold.PositiveThreshold)
    (samples : List (Good.HHGoodKernelSample parameter)) : Set where
  field
    amplitudeAllocation : HHGoodAmplitudeAllocation parameter
    criticalNonnegative : 0ℚ ≤ Owner.integralCritical environment
    dissipationNonnegative : 0ℚ ≤ Owner.dissipation environment
    quarticCoreBelowCriticalDissipation :
      weightedQuarticCore amplitudeAllocation samples
      ≤ Owner.integralCritical environment
          * Owner.dissipation environment

open HHGoodCriticalDissipationAllocation public

physicalHHGoodDataEnergyFactorization :
  ∀ {environment parameter samples} →
  (allocation : HHGoodCriticalDissipationAllocation
    environment parameter samples) →
  Good.weightedLocalMass samples
  ≤ dataEnergyFactor (amplitudeAllocation allocation)
      * Owner.integralCritical environment
      * Owner.dissipation environment
physicalHHGoodDataEnergyFactorization {environment} {samples = samples} allocation =
  let
    amplitude = amplitudeAllocation allocation
    E0 = dataEnergyFactor amplitude
    first = weightedLocalMassBelowDataEnergyQuarticCore amplitude samples

    scaled :
      E0 * weightedQuarticCore amplitude samples
      ≤ E0 *
          (Owner.integralCritical environment
            * Owner.dissipation environment)
    scaled =
      let instance E0NN = nonNegative (dataEnergyFactorNonnegative amplitude)
      in ℚP.*-monoˡ-≤-nonNeg E0
        (quarticCoreBelowCriticalDissipation allocation)

    normalized :
      E0 *
        (Owner.integralCritical environment
          * Owner.dissipation environment)
      ≡ E0 * Owner.integralCritical environment
          * Owner.dissipation environment
    normalized = solve
      ( E0
      ∷ Owner.integralCritical environment
      ∷ Owner.dissipation environment
      ∷ [])
  in
  ℚP.≤-trans first
    (subst
      (λ upper → E0 * weightedQuarticCore amplitude samples ≤ upper)
      normalized
      scaled)

hhGoodLiteralAmplitudeAllocationClosed : Bool
hhGoodLiteralAmplitudeAllocationClosed = true

hhGoodDataEnergyFactorizationReductionClosed : Bool
hhGoodDataEnergyFactorizationReductionClosed = true

physicalHHGoodSelectedEnergyLegBoundConstructed : Bool
physicalHHGoodSelectedEnergyLegBoundConstructed = false

physicalHHGoodQuarticCoreCriticalDissipationConstructed : Bool
physicalHHGoodQuarticCoreCriticalDissipationConstructed = false

hhGoodLiteralAmplitudeAllocationClosedIsTrue :
  hhGoodLiteralAmplitudeAllocationClosed ≡ true
hhGoodLiteralAmplitudeAllocationClosedIsTrue = refl

hhGoodDataEnergyFactorizationReductionClosedIsTrue :
  hhGoodDataEnergyFactorizationReductionClosed ≡ true
hhGoodDataEnergyFactorizationReductionClosedIsTrue = refl
