module DASHI.Physics.Closure.NSTriadKNHHGoodParabolicWindowKineticRecoveryRound42Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: J. Thomas Beale; Tosio Kato; Andrew Majda.
-- Title: "Remarks on the Breakdown of Smooth Solutions for the 3-D Euler
-- Equations".
-- DOI: 10.1007/BF01240221.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- DASHI CONTRIBUTION
--
-- The companion Round-42 no-go proves that bare kinetic energy cannot control
-- a pointwise vorticity amplitude uniformly in shell:
--
--   |omega_q|^2 <= lambda_q^2 E0.
--
-- However Luo's localized criterion uses a parabolic terminal window of length
-- proportional to lambda_q^-2.  The two scale factors cancel exactly:
--
--   lambda_q^2 * lambda_q^-2 = 1.
--
-- This file proves that cancellation on the repository's exact dyadic scales
-- and then proves the finite positive-measure analogue of the time-localized
-- estimate.  If nonnegative time cells have total mass
--
--   sum_i dt_i <= c lambda_q^-2
--
-- and each selected vorticity square obeys
--
--   omega_i^2 <= lambda_q^2 E0,
--
-- then
--
--   sum_i dt_i omega_i^2 <= c E0.
--
-- Thus the kinetic-energy idea rejected pointwise in Round 42 is not dead:
-- it can be recovered after the *correct parabolic time localization*.  The
-- remaining physical theorem is to identify the actual HH-good time integral
-- with such a positive window measure while preserving the quartic core and
-- PV/cancellation ordering.  No continuum time-integration authority is
-- fabricated here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadDissipativeFloorChargingRound36Exact as Floor
import DASHI.Physics.Closure.NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact as ScaleNN

frequencySquare : Nat → ℚ
frequencySquare shell =
  Sharp.dyadicScale shell * Sharp.dyadicScale shell

parabolicWindowScale : Nat → ℚ
parabolicWindowScale shell =
  Sharp.inverseDyadicScale shell * Sharp.inverseDyadicScale shell

frequencySquareNonnegative : ∀ shell → 0ℚ ≤ frequencySquare shell
frequencySquareNonnegative shell =
  let
    scaleNN = ScaleNN.dyadicScaleNonnegative shell
    instance
      leftNN = nonNegative scaleNN
      rightNN = nonNegative scaleNN
      productNN = ℚP.nonNeg*nonNeg⇒nonNeg
        (Sharp.dyadicScale shell) (Sharp.dyadicScale shell)
  in
  ℚP.nonNegative⁻¹ (frequencySquare shell)

parabolicWindowScaleNonnegative : ∀ shell → 0ℚ ≤ parabolicWindowScale shell
parabolicWindowScaleNonnegative shell =
  let
    inverseNN = Floor.inverseDyadicScaleNonnegative shell
    instance
      leftNN = nonNegative inverseNN
      rightNN = nonNegative inverseNN
      productNN = ℚP.nonNeg*nonNeg⇒nonNeg
        (Sharp.inverseDyadicScale shell)
        (Sharp.inverseDyadicScale shell)
  in
  ℚP.nonNegative⁻¹ (parabolicWindowScale shell)

frequencySquareTimesParabolicWindowExact :
  ∀ shell →
  frequencySquare shell * parabolicWindowScale shell ≡ 1ℚ
frequencySquareTimesParabolicWindowExact shell =
  let
    lambda = Sharp.dyadicScale shell
    mu = Sharp.inverseDyadicScale shell

    regroup :
      (lambda * lambda) * (mu * mu)
      ≡ (mu * lambda) * (mu * lambda)
    regroup = solve (lambda ∷ mu ∷ [])
  in
  trans regroup
    (trans
      (cong (λ reciprocal → reciprocal * reciprocal)
        (Sharp.inverseDyadicReciprocal shell))
      (solve []))

record ParabolicKineticCell (shell : Nat) (dataEnergy : ℚ) : Set where
  field
    timeWeight : ℚ
    selectedVorticitySquare : ℚ
    timeWeightNonnegative : 0ℚ ≤ timeWeight
    selectedVorticitySquareNonnegative : 0ℚ ≤ selectedVorticitySquare
    vorticitySquareBelowFrequencyKinetic :
      selectedVorticitySquare ≤ frequencySquare shell * dataEnergy

open ParabolicKineticCell public

timeMass :
  ∀ {shell dataEnergy} →
  List (ParabolicKineticCell shell dataEnergy) → ℚ
timeMass [] = 0ℚ
timeMass (cell ∷ rest) = timeWeight cell + timeMass rest

localizedVorticityMass :
  ∀ {shell dataEnergy} →
  List (ParabolicKineticCell shell dataEnergy) → ℚ
localizedVorticityMass [] = 0ℚ
localizedVorticityMass (cell ∷ rest) =
  timeWeight cell * selectedVorticitySquare cell
  + localizedVorticityMass rest

localizedVorticityMassBelowFrequencyTimesTimeMass :
  ∀ {shell dataEnergy} →
  0ℚ ≤ dataEnergy →
  (cells : List (ParabolicKineticCell shell dataEnergy)) →
  localizedVorticityMass cells
  ≤ frequencySquare shell * dataEnergy * timeMass cells
localizedVorticityMassBelowFrequencyTimesTimeMass
    {shell} {dataEnergy} dataEnergyNN [] =
  subst
    (λ upper → 0ℚ ≤ upper)
    (solve (frequencySquare shell ∷ dataEnergy ∷ []))
    ℚP.≤-refl
localizedVorticityMassBelowFrequencyTimesTimeMass
    {shell} {dataEnergy} dataEnergyNN (cell ∷ rest) =
  let
    local :
      timeWeight cell * selectedVorticitySquare cell
      ≤ timeWeight cell * (frequencySquare shell * dataEnergy)
    local =
      let instance weightNN = nonNegative (timeWeightNonnegative cell)
      in ℚP.*-monoˡ-≤-nonNeg
          (timeWeight cell)
          (vorticitySquareBelowFrequencyKinetic cell)

    tail = localizedVorticityMassBelowFrequencyTimesTimeMass
      dataEnergyNN rest

    added = ℚP.+-mono-≤ local tail

    rightMeaning :
      timeWeight cell * (frequencySquare shell * dataEnergy)
      + frequencySquare shell * dataEnergy * timeMass rest
      ≡ frequencySquare shell * dataEnergy
          * (timeWeight cell + timeMass rest)
    rightMeaning = solve
      ( timeWeight cell
      ∷ frequencySquare shell
      ∷ dataEnergy
      ∷ timeMass rest
      ∷ [])
  in
  subst
    (λ upper → localizedVorticityMass (cell ∷ rest) ≤ upper)
    rightMeaning
    added

record ParabolicKineticRecovery
    (shell : Nat)
    (dataEnergy windowConstant : ℚ) : Set where
  field
    dataEnergyNonnegative : 0ℚ ≤ dataEnergy
    windowConstantNonnegative : 0ℚ ≤ windowConstant
    cells : List (ParabolicKineticCell shell dataEnergy)
    timeMassBelowParabolicWindow :
      timeMass cells ≤ windowConstant * parabolicWindowScale shell

open ParabolicKineticRecovery public

localizedVorticityMassBelowWindowConstantKineticEnergy :
  ∀ {shell dataEnergy windowConstant} →
  (recovery : ParabolicKineticRecovery shell dataEnergy windowConstant) →
  localizedVorticityMass (cells recovery)
  ≤ windowConstant * dataEnergy
localizedVorticityMassBelowWindowConstantKineticEnergy
    {shell} {dataEnergy} {windowConstant} recovery =
  let
    first = localizedVorticityMassBelowFrequencyTimesTimeMass
      (dataEnergyNonnegative recovery)
      (cells recovery)

    scale = frequencySquare shell * dataEnergy
    scaleNN : 0ℚ ≤ scale
    scaleNN =
      let
        instance
          freqNN = nonNegative (frequencySquareNonnegative shell)
          energyNN = nonNegative (dataEnergyNonnegative recovery)
          productNN = ℚP.nonNeg*nonNeg⇒nonNeg
            (frequencySquare shell) dataEnergy
      in
      ℚP.nonNegative⁻¹ scale

    second :
      scale * timeMass (cells recovery)
      ≤ scale * (windowConstant * parabolicWindowScale shell)
    second =
      let instance scaleNNI = nonNegative scaleNN
      in ℚP.*-monoˡ-≤-nonNeg scale
          (timeMassBelowParabolicWindow recovery)

    collapsed :
      scale * (windowConstant * parabolicWindowScale shell)
      ≡ windowConstant * dataEnergy
    collapsed =
      let
        lambda2 = frequencySquare shell
        mu2 = parabolicWindowScale shell

        regroup :
          (lambda2 * dataEnergy) * (windowConstant * mu2)
          ≡ windowConstant * dataEnergy * (lambda2 * mu2)
        regroup = solve
          (lambda2 ∷ dataEnergy ∷ windowConstant ∷ mu2 ∷ [])
      in
      trans regroup
        (trans
          (cong (windowConstant * dataEnergy *_)
            (frequencySquareTimesParabolicWindowExact shell))
          (solve (windowConstant ∷ dataEnergy ∷ [])))
  in
  ℚP.≤-trans first
    (ℚP.≤-trans second
      (subst
        (λ lower → lower ≤ windowConstant * dataEnergy)
        (sym collapsed)
        ℚP.≤-refl))

hhGoodParabolicKineticScaleCancellationClosed : Bool
hhGoodParabolicKineticScaleCancellationClosed = true

hhGoodFiniteParabolicKineticRecoveryClosed : Bool
hhGoodFiniteParabolicKineticRecoveryClosed = true

physicalHHGoodContinuumParabolicKineticRecoveryConstructed : Bool
physicalHHGoodContinuumParabolicKineticRecoveryConstructed = false

hhGoodParabolicKineticScaleCancellationClosedIsTrue :
  hhGoodParabolicKineticScaleCancellationClosed ≡ true
hhGoodParabolicKineticScaleCancellationClosedIsTrue = refl

hhGoodFiniteParabolicKineticRecoveryClosedIsTrue :
  hhGoodFiniteParabolicKineticRecoveryClosed ≡ true
hhGoodFiniteParabolicKineticRecoveryClosedIsTrue = refl
