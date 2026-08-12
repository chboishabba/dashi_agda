module DASHI.Physics.Closure.NSTriadKNHHGoodParabolicAmplitudeAllocationRound42Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- `NSTriadKNHHGoodParabolicWindowKineticRecoveryRound42Exact` proves that the
-- lambda_q^2 cost of controlling one vorticity square by kinetic energy is
-- cancelled by a terminal window of total mass O(lambda_q^-2).
--
-- The HH-good local mass is the selected square times the residual quartic
-- core.  This file carries the parabolic cancellation through that exact
-- product.  For nonnegative time cells assume
--
--   omega_i^2 <= lambda_q^2 E0,
--   Q_i <= Q,
--   sum_i dt_i <= c lambda_q^-2.
--
-- Then
--
--   sum_i dt_i omega_i^2 Q_i <= c E0 Q.
--
-- If the common quartic envelope satisfies Q <= X D, then
--
--   sum_i dt_i omega_i^2 Q_i <= c E0 X D.
--
-- This is a concrete repaired version of the false pointwise `W<=E0 X D`
-- shortcut.  The remaining physical work is sharply same-object: construct
-- the actual terminal-window cells after PV/shell localization and prove a
-- cutoff-uniform quartic envelope (or a stronger replacement).  No continuum
-- time-integration or supremum theorem is fabricated here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHGoodParabolicWindowKineticRecoveryRound42Exact as Window

record ParabolicAmplitudeCell
    (shell : Nat)
    (dataEnergy quarticEnvelope : ℚ) : Set where
  field
    timeWeight : ℚ
    selectedVorticitySquare : ℚ
    quarticCore : ℚ

    timeWeightNonnegative : 0ℚ ≤ timeWeight
    selectedVorticitySquareNonnegative : 0ℚ ≤ selectedVorticitySquare
    quarticCoreNonnegative : 0ℚ ≤ quarticCore

    vorticitySquareBelowFrequencyKinetic :
      selectedVorticitySquare ≤ Window.frequencySquare shell * dataEnergy

    quarticCoreBelowEnvelope : quarticCore ≤ quarticEnvelope

open ParabolicAmplitudeCell public

amplitudeTimeMass :
  ∀ {shell dataEnergy quarticEnvelope} →
  List (ParabolicAmplitudeCell shell dataEnergy quarticEnvelope) → ℚ
amplitudeTimeMass [] = 0ℚ
amplitudeTimeMass (cell ∷ rest) =
  timeWeight cell + amplitudeTimeMass rest

localizedAmplitudeQuarticMass :
  ∀ {shell dataEnergy quarticEnvelope} →
  List (ParabolicAmplitudeCell shell dataEnergy quarticEnvelope) → ℚ
localizedAmplitudeQuarticMass [] = 0ℚ
localizedAmplitudeQuarticMass (cell ∷ rest) =
  timeWeight cell * selectedVorticitySquare cell * quarticCore cell
  + localizedAmplitudeQuarticMass rest

localAmplitudeQuarticBelowUniformEnvelope :
  ∀ {shell dataEnergy quarticEnvelope} →
  0ℚ ≤ dataEnergy →
  0ℚ ≤ quarticEnvelope →
  (cell : ParabolicAmplitudeCell shell dataEnergy quarticEnvelope) →
  timeWeight cell * selectedVorticitySquare cell * quarticCore cell
  ≤
  timeWeight cell
    * (Window.frequencySquare shell * dataEnergy)
    * quarticEnvelope
localAmplitudeQuarticBelowUniformEnvelope
    {shell} {dataEnergy} dataEnergyNN envelopeNN cell =
  let
    weightedOmegaUpper :
      timeWeight cell * selectedVorticitySquare cell
      ≤ timeWeight cell * (Window.frequencySquare shell * dataEnergy)
    weightedOmegaUpper =
      let instance weightNN = nonNegative (timeWeightNonnegative cell)
      in ℚP.*-monoˡ-≤-nonNeg
          (timeWeight cell)
          (vorticitySquareBelowFrequencyKinetic cell)

    leftScale :
      (timeWeight cell * selectedVorticitySquare cell) * quarticCore cell
      ≤
      (timeWeight cell * (Window.frequencySquare shell * dataEnergy))
        * quarticCore cell
    leftScale =
      let instance coreNN = nonNegative (quarticCoreNonnegative cell)
      in ℚP.*-monoʳ-≤-nonNeg (quarticCore cell) weightedOmegaUpper

    frequencyEnergyNN :
      0ℚ ≤ Window.frequencySquare shell * dataEnergy
    frequencyEnergyNN =
      let
        instance
          frequencyNN = nonNegative (Window.frequencySquareNonnegative shell)
          energyNN = nonNegative dataEnergyNN
          productNN = ℚP.nonNeg*nonNeg⇒nonNeg
            (Window.frequencySquare shell) dataEnergy
      in
      ℚP.nonNegative⁻¹ (Window.frequencySquare shell * dataEnergy)

    weightedFrequencyEnergyNN :
      0ℚ ≤ timeWeight cell * (Window.frequencySquare shell * dataEnergy)
    weightedFrequencyEnergyNN =
      let
        instance
          weightNN = nonNegative (timeWeightNonnegative cell)
          frequencyEnergyNNI = nonNegative frequencyEnergyNN
          productNN = ℚP.nonNeg*nonNeg⇒nonNeg
            (timeWeight cell)
            (Window.frequencySquare shell * dataEnergy)
      in
      ℚP.nonNegative⁻¹
        (timeWeight cell * (Window.frequencySquare shell * dataEnergy))

    rightScale :
      (timeWeight cell * (Window.frequencySquare shell * dataEnergy))
        * quarticCore cell
      ≤
      (timeWeight cell * (Window.frequencySquare shell * dataEnergy))
        * quarticEnvelope
    rightScale =
      let instance prefixNN = nonNegative weightedFrequencyEnergyNN
      in ℚP.*-monoˡ-≤-nonNeg
          (timeWeight cell * (Window.frequencySquare shell * dataEnergy))
          (quarticCoreBelowEnvelope cell)
  in
  ℚP.≤-trans leftScale rightScale

record ParabolicAmplitudeRecovery
    (shell : Nat)
    (dataEnergy windowConstant quarticEnvelope : ℚ) : Set where
  field
    dataEnergyNonnegative : 0ℚ ≤ dataEnergy
    windowConstantNonnegative : 0ℚ ≤ windowConstant
    quarticEnvelopeNonnegative : 0ℚ ≤ quarticEnvelope
    cells : List (ParabolicAmplitudeCell shell dataEnergy quarticEnvelope)
    timeMassBelowParabolicWindow :
      amplitudeTimeMass cells
      ≤ windowConstant * Window.parabolicWindowScale shell

open ParabolicAmplitudeRecovery public

localizedAmplitudeQuarticBelowFrequencyEnvelopeTimeMass :
  ∀ {shell dataEnergy windowConstant quarticEnvelope}
    (recovery : ParabolicAmplitudeRecovery
      shell dataEnergy windowConstant quarticEnvelope) →
  localizedAmplitudeQuarticMass (cells recovery)
  ≤
  Window.frequencySquare shell * dataEnergy * quarticEnvelope
    * amplitudeTimeMass (cells recovery)
localizedAmplitudeQuarticBelowFrequencyEnvelopeTimeMass
    {shell} {dataEnergy} {quarticEnvelope = quarticEnvelope} recovery =
  go (cells recovery)
  where
  go :
    (selected : List (ParabolicAmplitudeCell shell dataEnergy quarticEnvelope)) →
    localizedAmplitudeQuarticMass selected
    ≤ Window.frequencySquare shell * dataEnergy * quarticEnvelope
        * amplitudeTimeMass selected
  go [] =
    subst
      (λ upper → 0ℚ ≤ upper)
      (solve
        ( Window.frequencySquare shell
        ∷ dataEnergy
        ∷ quarticEnvelope
        ∷ []))
      ℚP.≤-refl
  go (cell ∷ rest) =
    let
      local = localAmplitudeQuarticBelowUniformEnvelope
        (dataEnergyNonnegative recovery)
        (quarticEnvelopeNonnegative recovery)
        cell
      tail = go rest
      added = ℚP.+-mono-≤ local tail

      rightMeaning :
        timeWeight cell * (Window.frequencySquare shell * dataEnergy)
          * quarticEnvelope
        + Window.frequencySquare shell * dataEnergy * quarticEnvelope
          * amplitudeTimeMass rest
        ≡ Window.frequencySquare shell * dataEnergy * quarticEnvelope
          * amplitudeTimeMass (cell ∷ rest)
      rightMeaning = solve
        ( timeWeight cell
        ∷ Window.frequencySquare shell
        ∷ dataEnergy
        ∷ quarticEnvelope
        ∷ amplitudeTimeMass rest
        ∷ [])
    in
    subst
      (λ upper → localizedAmplitudeQuarticMass (cell ∷ rest) ≤ upper)
      rightMeaning
      added

localizedAmplitudeQuarticBelowParabolicKineticEnvelope :
  ∀ {shell dataEnergy windowConstant quarticEnvelope}
    (recovery : ParabolicAmplitudeRecovery
      shell dataEnergy windowConstant quarticEnvelope) →
  localizedAmplitudeQuarticMass (cells recovery)
  ≤ windowConstant * dataEnergy * quarticEnvelope
localizedAmplitudeQuarticBelowParabolicKineticEnvelope
    {shell} {dataEnergy} {windowConstant} {quarticEnvelope} recovery =
  let
    first = localizedAmplitudeQuarticBelowFrequencyEnvelopeTimeMass recovery

    scale = Window.frequencySquare shell * dataEnergy * quarticEnvelope
    scaleNN : 0ℚ ≤ scale
    scaleNN =
      let
        instance
          frequencyNN = nonNegative (Window.frequencySquareNonnegative shell)
          energyNN = nonNegative (dataEnergyNonnegative recovery)
          quarticNN = nonNegative (quarticEnvelopeNonnegative recovery)
          firstProductNN = ℚP.nonNeg*nonNeg⇒nonNeg
            (Window.frequencySquare shell) dataEnergy
          fullProductNN = ℚP.nonNeg*nonNeg⇒nonNeg
            (Window.frequencySquare shell * dataEnergy) quarticEnvelope
      in
      ℚP.nonNegative⁻¹ scale

    second :
      scale * amplitudeTimeMass (cells recovery)
      ≤ scale * (windowConstant * Window.parabolicWindowScale shell)
    second =
      let instance scaleNNI = nonNegative scaleNN
      in ℚP.*-monoˡ-≤-nonNeg scale
          (timeMassBelowParabolicWindow recovery)

    collapsed :
      scale * (windowConstant * Window.parabolicWindowScale shell)
      ≡ windowConstant * dataEnergy * quarticEnvelope
    collapsed =
      let
        lambda2 = Window.frequencySquare shell
        mu2 = Window.parabolicWindowScale shell
        regroup :
          (lambda2 * dataEnergy * quarticEnvelope) * (windowConstant * mu2)
          ≡ windowConstant * dataEnergy * quarticEnvelope * (lambda2 * mu2)
        regroup = solve
          (lambda2 ∷ dataEnergy ∷ quarticEnvelope ∷ windowConstant ∷ mu2 ∷ [])
      in
      trans regroup
        (trans
          (cong (windowConstant * dataEnergy * quarticEnvelope *_)
            (Window.frequencySquareTimesParabolicWindowExact shell))
          (solve (windowConstant ∷ dataEnergy ∷ quarticEnvelope ∷ [])))
  in
  ℚP.≤-trans first
    (ℚP.≤-trans second
      (subst
        (λ lower → lower ≤ windowConstant * dataEnergy * quarticEnvelope)
        (sym collapsed)
        ℚP.≤-refl))

record ParabolicHHGoodCriticalRecovery
    (environment : Owner.TaxEnvironment)
    (shell : Nat)
    (dataEnergy windowConstant quarticEnvelope : ℚ) : Set where
  field
    recovery : ParabolicAmplitudeRecovery
      shell dataEnergy windowConstant quarticEnvelope
    quarticEnvelopeBelowCriticalDissipation :
      quarticEnvelope
      ≤ Owner.integralCritical environment * Owner.dissipation environment

open ParabolicHHGoodCriticalRecovery public

localizedHHGoodMassBelowParabolicKineticCriticalDissipation :
  ∀ {environment shell dataEnergy windowConstant quarticEnvelope}
    (input : ParabolicHHGoodCriticalRecovery
      environment shell dataEnergy windowConstant quarticEnvelope) →
  localizedAmplitudeQuarticMass (cells (recovery input))
  ≤ windowConstant * dataEnergy
      * Owner.integralCritical environment
      * Owner.dissipation environment
localizedHHGoodMassBelowParabolicKineticCriticalDissipation
    {environment} {dataEnergy} {windowConstant} {quarticEnvelope} input =
  let
    rec = recovery input
    first = localizedAmplitudeQuarticBelowParabolicKineticEnvelope rec

    prefix = windowConstant * dataEnergy
    prefixNN : 0ℚ ≤ prefix
    prefixNN =
      let
        instance
          windowNN = nonNegative (windowConstantNonnegative rec)
          energyNN = nonNegative (dataEnergyNonnegative rec)
          productNN = ℚP.nonNeg*nonNeg⇒nonNeg windowConstant dataEnergy
      in
      ℚP.nonNegative⁻¹ prefix

    scaled :
      prefix * quarticEnvelope
      ≤ prefix * (Owner.integralCritical environment * Owner.dissipation environment)
    scaled =
      let instance prefixNNI = nonNegative prefixNN
      in ℚP.*-monoˡ-≤-nonNeg prefix
          (quarticEnvelopeBelowCriticalDissipation input)

    targetMeaning :
      prefix * (Owner.integralCritical environment * Owner.dissipation environment)
      ≡ windowConstant * dataEnergy
          * Owner.integralCritical environment
          * Owner.dissipation environment
    targetMeaning = solve
      ( windowConstant
      ∷ dataEnergy
      ∷ Owner.integralCritical environment
      ∷ Owner.dissipation environment
      ∷ [])
  in
  ℚP.≤-trans first
    (subst
      (λ upper → prefix * quarticEnvelope ≤ upper)
      targetMeaning
      scaled)

hhGoodParabolicAmplitudeAllocationClosed : Bool
hhGoodParabolicAmplitudeAllocationClosed = true

hhGoodParabolicKineticQuarticRecoveryClosed : Bool
hhGoodParabolicKineticQuarticRecoveryClosed = true

physicalHHGoodParabolicWindowQuarticEnvelopeConstructed : Bool
physicalHHGoodParabolicWindowQuarticEnvelopeConstructed = false

hhGoodParabolicAmplitudeAllocationClosedIsTrue :
  hhGoodParabolicAmplitudeAllocationClosed ≡ true
hhGoodParabolicAmplitudeAllocationClosedIsTrue = refl
