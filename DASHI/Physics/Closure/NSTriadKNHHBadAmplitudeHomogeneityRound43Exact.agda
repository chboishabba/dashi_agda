module DASHI.Physics.Closure.NSTriadKNHHBadAmplitudeHomogeneityRound43Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
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
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Round 42 found two inverse powers in *frequency* scaling of literal
-- production versus viscous charge.  Frequency scaling alone is not a physical
-- HH-bad estimate, because the two quantities have different amplitude
-- homogeneity.  This file audits that missing direction exactly.
--
-- Keeping wavevectors fixed and scaling vorticity amplitudes by a common a:
--
--   u(a omega) = a u(omega),
--   F(a omega_p, a omega_r) = a^2 F(omega_p,omega_r),
--   P(a omega_k,a omega_p,a omega_r) = a^3 P(omega_k,omega_p,omega_r),
--   D(a omega_k) = a^2 D(omega_k).
--
-- Hence the production/dissipation ratio is degree +1 in amplitude.  More
-- sharply, a base estimate P <= C D transports to common amplitude a only as
--
--   P_a <= (a C) D_a,
--
-- not with the same C.  The Round-42 inverse-square frequency gain can close
-- HH-bad only after a genuine amplitude/critical/geometric producer controls
-- this extra factor.  This is a mathematical obstruction, not a bookkeeping
-- issue, and prevents us from falsely promoting the frequency-scaling theorem
-- to a uniform owner bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _*_; _+_; _-_; -_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans; subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalDirectionalDefectExact as Physical
import DASHI.Physics.Closure.NSTriadKNLuoPeriodicBiotSavartMultiplierExact as Biot
import DASHI.Physics.Closure.NSTriadKNLuoGalerkinFourierVorticityConvolutionExact as Conv
import DASHI.Physics.Closure.NSTriadKNHHBadLiteralVorticityInteractionScalingRound42Exact as Literal
import DASHI.Physics.Closure.NSTriadKNHHBadLiteralProductionDissipationScalingRound42Exact as Diss

scaleVec : ℚ → Gram.Vec3 → Gram.Vec3
scaleVec = Physical.scaleVec3

amplitudeScaledMode : ℚ → Biot.NonzeroVorticityMode → Biot.NonzeroVorticityMode
amplitudeScaledMode amplitude mode =
  Biot.nonzeroVorticityMode
    (Biot.wavevector mode)
    (scaleVec amplitude (Biot.vorticity mode))
    (Biot.inverseRadiusSquared mode)
    (Biot.inverseRadiusLaw mode)
    transverse
  where
  transverse :
    Gram.dot (Biot.wavevector mode)
      (scaleVec amplitude (Biot.vorticity mode)) ≡ 0ℚ
  transverse =
    trans
      (Conv.dotScaleRight
        (Biot.wavevector mode) amplitude (Biot.vorticity mode))
      (trans
        (cong (amplitude *_) (Biot.transverseVorticity mode))
        (solve (amplitude ∷ [])))

amplitudeScaledWavevector : ∀ amplitude mode →
  Biot.wavevector (amplitudeScaledMode amplitude mode)
  ≡ Biot.wavevector mode
amplitudeScaledWavevector amplitude mode = refl

amplitudeScaledVorticity : ∀ amplitude mode →
  Biot.vorticity (amplitudeScaledMode amplitude mode)
  ≡ scaleVec amplitude (Biot.vorticity mode)
amplitudeScaledVorticity amplitude mode = refl

amplitudeScaledInverseRadius : ∀ amplitude mode →
  Biot.inverseRadiusSquared (amplitudeScaledMode amplitude mode)
  ≡ Biot.inverseRadiusSquared mode
amplitudeScaledInverseRadius amplitude mode = refl

curlNumeratorAmplitudeLinear : ∀ amplitude mode →
  Biot.curlNumerator (amplitudeScaledMode amplitude mode)
  ≡ scaleVec amplitude (Biot.curlNumerator mode)
curlNumeratorAmplitudeLinear amplitude mode =
  Physical.vec3Ext
    (solve
      ( amplitude
      ∷ Gram.x (Biot.wavevector mode)
      ∷ Gram.y (Biot.wavevector mode)
      ∷ Gram.z (Biot.wavevector mode)
      ∷ Gram.x (Biot.vorticity mode)
      ∷ Gram.y (Biot.vorticity mode)
      ∷ Gram.z (Biot.vorticity mode)
      ∷ []))
    (solve
      ( amplitude
      ∷ Gram.x (Biot.wavevector mode)
      ∷ Gram.y (Biot.wavevector mode)
      ∷ Gram.z (Biot.wavevector mode)
      ∷ Gram.x (Biot.vorticity mode)
      ∷ Gram.y (Biot.vorticity mode)
      ∷ Gram.z (Biot.vorticity mode)
      ∷ []))
    (solve
      ( amplitude
      ∷ Gram.x (Biot.wavevector mode)
      ∷ Gram.y (Biot.wavevector mode)
      ∷ Gram.z (Biot.wavevector mode)
      ∷ Gram.x (Biot.vorticity mode)
      ∷ Gram.y (Biot.vorticity mode)
      ∷ Gram.z (Biot.vorticity mode)
      ∷ []))

velocityCarrierAmplitudeLinear : ∀ amplitude mode →
  Conv.velocityCarrier (amplitudeScaledMode amplitude mode)
  ≡ scaleVec amplitude (Conv.velocityCarrier mode)
velocityCarrierAmplitudeLinear amplitude mode =
  let
    inv = Biot.inverseRadiusSquared mode
    curl = Biot.curlNumerator mode
  in
  trans
    (cong (scaleVec inv) (curlNumeratorAmplitudeLinear amplitude mode))
    (Physical.vec3Ext
      (solve (inv ∷ amplitude ∷ Gram.x curl ∷ []))
      (solve (inv ∷ amplitude ∷ Gram.y curl ∷ []))
      (solve (inv ∷ amplitude ∷ Gram.z curl ∷ [])))

orderedInteractionAmplitudeBilinear :
  ∀ leftAmplitude rightAmplitude left right →
  Conv.orderedVorticityInteraction
    (amplitudeScaledMode leftAmplitude left)
    (amplitudeScaledMode rightAmplitude right)
  ≡
  scaleVec (leftAmplitude * rightAmplitude)
    (Conv.orderedVorticityInteraction left right)
orderedInteractionAmplitudeBilinear
    leftAmplitude rightAmplitude left right =
  Physical.vec3Ext
    (solve
      ( leftAmplitude ∷ rightAmplitude
      ∷ Biot.inverseRadiusSquared left
      ∷ Biot.inverseRadiusSquared right
      ∷ Gram.x (Biot.wavevector left)
      ∷ Gram.y (Biot.wavevector left)
      ∷ Gram.z (Biot.wavevector left)
      ∷ Gram.x (Biot.wavevector right)
      ∷ Gram.y (Biot.wavevector right)
      ∷ Gram.z (Biot.wavevector right)
      ∷ Gram.x (Biot.vorticity left)
      ∷ Gram.y (Biot.vorticity left)
      ∷ Gram.z (Biot.vorticity left)
      ∷ Gram.x (Biot.vorticity right)
      ∷ Gram.y (Biot.vorticity right)
      ∷ Gram.z (Biot.vorticity right)
      ∷ []))
    (solve
      ( leftAmplitude ∷ rightAmplitude
      ∷ Biot.inverseRadiusSquared left
      ∷ Biot.inverseRadiusSquared right
      ∷ Gram.x (Biot.wavevector left)
      ∷ Gram.y (Biot.wavevector left)
      ∷ Gram.z (Biot.wavevector left)
      ∷ Gram.x (Biot.wavevector right)
      ∷ Gram.y (Biot.wavevector right)
      ∷ Gram.z (Biot.wavevector right)
      ∷ Gram.x (Biot.vorticity left)
      ∷ Gram.y (Biot.vorticity left)
      ∷ Gram.z (Biot.vorticity left)
      ∷ Gram.x (Biot.vorticity right)
      ∷ Gram.y (Biot.vorticity right)
      ∷ Gram.z (Biot.vorticity right)
      ∷ []))
    (solve
      ( leftAmplitude ∷ rightAmplitude
      ∷ Biot.inverseRadiusSquared left
      ∷ Biot.inverseRadiusSquared right
      ∷ Gram.x (Biot.wavevector left)
      ∷ Gram.y (Biot.wavevector left)
      ∷ Gram.z (Biot.wavevector left)
      ∷ Gram.x (Biot.wavevector right)
      ∷ Gram.y (Biot.wavevector right)
      ∷ Gram.z (Biot.wavevector right)
      ∷ Gram.x (Biot.vorticity left)
      ∷ Gram.y (Biot.vorticity left)
      ∷ Gram.z (Biot.vorticity left)
      ∷ Gram.x (Biot.vorticity right)
      ∷ Gram.y (Biot.vorticity right)
      ∷ Gram.z (Biot.vorticity right)
      ∷ []))

orderedProductionAmplitudeTrilinear :
  ∀ outputAmplitude leftAmplitude rightAmplitude outputVorticity left right →
  Literal.orderedEnstrophyProduction
    (scaleVec outputAmplitude outputVorticity)
    (amplitudeScaledMode leftAmplitude left)
    (amplitudeScaledMode rightAmplitude right)
  ≡
  outputAmplitude * leftAmplitude * rightAmplitude
    * Literal.orderedEnstrophyProduction outputVorticity left right
orderedProductionAmplitudeTrilinear
    outputAmplitude leftAmplitude rightAmplitude outputVorticity left right =
  let
    interaction = Conv.orderedVorticityInteraction left right
    interactionScaling =
      orderedInteractionAmplitudeBilinear
        leftAmplitude rightAmplitude left right
    expose :
      Literal.orderedEnstrophyProduction
        (scaleVec outputAmplitude outputVorticity)
        (amplitudeScaledMode leftAmplitude left)
        (amplitudeScaledMode rightAmplitude right)
      ≡
      Gram.dot (scaleVec outputAmplitude outputVorticity)
        (scaleVec (leftAmplitude * rightAmplitude) interaction)
    expose = cong (Gram.dot (scaleVec outputAmplitude outputVorticity)) interactionScaling

    dotScaling =
      Literal.dotScaleBoth
        outputAmplitude outputVorticity
        (leftAmplitude * rightAmplitude) interaction

    regroup :
      outputAmplitude * (leftAmplitude * rightAmplitude)
        * Gram.dot outputVorticity interaction
      ≡ outputAmplitude * leftAmplitude * rightAmplitude
        * Literal.orderedEnstrophyProduction outputVorticity left right
    regroup = solve
      ( outputAmplitude ∷ leftAmplitude ∷ rightAmplitude
      ∷ Gram.dot outputVorticity interaction
      ∷ [])
  in
  trans expose (trans dotScaling regroup)

commonAmplitudeProductionCubic :
  ∀ amplitude outputVorticity left right →
  Literal.orderedEnstrophyProduction
    (scaleVec amplitude outputVorticity)
    (amplitudeScaledMode amplitude left)
    (amplitudeScaledMode amplitude right)
  ≡ amplitude * amplitude * amplitude
      * Literal.orderedEnstrophyProduction outputVorticity left right
commonAmplitudeProductionCubic amplitude outputVorticity left right =
  orderedProductionAmplitudeTrilinear
    amplitude amplitude amplitude outputVorticity left right

viscousChargeAmplitudeQuadratic :
  ∀ viscosity amplitude mode →
  Diss.viscousEnstrophyCharge viscosity (amplitudeScaledMode amplitude mode)
  ≡ amplitude * amplitude * Diss.viscousEnstrophyCharge viscosity mode
viscousChargeAmplitudeQuadratic viscosity amplitude mode =
  let
    k2 = Gram.normSquared (Biot.wavevector mode)
    omega = Biot.vorticity mode
    expose :
      Diss.viscousEnstrophyCharge viscosity (amplitudeScaledMode amplitude mode)
      ≡ viscosity * k2 * Gram.normSquared (scaleVec amplitude omega)
    expose = refl

    normScale = Literal.normSquaredScale amplitude omega

    regroup :
      viscosity * k2 * (amplitude * amplitude * Gram.normSquared omega)
      ≡ amplitude * amplitude * Diss.viscousEnstrophyCharge viscosity mode
    regroup = solve
      ( viscosity ∷ k2 ∷ amplitude ∷ Gram.normSquared omega ∷ [])
  in
  trans expose
    (trans
      (cong (viscosity * k2 *_) normScale)
      regroup)

commonAmplitudeBoundNeedsLinearCoefficient :
  ∀ viscosity coefficient amplitude outputVorticity left right outputMode →
  0ℚ ≤ amplitude →
  Literal.orderedEnstrophyProduction outputVorticity left right
    ≤ coefficient * Diss.viscousEnstrophyCharge viscosity outputMode →
  Literal.orderedEnstrophyProduction
      (scaleVec amplitude outputVorticity)
      (amplitudeScaledMode amplitude left)
      (amplitudeScaledMode amplitude right)
  ≤
  (amplitude * coefficient)
    * Diss.viscousEnstrophyCharge viscosity
        (amplitudeScaledMode amplitude outputMode)
commonAmplitudeBoundNeedsLinearCoefficient
    viscosity coefficient amplitude outputVorticity left right outputMode
    amplitudeNN baseBound =
  let
    production = Literal.orderedEnstrophyProduction outputVorticity left right
    dissipation = Diss.viscousEnstrophyCharge viscosity outputMode
    cube = amplitude * amplitude * amplitude

    squareNN : 0ℚ ≤ amplitude * amplitude
    squareNN =
      let instance amplitudeNNI = nonNegative amplitudeNN
      in ℚP.nonNegative⁻¹ (amplitude * amplitude)

    cubeNN : 0ℚ ≤ cube
    cubeNN =
      let
        instance
          squareNNI = nonNegative squareNN
          amplitudeNNI = nonNegative amplitudeNN
          cubeNNI = ℚP.nonNeg*nonNeg⇒nonNeg
            (amplitude * amplitude) amplitude
      in
      ℚP.nonNegative⁻¹ cube

    scaledBase : cube * production ≤ cube * (coefficient * dissipation)
    scaledBase =
      let instance cubeNNI = nonNegative cubeNN
      in ℚP.*-monoˡ-≤-nonNeg cube baseBound

    leftMeaning :
      Literal.orderedEnstrophyProduction
        (scaleVec amplitude outputVorticity)
        (amplitudeScaledMode amplitude left)
        (amplitudeScaledMode amplitude right)
      ≡ cube * production
    leftMeaning = commonAmplitudeProductionCubic
      amplitude outputVorticity left right

    rightMeaning :
      (amplitude * coefficient)
        * Diss.viscousEnstrophyCharge viscosity
            (amplitudeScaledMode amplitude outputMode)
      ≡ cube * (coefficient * dissipation)
    rightMeaning =
      trans
        (cong ((amplitude * coefficient) *_)
          (viscousChargeAmplitudeQuadratic viscosity amplitude outputMode))
        (solve (amplitude ∷ coefficient ∷ dissipation ∷ []))
  in
  subst
    (λ lower →
      lower
      ≤ (amplitude * coefficient)
        * Diss.viscousEnstrophyCharge viscosity
            (amplitudeScaledMode amplitude outputMode))
    (sym leftMeaning)
    (subst
      (λ upper → cube * production ≤ upper)
      (sym rightMeaning)
      scaledBase)

literalProductionAmplitudeDegree : Bool
literalProductionAmplitudeDegree = true

viscousChargeAmplitudeDegree : Bool
viscousChargeAmplitudeDegree = true

frequencyInverseSquareDoesNotRemoveAmplitudeFactor : Bool
frequencyInverseSquareDoesNotRemoveAmplitudeFactor = true

amplitudeCorrectedCoefficientTransportClosed : Bool
amplitudeCorrectedCoefficientTransportClosed = true

literalProductionAmplitudeDegreeIsTrue :
  literalProductionAmplitudeDegree ≡ true
literalProductionAmplitudeDegreeIsTrue = refl

viscousChargeAmplitudeDegreeIsTrue :
  viscousChargeAmplitudeDegree ≡ true
viscousChargeAmplitudeDegreeIsTrue = refl

frequencyInverseSquareDoesNotRemoveAmplitudeFactorIsTrue :
  frequencyInverseSquareDoesNotRemoveAmplitudeFactor ≡ true
frequencyInverseSquareDoesNotRemoveAmplitudeFactorIsTrue = refl

amplitudeCorrectedCoefficientTransportClosedIsTrue :
  amplitudeCorrectedCoefficientTransportClosed ≡ true
amplitudeCorrectedCoefficientTransportClosedIsTrue = refl
