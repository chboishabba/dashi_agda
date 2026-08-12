module DASHI.Physics.Closure.NSTriadKNHHBadLiteralVorticityInteractionScalingRound42Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- DASHI CONTRIBUTION
--
-- The repository already contains the literal finite Fourier vorticity
-- interaction
--
--   F(p,r) = (omega_p.r) u_r - (u_p.r) omega_r,
--   u_p = |p|^-2 (p cross omega_p),
--
-- with the common complex phase factored out.
--
-- Round 41/42 tested whether the HH-bad physical gain could have exactly one
-- net derivative before the parabolic inverse.  This file audits the *literal
-- vorticity nonlinearity itself* rather than a schematic Schur expression.
-- Under a common positive rational frequency rescaling
--
--   p -> s p,   r -> s r,
--
-- with vorticity amplitudes held fixed, Biot--Savart gives
--
--   u_(s p) = s^-1 u_p.
--
-- Consequently
--
--   (omega_p . s r) u_(s r)
--       = (s)(s^-1) (omega_p.r) u_r,
--
-- and
--
--   (u_(s p) . s r) omega_r
--       = (s^-1)(s) (u_p.r) omega_r.
--
-- Both ordered terms are therefore exactly scale invariant, and so are their
-- difference, the symmetrized physical coefficient, and pairing either with
-- a fixed output vorticity.
--
-- This is a strong same-object diagnostic: the literal vorticity convolution
-- and its fixed-output production scalar are order zero in common HH frequency
-- scale.  Therefore any `one derivative` appearing in the Round-41 restricted
-- gain density must come from a later shell/source/energy normalization, not
-- from the raw vorticity interaction itself.  The remaining HH-bad task is to
-- identify that later normalization exactly before assigning the inverse-shell
-- Schur cost.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalDirectionalDefectExact as Physical
import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNLuoPeriodicBiotSavartMultiplierExact as Biot
import DASHI.Physics.Closure.NSTriadKNLuoGalerkinFourierVorticityConvolutionExact as Conv

scaleVec : ℚ → Gram.Vec3 → Gram.Vec3
scaleVec = Physical.scaleVec3

normSquaredScale : ∀ scalar value →
  Gram.normSquared (scaleVec scalar value)
  ≡ scalar * scalar * Gram.normSquared value
normSquaredScale scalar (Gram.vec3 x y z) =
  solve (scalar ∷ x ∷ y ∷ z ∷ [])

crossScaleLeft : ∀ scalar left right →
  Gram.cross (scaleVec scalar left) right
  ≡ scaleVec scalar (Gram.cross left right)
crossScaleLeft scalar (Gram.vec3 lx ly lz) (Gram.vec3 rx ry rz) =
  Physical.vec3Ext
    (solve (scalar ∷ lx ∷ ly ∷ lz ∷ rx ∷ ry ∷ rz ∷ []))
    (solve (scalar ∷ lx ∷ ly ∷ lz ∷ rx ∷ ry ∷ rz ∷ []))
    (solve (scalar ∷ lx ∷ ly ∷ lz ∷ rx ∷ ry ∷ rz ∷ []))

scaleVecCompose : ∀ left right value →
  scaleVec left (scaleVec right value)
  ≡ scaleVec (left * right) value
scaleVecCompose left right (Gram.vec3 x y z) =
  Physical.vec3Ext
    (solve (left ∷ right ∷ x ∷ []))
    (solve (left ∷ right ∷ y ∷ []))
    (solve (left ∷ right ∷ z ∷ []))

dotScaleBoth : ∀ leftScale left rightScale right →
  Gram.dot (scaleVec leftScale left) (scaleVec rightScale right)
  ≡ leftScale * rightScale * Gram.dot left right
dotScaleBoth leftScale (Gram.vec3 lx ly lz)
    rightScale (Gram.vec3 rx ry rz) =
  solve
    ( leftScale ∷ rightScale
    ∷ lx ∷ ly ∷ lz ∷ rx ∷ ry ∷ rz
    ∷ [])

scaledNonzeroVorticityMode :
  Threshold.PositiveThreshold →
  Biot.NonzeroVorticityMode →
  Biot.NonzeroVorticityMode
scaledNonzeroVorticityMode scale mode =
  Biot.nonzeroVorticityMode
    (scaleVec r (Biot.wavevector mode))
    (Biot.vorticity mode)
    (Biot.inverseRadiusSquared mode * rinv * rinv)
    scaledInverseLaw
    scaledTransverse
  where
  r = Threshold.threshold scale
  rinv = Threshold.thresholdInverse scale
  k = Biot.wavevector mode
  omega = Biot.vorticity mode
  inv = Biot.inverseRadiusSquared mode
  radiusSquared = Gram.normSquared k

  scaledInverseLaw :
    Gram.normSquared (scaleVec r k) * (inv * rinv * rinv) ≡ 1ℚ
  scaledInverseLaw =
    let
      exposeScaledNorm :
        Gram.normSquared (scaleVec r k) * (inv * rinv * rinv)
        ≡ (r * r * radiusSquared) * (inv * rinv * rinv)
      exposeScaledNorm =
        cong (_* (inv * rinv * rinv)) (normSquaredScale r k)

      regroup :
        (r * r * radiusSquared) * (inv * rinv * rinv)
        ≡ (radiusSquared * inv) * (rinv * r) * (rinv * r)
      regroup = solve (r ∷ rinv ∷ radiusSquared ∷ inv ∷ [])

      cancelRadius :
        (radiusSquared * inv) * (rinv * r) * (rinv * r)
        ≡ 1ℚ * (rinv * r) * (rinv * r)
      cancelRadius =
        cong (λ reciprocal → reciprocal * (rinv * r) * (rinv * r))
          (Biot.inverseRadiusLaw mode)

      cancelScale :
        1ℚ * (rinv * r) * (rinv * r) ≡ 1ℚ
      cancelScale rewrite Threshold.inverseMeaning scale = solve []
    in
    trans exposeScaledNorm
      (trans regroup (trans cancelRadius cancelScale))

  scaledTransverse :
    Gram.dot (scaleVec r k) omega ≡ 0ℚ
  scaledTransverse =
    trans
      (dotScaleBoth r k 1ℚ omega)
      (trans
        (cong (λ value → r * 1ℚ * value)
          (Biot.transverseVorticity mode))
        (solve (r ∷ [])))

scaledWavevector : ∀ scale mode →
  Biot.wavevector (scaledNonzeroVorticityMode scale mode)
  ≡ scaleVec (Threshold.threshold scale) (Biot.wavevector mode)
scaledWavevector scale mode = refl

scaledVorticity : ∀ scale mode →
  Biot.vorticity (scaledNonzeroVorticityMode scale mode)
  ≡ Biot.vorticity mode
scaledVorticity scale mode = refl

scaledInverseRadiusSquared : ∀ scale mode →
  Biot.inverseRadiusSquared (scaledNonzeroVorticityMode scale mode)
  ≡ Biot.inverseRadiusSquared mode
      * Threshold.thresholdInverse scale
      * Threshold.thresholdInverse scale
scaledInverseRadiusSquared scale mode = refl

scaledCurlNumerator : ∀ scale mode →
  Biot.curlNumerator (scaledNonzeroVorticityMode scale mode)
  ≡ scaleVec (Threshold.threshold scale) (Biot.curlNumerator mode)
scaledCurlNumerator scale mode =
  crossScaleLeft
    (Threshold.threshold scale)
    (Biot.wavevector mode)
    (Biot.vorticity mode)

scaledVelocityCarrier : ∀ scale mode →
  Conv.velocityCarrier (scaledNonzeroVorticityMode scale mode)
  ≡ scaleVec (Threshold.thresholdInverse scale) (Conv.velocityCarrier mode)
scaledVelocityCarrier scale mode =
  let
    r = Threshold.threshold scale
    rinv = Threshold.thresholdInverse scale
    inv = Biot.inverseRadiusSquared mode
    curl = Biot.curlNumerator mode

    exposeCurl :
      scaleVec (inv * rinv * rinv)
        (Biot.curlNumerator (scaledNonzeroVorticityMode scale mode))
      ≡ scaleVec (inv * rinv * rinv) (scaleVec r curl)
    exposeCurl =
      cong (scaleVec (inv * rinv * rinv))
        (scaledCurlNumerator scale mode)

    compose :
      scaleVec (inv * rinv * rinv) (scaleVec r curl)
      ≡ scaleVec ((inv * rinv * rinv) * r) curl
    compose = scaleVecCompose (inv * rinv * rinv) r curl

    coefficient :
      (inv * rinv * rinv) * r ≡ rinv * inv
    coefficient =
      trans
        (solve (inv ∷ rinv ∷ r ∷ []))
        (trans
          (cong (λ reciprocal → rinv * inv * reciprocal)
            (Threshold.inverseMeaning scale))
          (solve (rinv ∷ inv ∷ [])))

    targetCompose :
      scaleVec rinv (scaleVec inv curl)
      ≡ scaleVec (rinv * inv) curl
    targetCompose = scaleVecCompose rinv inv curl
  in
  trans exposeCurl
    (trans compose
      (trans
        (cong (λ scalar → scaleVec scalar curl) coefficient)
        (sym targetCompose)))

stretchCoefficientScales : ∀ scale left right →
  Gram.dot
    (Biot.vorticity (scaledNonzeroVorticityMode scale left))
    (Biot.wavevector (scaledNonzeroVorticityMode scale right))
  ≡ Threshold.threshold scale
      * Gram.dot (Biot.vorticity left) (Biot.wavevector right)
stretchCoefficientScales scale left right =
  Conv.dotScaleRight
    (Biot.vorticity left)
    (Threshold.threshold scale)
    (Biot.wavevector right)

transportCoefficientScaleCancels : ∀ scale left right →
  Gram.dot
    (Conv.velocityCarrier (scaledNonzeroVorticityMode scale left))
    (Biot.wavevector (scaledNonzeroVorticityMode scale right))
  ≡ Gram.dot (Conv.velocityCarrier left) (Biot.wavevector right)
transportCoefficientScaleCancels scale left right =
  let
    r = Threshold.threshold scale
    rinv = Threshold.thresholdInverse scale
    u = Conv.velocityCarrier left
    q = Biot.wavevector right

    both :
      Gram.dot (scaleVec rinv u) (scaleVec r q)
      ≡ rinv * r * Gram.dot u q
    both = dotScaleBoth rinv u r q
  in
  trans
    (cong₂ Gram.dot
      (scaledVelocityCarrier scale left)
      (scaledWavevector scale right))
    (trans both
      (trans
        (cong (λ reciprocal → reciprocal * Gram.dot u q)
          (Threshold.inverseMeaning scale))
        (solve (Gram.dot u q ∷ []))))

scaledStretchTermInvariant : ∀ scale left right →
  scaleVec
    (Gram.dot
      (Biot.vorticity (scaledNonzeroVorticityMode scale left))
      (Biot.wavevector (scaledNonzeroVorticityMode scale right)))
    (Conv.velocityCarrier (scaledNonzeroVorticityMode scale right))
  ≡
  scaleVec
    (Gram.dot (Biot.vorticity left) (Biot.wavevector right))
    (Conv.velocityCarrier right)
scaledStretchTermInvariant scale left right =
  let
    r = Threshold.threshold scale
    rinv = Threshold.thresholdInverse scale
    coefficient = Gram.dot (Biot.vorticity left) (Biot.wavevector right)
    velocity = Conv.velocityCarrier right

    coefficientCancel :
      (r * coefficient) * rinv ≡ coefficient
    coefficientCancel =
      trans
        (solve (r ∷ rinv ∷ coefficient ∷ []))
        (trans
          (cong (λ reciprocal → coefficient * reciprocal)
            (Threshold.inverseMeaning scale))
          (solve (coefficient ∷ [])))
  in
  trans
    (cong₂ scaleVec
      (stretchCoefficientScales scale left right)
      (scaledVelocityCarrier scale right))
    (trans
      (scaleVecCompose (r * coefficient) rinv velocity)
      (cong (λ scalar → scaleVec scalar velocity) coefficientCancel))

scaledTransportTermInvariant : ∀ scale left right →
  scaleVec
    (Gram.dot
      (Conv.velocityCarrier (scaledNonzeroVorticityMode scale left))
      (Biot.wavevector (scaledNonzeroVorticityMode scale right)))
    (Biot.vorticity (scaledNonzeroVorticityMode scale right))
  ≡
  scaleVec
    (Gram.dot (Conv.velocityCarrier left) (Biot.wavevector right))
    (Biot.vorticity right)
scaledTransportTermInvariant scale left right =
  cong₂ scaleVec
    (transportCoefficientScaleCancels scale left right)
    (scaledVorticity scale right)

orderedVorticityInteractionScaleInvariant : ∀ scale left right →
  Conv.orderedVorticityInteraction
    (scaledNonzeroVorticityMode scale left)
    (scaledNonzeroVorticityMode scale right)
  ≡ Conv.orderedVorticityInteraction left right
orderedVorticityInteractionScaleInvariant scale left right =
  Physical.vec3Ext
    componentX componentY componentZ
  where
  stretch = scaledStretchTermInvariant scale left right
  transport = scaledTransportTermInvariant scale left right

  componentX = cong₂ _-_ (cong Gram.x stretch) (cong Gram.x transport)
  componentY = cong₂ _-_ (cong Gram.y stretch) (cong Gram.y transport)
  componentZ = cong₂ _-_ (cong Gram.z stretch) (cong Gram.z transport)

symmetrizedVorticityInteractionScaleInvariant : ∀ scale left right →
  Conv.symmetrizedVorticityInteraction
    (scaledNonzeroVorticityMode scale left)
    (scaledNonzeroVorticityMode scale right)
  ≡ Conv.symmetrizedVorticityInteraction left right
symmetrizedVorticityInteractionScaleInvariant scale left right =
  Physical.vec3Ext
    componentX componentY componentZ
  where
  first = orderedVorticityInteractionScaleInvariant scale left right
  second = orderedVorticityInteractionScaleInvariant scale right left

  componentX = cong₂ _+_ (cong Gram.x first) (cong Gram.x second)
  componentY = cong₂ _+_ (cong Gram.y first) (cong Gram.y second)
  componentZ = cong₂ _+_ (cong Gram.z first) (cong Gram.z second)

orderedEnstrophyProduction :
  Gram.Vec3 → Biot.NonzeroVorticityMode → Biot.NonzeroVorticityMode → ℚ
orderedEnstrophyProduction outputVorticity left right =
  Gram.dot outputVorticity (Conv.orderedVorticityInteraction left right)

symmetrizedEnstrophyProduction :
  Gram.Vec3 → Biot.NonzeroVorticityMode → Biot.NonzeroVorticityMode → ℚ
symmetrizedEnstrophyProduction outputVorticity left right =
  Gram.dot outputVorticity (Conv.symmetrizedVorticityInteraction left right)

orderedEnstrophyProductionScaleInvariant :
  ∀ outputVorticity scale left right →
  orderedEnstrophyProduction outputVorticity
    (scaledNonzeroVorticityMode scale left)
    (scaledNonzeroVorticityMode scale right)
  ≡ orderedEnstrophyProduction outputVorticity left right
orderedEnstrophyProductionScaleInvariant outputVorticity scale left right =
  cong (Gram.dot outputVorticity)
    (orderedVorticityInteractionScaleInvariant scale left right)

symmetrizedEnstrophyProductionScaleInvariant :
  ∀ outputVorticity scale left right →
  symmetrizedEnstrophyProduction outputVorticity
    (scaledNonzeroVorticityMode scale left)
    (scaledNonzeroVorticityMode scale right)
  ≡ symmetrizedEnstrophyProduction outputVorticity left right
symmetrizedEnstrophyProductionScaleInvariant outputVorticity scale left right =
  cong (Gram.dot outputVorticity)
    (symmetrizedVorticityInteractionScaleInvariant scale left right)

literalVorticityInteractionCommonHHScaleInvariant : Bool
literalVorticityInteractionCommonHHScaleInvariant = true

literalEnstrophyProductionCommonHHScaleInvariant : Bool
literalEnstrophyProductionCommonHHScaleInvariant = true

rawVorticityInteractionCarriesNoNetCommonHHDerivative : Bool
rawVorticityInteractionCarriesNoNetCommonHHDerivative = true

hhBadOneDerivativeMustEnterAfterRawVorticityConvolution : Bool
hhBadOneDerivativeMustEnterAfterRawVorticityConvolution = true

literalVorticityInteractionCommonHHScaleInvariantIsTrue :
  literalVorticityInteractionCommonHHScaleInvariant ≡ true
literalVorticityInteractionCommonHHScaleInvariantIsTrue = refl

literalEnstrophyProductionCommonHHScaleInvariantIsTrue :
  literalEnstrophyProductionCommonHHScaleInvariant ≡ true
literalEnstrophyProductionCommonHHScaleInvariantIsTrue = refl
