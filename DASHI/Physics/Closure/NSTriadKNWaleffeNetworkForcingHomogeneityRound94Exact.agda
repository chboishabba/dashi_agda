module DASHI.Physics.Closure.NSTriadKNWaleffeNetworkForcingHomogeneityRound94Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "The Regularity of Weak Solutions of the 3D Navier-Stokes Equations
-- in B^{-1}_{infinity,infinity}".
-- Archive for Rational Mechanics and Analysis 195 (2010), 159--169.
-- DOI: 10.1007/s00205-009-0265-2.
--
-- ROUND94 / HOMOGENEITY FALSIFICATION
--
-- Round94 derived the exact full-network Waleffe-amplitude tangent
--
--   dZ = -gamma Z + F_network.
--
-- The literal projected NS nonlinearity is quadratic.  Consequently, under a
-- real amplitude scaling u -> a u,
--
--   Z         -> a^3 Z,
--   F_network -> a^4 F_network.
--
-- This file proves those degree statements on the same finite physical
-- Galerkin carrier.  Therefore no amplitude-independent estimate of the form
-- |F_network| <= c gamma |Z| can follow from homogeneity alone.  A successful
-- occupation argument must use a normalized phase/coherence variable or a
-- genuine quartic cancellation/transfer identity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as PhysicalField
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as Tangent
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinWaleffeAmplitudeTangentRound94Exact as PhysicalTangent
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityQuadraticHomogeneityRound94Exact as Quadratic

realScalar :
  ∀ {r} (F : C3.RealField r) → C3.Carrier F → C3.Complex F
realScalar = C3.realEmbed

cubeScalar :
  ∀ {r} {F : C3.RealField r} → C3.Complex F → C3.Complex F
cubeScalar scalar =
  C3.complexMultiply (C3.complexMultiply scalar scalar) scalar

fourthScalar :
  ∀ {r} {F : C3.RealField r} → C3.Complex F → C3.Complex F
fourthScalar scalar =
  C3.complexMultiply (Quadratic.squareScalar scalar)
    (Quadratic.squareScalar scalar)

scaledPhysicalSystem :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F →
  PhysicalField.PhysicalFiniteComplex3GalerkinSystem F →
  PhysicalField.PhysicalFiniteComplex3GalerkinSystem F
scaledPhysicalSystem {F = F} amplitude physicalSystem = record
  { PhysicalField.physicalEmbedding = PhysicalField.physicalEmbedding physicalSystem
  ; PhysicalField.physicalInverseSquare = PhysicalField.physicalInverseSquare physicalSystem
  ; PhysicalField.finiteSystem =
      Quadratic.scaleSystem (realScalar F amplitude)
        (PhysicalField.finiteSystem physicalSystem)
  ; PhysicalField.viscosity = PhysicalField.viscosity physicalSystem
  ; PhysicalField.retainedModeNonzero =
      PhysicalField.retainedModeNonzero physicalSystem
  ; PhysicalField.retainedVelocityTransverse = transverseScaled
  }
  where
  scalar = realScalar F amplitude

  transverseScaled : ∀ mode →
    mode Cube.∈ Audit.modes (PhysicalField.finiteSystem physicalSystem) →
    C3.bilinearDot3
      (C3.modeVector
        (Audit.integerEmbedding (PhysicalField.finiteSystem physicalSystem)) mode)
      (C3.complex3Scale scalar
        (Audit.velocityAt (PhysicalField.finiteSystem physicalSystem) mode))
    ≡ C3.complexZero F
  transverseScaled mode member =
    trans
      (Scaling.bilinearDot3ScaleRight scalar
        (C3.modeVector
          (Audit.integerEmbedding (PhysicalField.finiteSystem physicalSystem)) mode)
        (Audit.velocityAt (PhysicalField.finiteSystem physicalSystem) mode))
      (trans
        (cong (C3.complexMultiply scalar)
          (PhysicalField.retainedVelocityTransverse physicalSystem mode member))
        (Algebra.complexMultiplyZeroRight scalar))

crossTwoScaled :
  ∀ {r} {F : C3.RealField r}
    (scalar : C3.Complex F) (u v : C3.Complex3 F) →
  DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact.complex3Cross
    (C3.complex3Scale scalar u) (C3.complex3Scale scalar v)
  ≡
  C3.complex3Scale (Quadratic.squareScalar scalar)
    (DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact.complex3Cross u v)
crossTwoScaled scalar u v =
  trans
    (Tangent.crossScaleLeft scalar u (C3.complex3Scale scalar v))
    (trans
      (cong (C3.complex3Scale scalar)
        (Tangent.crossScaleRight scalar u v))
      (Quadratic.nestedScale scalar scalar
        (DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact.complex3Cross u v)))

realScalarConjugate :
  ∀ {r} {F : C3.RealField r} (a : C3.Carrier F) →
  C3.complexConjugate (realScalar F a) ≡ realScalar F a
realScalarConjugate {F = F} a = C3.realEmbedConjugate F a

amplitudeCubicHomogeneous :
  ∀ {r} {F : C3.RealField r}
    (a : C3.Carrier F)
    (uK uP uQ : C3.Complex3 F) →
  Tangent.complexAmplitude
    (C3.complex3Scale (realScalar F a) uK)
    (C3.complex3Scale (realScalar F a) uP)
    (C3.complex3Scale (realScalar F a) uQ)
  ≡
  C3.complexMultiply (cubeScalar (realScalar F a))
    (Tangent.complexAmplitude uK uP uQ)
amplitudeCubicHomogeneous {F = F} a uK uP uQ =
  let
    s = realScalar F a
    cross =
      DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact.complex3Cross uP uQ
    Z = Tangent.complexAmplitude uK uP uQ
  in
  trans
    (cong (C3.hermitianPairing3 (C3.complex3Scale s uK))
      (crossTwoScaled s uP uQ))
    (trans
      (Scaling.hermitianPairingScaleLeft s uK
        (C3.complex3Scale (Quadratic.squareScalar s) cross))
      (trans
        (cong
          (λ conjugateS →
            C3.complexMultiply conjugateS
              (C3.hermitianPairing3 uK
                (C3.complex3Scale (Quadratic.squareScalar s) cross)))
          (realScalarConjugate a))
        (trans
          (cong (C3.complexMultiply s)
            (Scaling.hermitianPairingScaleRight
              (Quadratic.squareScalar s) uK cross))
          (R.solve 2
            (λ s Z → s R.⊗ ((s R.⊗ s) R.⊗ Z)
              R.⊜ ((s R.⊗ s) R.⊗ s) R.⊗ Z)
            refl s Z))))
  where module R = Ring.Solver F

networkForcingFourthHomogeneousGeneral :
  ∀ {r} {F : C3.RealField r}
    (a : C3.Carrier F)
    (uK uP uQ fK fP fQ : C3.Complex3 F) →
  Tangent.networkForcing
    (C3.complex3Scale (realScalar F a) uK)
    (C3.complex3Scale (realScalar F a) uP)
    (C3.complex3Scale (realScalar F a) uQ)
    (C3.complex3Scale (Quadratic.squareScalar (realScalar F a)) fK)
    (C3.complex3Scale (Quadratic.squareScalar (realScalar F a)) fP)
    (C3.complex3Scale (Quadratic.squareScalar (realScalar F a)) fQ)
  ≡
  C3.complexMultiply (fourthScalar (realScalar F a))
    (Tangent.networkForcing uK uP uQ fK fP fQ)
networkForcingFourthHomogeneousGeneral {F = F} a uK uP uQ fK fP fQ =
  let
    s = realScalar F a
    s2 = Quadratic.squareScalar s
    s4 = fourthScalar s
    crossPQ = DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact.complex3Cross uP uQ
    crossFK = DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact.complex3Cross fP uQ
    crossFQ = DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact.complex3Cross uP fQ
    FK = C3.hermitianPairing3 fK crossPQ
    FP = C3.hermitianPairing3 uK crossFK
    FQ = C3.hermitianPairing3 uK crossFQ

    firstSlot :
      C3.hermitianPairing3 (C3.complex3Scale s2 fK)
        (DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact.complex3Cross
          (C3.complex3Scale s uP) (C3.complex3Scale s uQ))
      ≡ C3.complexMultiply s4 FK
    firstSlot =
      trans
        (cong (C3.hermitianPairing3 (C3.complex3Scale s2 fK))
          (crossTwoScaled s uP uQ))
        (trans
          (Scaling.hermitianPairingScaleLeft s2 fK
            (C3.complex3Scale s2 crossPQ))
          (trans
            (cong
              (λ selected → C3.complexMultiply selected
                (C3.hermitianPairing3 fK (C3.complex3Scale s2 crossPQ)))
              (C3.realEmbedConjugate F
                (C3.multiply F a a)))
            (trans
              (cong (C3.complexMultiply s2)
                (Scaling.hermitianPairingScaleRight s2 fK crossPQ))
              (R.solve 3
                (λ s2 s4 value → s2 R.⊗ (s2 R.⊗ value)
                  R.⊜ s4 R.⊗ value)
                scalarSquareFourth s2 s4 FK))))

    secondCross :
      DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact.complex3Cross
        (C3.complex3Scale s2 fP) (C3.complex3Scale s uQ)
      ≡ C3.complex3Scale (C3.complexMultiply s2 s) crossFK
    secondCross =
      trans
        (Tangent.crossScaleLeft s2 fP (C3.complex3Scale s uQ))
        (trans
          (cong (C3.complex3Scale s2)
            (Tangent.crossScaleRight s fP uQ))
          (Quadratic.nestedScale s2 s crossFK))

    secondSlot :
      C3.hermitianPairing3 (C3.complex3Scale s uK)
        (DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact.complex3Cross
          (C3.complex3Scale s2 fP) (C3.complex3Scale s uQ))
      ≡ C3.complexMultiply s4 FP
    secondSlot =
      trans
        (cong (C3.hermitianPairing3 (C3.complex3Scale s uK)) secondCross)
        (trans
          (Scaling.hermitianPairingScaleLeft s uK
            (C3.complex3Scale (C3.complexMultiply s2 s) crossFK))
          (trans
            (cong
              (λ selected → C3.complexMultiply selected
                (C3.hermitianPairing3 uK
                  (C3.complex3Scale (C3.complexMultiply s2 s) crossFK)))
              (realScalarConjugate a))
            (trans
              (cong (C3.complexMultiply s)
                (Scaling.hermitianPairingScaleRight
                  (C3.complexMultiply s2 s) uK crossFK))
              (R.solve 3
                (λ s s2 value → s R.⊗ ((s2 R.⊗ s) R.⊗ value)
                  R.⊜ ((s2 R.⊗ s2) R.⊗ value))
                scalarSquare s s2 FP))))

    thirdCross :
      DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact.complex3Cross
        (C3.complex3Scale s uP) (C3.complex3Scale s2 fQ)
      ≡ C3.complex3Scale (C3.complexMultiply s s2) crossFQ
    thirdCross =
      trans
        (Tangent.crossScaleLeft s uP (C3.complex3Scale s2 fQ))
        (trans
          (cong (C3.complex3Scale s)
            (Tangent.crossScaleRight s2 uP fQ))
          (Quadratic.nestedScale s s2 crossFQ))

    thirdSlot :
      C3.hermitianPairing3 (C3.complex3Scale s uK)
        (DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact.complex3Cross
          (C3.complex3Scale s uP) (C3.complex3Scale s2 fQ))
      ≡ C3.complexMultiply s4 FQ
    thirdSlot =
      trans
        (cong (C3.hermitianPairing3 (C3.complex3Scale s uK)) thirdCross)
        (trans
          (Scaling.hermitianPairingScaleLeft s uK
            (C3.complex3Scale (C3.complexMultiply s s2) crossFQ))
          (trans
            (cong
              (λ selected → C3.complexMultiply selected
                (C3.hermitianPairing3 uK
                  (C3.complex3Scale (C3.complexMultiply s s2) crossFQ)))
              (realScalarConjugate a))
            (trans
              (cong (C3.complexMultiply s)
                (Scaling.hermitianPairingScaleRight
                  (C3.complexMultiply s s2) uK crossFQ))
              (R.solve 3
                (λ s s2 value → s R.⊗ ((s R.⊗ s2) R.⊗ value)
                  R.⊜ ((s2 R.⊗ s2) R.⊗ value))
                scalarSquare s s2 FQ))))

    slots = cong₂ C3.complexAdd (cong₂ C3.complexAdd firstSlot secondSlot) thirdSlot
  in
  trans slots
    (sym
      (Ring.complexDistributeLeft s4
        (C3.complexAdd FK FP) FQ))
  where
  module R = Ring.Solver F
  s = realScalar F a
  s2 = Quadratic.squareScalar s
  s4 = fourthScalar s

  scalarSquare : C3.complexMultiply s s ≡ s2
  scalarSquare = refl

  scalarSquareFourth : C3.complexMultiply s2 s2 ≡ s4
  scalarSquareFourth = refl

physicalNetworkForcingFourthHomogeneous :
  ∀ {r} {F : C3.RealField r}
    (a : C3.Carrier F)
    (physicalSystem : PhysicalField.PhysicalFiniteComplex3GalerkinSystem F)
    (tau : Physical.PhysicalTriadIncidence) →
  PhysicalTangent.physicalTriadNetworkForcing
    (scaledPhysicalSystem a physicalSystem) tau
  ≡
  C3.complexMultiply (fourthScalar (realScalar F a))
    (PhysicalTangent.physicalTriadNetworkForcing physicalSystem tau)
physicalNetworkForcingFourthHomogeneous {F = F} a physicalSystem tau =
  let
    s = realScalar F a
    baseSystem = PhysicalField.finiteSystem physicalSystem
    k = Physical.k tau
    p = Physical.p tau
    q = Physical.q tau
    uK = Audit.velocityAt baseSystem k
    uP = Audit.velocityAt baseSystem p
    uQ = Audit.velocityAt baseSystem q
    fK = Audit.projectedNonlinearity baseSystem k
    fP = Audit.projectedNonlinearity baseSystem p
    fQ = Audit.projectedNonlinearity baseSystem q
  in
  trans
    (cong₂
      (Tangent.networkForcing
        (C3.complex3Scale s uK)
        (C3.complex3Scale s uP)
        (C3.complex3Scale s uQ))
      (cong₂ _,_
        (Quadratic.projectedNonlinearityQuadraticHomogeneous baseSystem s k)
        (Quadratic.projectedNonlinearityQuadraticHomogeneous baseSystem s p))
      (Quadratic.projectedNonlinearityQuadraticHomogeneous baseSystem s q))
    (networkForcingFourthHomogeneousGeneral a uK uP uQ fK fP fQ)

round94WaleffeAmplitudeCubicHomogeneityClosed : Bool
round94WaleffeAmplitudeCubicHomogeneityClosed = true

round94NetworkForcingQuarticHomogeneityClosed : Bool
round94NetworkForcingQuarticHomogeneityClosed = true

round94RawAmplitudeUniformDampingRouteRejected : Bool
round94RawAmplitudeUniformDampingRouteRejected = true

round94WaleffeAmplitudeCubicHomogeneityClosedIsTrue :
  round94WaleffeAmplitudeCubicHomogeneityClosed ≡ true
round94WaleffeAmplitudeCubicHomogeneityClosedIsTrue = refl

round94NetworkForcingQuarticHomogeneityClosedIsTrue :
  round94NetworkForcingQuarticHomogeneityClosed ≡ true
round94NetworkForcingQuarticHomogeneityClosedIsTrue = refl

round94RawAmplitudeUniformDampingRouteRejectedIsTrue :
  round94RawAmplitudeUniformDampingRouteRejected ≡ true
round94RawAmplitudeUniformDampingRouteRejectedIsTrue = refl
