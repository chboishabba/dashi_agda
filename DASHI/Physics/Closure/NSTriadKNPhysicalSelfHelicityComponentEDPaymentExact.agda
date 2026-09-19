module DASHI.Physics.Closure.NSTriadKNPhysicalSelfHelicityComponentEDPaymentExact where

------------------------------------------------------------------------
-- PHYSICAL RETAINED HELICITY COMPONENT SELF-PHASE -> ED PAIR KERNEL
--
-- On the actual finite Galerkin system, project each retained input coefficient
-- to one helical sign.  R106 identifies the real self-phase pairing with
--
--   (signed radius_q - signed radius_p) * ||P_k(u_p^s x u_q^t)||^2.
--
-- The retained-mode signed-gap theorem bounds the first factor above by
-- |p|^2+|q|^2; R110 bounds the projected-cross square mass by E_p E_q.
-- The sign-robust ED kernel then yields
--
--   selfPhase_{s,t}(p,q) <= D_p E_q + E_p D_q
--
-- for every one of the four sign pairs.  No favourable-sign assumption,
-- absolute value, positive part, or pair-count factor is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _-_; -_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNComplex3EuclideanSelfPairing as SelfPair
import DASHI.Physics.Closure.NSTriadKNLiteralThreeLegWaleffeCommonAmplitudeRound93Exact as R93
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106Vector
import DASHI.Physics.Closure.NSTriadKNSelfWaleffePhaseProjectedCrossMassRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNProjectedCrossEnergyBoundRound110Exact as R110
import DASHI.Physics.Closure.NSTriadKNSignedSelfPhaseEDKernelExact as SignedED
import DASHI.Physics.Closure.NSTriadKNRetainedHelicalSignedGapEDExact as Gap

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalComponentED
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws
      F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem)
      S)
    (O : Leray.RationalInverseNormOrder
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem))
    (unitGap : Gap.R450.CanonicalFourierUnitGap physicalSystem)
    (radiusCalibration :
      Gap.R464.PhysicalSquareAndMHDCalibration
        (Field30.physicalEmbedding physicalSystem)
        (Field30.physicalInverseSquare physicalSystem)
        S)
    (orientation : Gap.R468.PhysicalRadiusOrientation S) where

  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem
  system = Field30.finiteSystem physicalSystem

  module G = Gap.PhysicalRetainedGap
    physicalSystem S unitGap radiusCalibration orientation

  velocity : Z3.FourierMode → C3.Complex3 F
  velocity = Audit.velocity system

  component :
    Helical.HelicitySign → Z3.FourierMode → C3.Complex3 F
  component sign mode =
    Helical.helicalProjector E I S sign mode (velocity mode)

  signedRadius : Helical.HelicitySign → Z3.FourierMode → ℚ
  signedRadius Helical.plus mode = Helical.modeNorm S mode
  signedRadius Helical.minus mode = - Helical.modeNorm S mode

  signedEigen :
    Helical.HelicitySign → Z3.FourierMode → C3.Complex F
  signedEigen sign mode = C3.realEmbed F (signedRadius sign mode)

  componentCurlEigen :
    (sign : Helical.HelicitySign) (mode : Z3.FourierMode) →
    Helical.curlSymbol E mode (component sign mode)
    ≡ C3.complex3Scale (signedEigen sign mode) (component sign mode)
  componentCurlEigen Helical.plus mode =
    Helical.helicalCurlEigenvaluePlus L mode (velocity mode)
  componentCurlEigen Helical.minus mode =
    Helical.helicalCurlEigenvalueMinus L mode (velocity mode)

  componentPairData :
    (tau : Physical.PhysicalTriadIncidence) →
    Z3.NonZeroMode (Physical.k tau) →
    (signP signQ : Helical.HelicitySign) →
    R106Vector.ProjectedHelicalPairData E I
      (Physical.p tau) (Physical.q tau) (Physical.k tau)
  componentPairData tau outputNonzero signP signQ =
    R106Vector.projected-helical-pair-data
      (Physical.resonance tau)
      outputNonzero
      (component signP (Physical.p tau))
      (component signQ (Physical.q tau))
      (signedEigen signP (Physical.p tau))
      (signedEigen signQ (Physical.q tau))
      (componentCurlEigen signP (Physical.p tau))
      (componentCurlEigen signQ (Physical.q tau))

  delta :
    Helical.HelicitySign → Helical.HelicitySign →
    Z3.FourierMode → Z3.FourierMode → ℚ
  delta signP signQ p q =
    signedRadius signQ q - signedRadius signP p

  deltaComplexMeaning :
    (signP signQ : Helical.HelicitySign) →
    (p q : Z3.FourierMode) →
    C3.complexSubtract
      (signedEigen signQ q)
      (signedEigen signP p)
    ≡ C3.realEmbed F (delta signP signQ p q)
  deltaComplexMeaning signP signQ p q =
    trans
      (R93.realEmbedSubtract
        (signedRadius signQ q)
        (signedRadius signP p))
      (cong (C3.realEmbed F)
        (solve
          (signedRadius signP p
          ∷ signedRadius signQ q
          ∷ [])))

  deltaComplexReal :
    (signP signQ : Helical.HelicitySign) →
    (p q : Z3.FourierMode) →
    C3.complexConjugate
      (C3.complexSubtract
        (signedEigen signQ q)
        (signedEigen signP p))
    ≡
    C3.complexSubtract
      (signedEigen signQ q)
      (signedEigen signP p)
  deltaComplexReal signP signQ p q =
    trans
      (cong C3.complexConjugate
        (deltaComplexMeaning signP signQ p q))
      (trans
        (C3.realEmbedConjugate F (delta signP signQ p q))
        (sym (deltaComplexMeaning signP signQ p q)))

  crossVector :
    (tau : Physical.PhysicalTriadIncidence) →
    (signP signQ : Helical.HelicitySign) →
    C3.Complex3 F
  crossVector tau signP signQ =
    Cross.complex3Cross
      (component signP (Physical.p tau))
      (component signQ (Physical.q tau))

  projectedCross :
    (tau : Physical.PhysicalTriadIncidence) →
    (signP signQ : Helical.HelicitySign) →
    C3.Complex3 F
  projectedCross tau signP signQ =
    C3.lerayProject3 E I (Physical.k tau)
      (crossVector tau signP signQ)

  selfPhaseReal :
    (tau : Physical.PhysicalTriadIncidence) →
    Z3.NonZeroMode (Physical.k tau) →
    (signP signQ : Helical.HelicitySign) →
    ℚ
  selfPhaseReal tau outputNonzero signP signQ =
    let H = componentPairData tau outputNonzero signP signQ
        X = crossVector tau signP signQ
        force =
          R106Vector.Signed.orderedPairVelocityInteraction
            (C3.complex3VelocityGalerkinLaws F E I)
            (Physical.k tau)
            (Physical.p tau)
            (Physical.q tau)
            (R106Vector.uP H)
            (R106Vector.uQ H)
    in
    C3.real (C3.hermitianPairing3 force X)

  selfPhaseRealMeaning :
    (tau : Physical.PhysicalTriadIncidence) →
    (outputNonzero : Z3.NonZeroMode (Physical.k tau)) →
    (signP signQ : Helical.HelicitySign) →
    selfPhaseReal tau outputNonzero signP signQ
    ≡
    delta signP signQ (Physical.p tau) (Physical.q tau)
      * Rational.squareMass (projectedCross tau signP signQ)
  selfPhaseRealMeaning tau outputNonzero signP signQ =
    let
      p = Physical.p tau
      q = Physical.q tau
      H = componentPairData tau outputNonzero signP signQ
      X = crossVector tau signP signQ
      PX = projectedCross tau signP signQ
      d = delta signP signQ p q
      phaseExact =
        R106.selfPhaseLegExact H
          (deltaComplexReal signP signQ p q)
      realExact = cong C3.real phaseExact
      scaled =
        R93.realOfRealScale d (C3.hermitianPairing3 PX PX)
      selfNorm =
        SelfPair.complex3SelfPairingRealPartIsNormSquared PX
    in
    trans realExact
      (trans
        (subst
          (λ scalar →
            C3.real
              (C3.complexMultiply scalar
                (C3.hermitianPairing3 PX PX))
            ≡ d * C3.real (C3.hermitianPairing3 PX PX))
          (deltaComplexMeaning signP signQ p q)
          scaled)
        (cong (d *_) selfNorm))

  componentEnergy :
    Helical.HelicitySign → Z3.FourierMode → ℚ
  componentEnergy sign mode =
    Rational.squareMass (component sign mode)

  componentDissipation :
    Helical.HelicitySign → Z3.FourierMode → ℚ
  componentDissipation sign mode =
    C3.normSquared I mode * componentEnergy sign mode

  selfPhaseComponentBelowED :
    (tau : Physical.PhysicalTriadIncidence) →
    (outputNonzero : Z3.NonZeroMode (Physical.k tau)) →
    (signP signQ : Helical.HelicitySign) →
    (pMember : Physical.p tau Cube.∈ Audit.modes system) →
    (qMember : Physical.q tau Cube.∈ Audit.modes system) →
    selfPhaseReal tau outputNonzero signP signQ
    ≤
    componentDissipation signP (Physical.p tau)
      * componentEnergy signQ (Physical.q tau)
      +
    componentEnergy signP (Physical.p tau)
      * componentDissipation signQ (Physical.q tau)
  selfPhaseComponentBelowED tau outputNonzero signP signQ pMember qMember =
    let
      p = Physical.p tau
      q = Physical.q tau
      uP = component signP p
      uQ = component signQ q
      PX = projectedCross tau signP signQ
      d = delta signP signQ p q
      p2 = C3.normSquared I p
      q2 = C3.normSquared I q
      eP = componentEnergy signP p
      eQ = componentEnergy signQ q
      m = Rational.squareMass PX

      p2NN = G.squareNN p
      q2NN = G.squareNN q
      ePNN = Rational.squareMassNonnegative uP
      eQNN = Rational.squareMassNonnegative uQ
      mNN = Rational.squareMassNonnegative PX

      dBound =
        G.signedGapBelowSquares signP signQ p q pMember qMember

      massBound =
        R110.projectedCrossNormSquaredBelowProduct
          E I O (Physical.k tau) uP uQ outputNonzero

      kernelBound =
        SignedED.signedSelfPhaseBelowEDKernel
          d p2 q2 eP eQ m
          p2NN q2NN ePNN eQNN mNN
          dBound massBound
    in
    subst
      (λ lower →
        lower
        ≤ (p2 * eP) * eQ + eP * (q2 * eQ))
      (sym (selfPhaseRealMeaning tau outputNonzero signP signQ))
      kernelBound
