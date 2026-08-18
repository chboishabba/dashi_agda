module DASHI.Physics.Closure.NSTriadKNPressureTransportAdjointDivergenceDefectRound85Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Jinhee Jeong; Fazle Hussain.
-- Title: "On the identification of a vortex".
-- DOI: 10.1017/S0022112095000462.
--
-- ROUND85 / TRANSPORT ADJOINT DEFECT = DIVERGENCE; PRESSURE DEFECT = -h
--
-- Round40 proved exact skew-adjoint transport when the advector is
-- divergence-free.  Here we keep the divergence term instead of setting it to
-- zero.  For a real advector coefficient a_m and resonance
--
--   m + q = k,
--
-- with transport coefficients
--
--   c(k,q) = i (q . a_m),
--   c(q,k) = i (k . a_-m),
--
-- reality gives exactly
--
--   conjugate(c(q,k)) + c(k,q) = - i (m . a_m).
--
-- Thus the symmetric part of transport is precisely its divergence defect.
-- For the Round85 pressure direction
--
--   P_m = - i m pHat_m,
--
-- the right side is
--
--   - i (m . P_m) = - |m|^2 pHat_m = - h_m,
--
-- where h=-Delta p=-2Q is the literal same-object Poisson source.
--
-- This is the finite-Fourier integration-by-parts identity behind the
-- principal packet pressure operator.  No continuum integration authority is
-- used and no shell summation is asserted here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as CRing
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLerayOutputTransversalityRound30Exact as LerayOut
import DASHI.Physics.Closure.NSTriadKNPhysicalTransportCoefficientSkewRound40Exact as Transport
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Galerkin
import DASHI.Physics.Closure.NSTriadKNLiteralAdvectivePressureRHSSplitRound84Exact as AP
import DASHI.Physics.Closure.NSTriadKNPressurePotentialGradientHessianSameModeRound85Exact as Potential
import DASHI.Physics.Closure.NSTriadKNPressureTransportPoissonSplitRound85Exact as Poisson

------------------------------------------------------------------------
-- Generic real-advector adjoint defect, without divergence-free assumption.
------------------------------------------------------------------------

record ResonantRealAdvector
    {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (advector input output : Z3.FourierMode) : Set r where
  field
    coefficient : C3.Complex3 F
    negativeCoefficient : C3.Complex3 F
    resonance : Z3.addMode advector input ≡ output
    reality : negativeCoefficient ≡ C3.complex3Conjugate coefficient

open ResonantRealAdvector public

forwardCoefficient :
  ∀ {r F E advector input output} →
  ResonantRealAdvector {r} {F} E advector input output → C3.Complex F
forwardCoefficient {E = E} {input = input} witness =
  Transport.transportCoefficient E input (coefficient witness)

reverseCoefficient :
  ∀ {r F E advector input output} →
  ResonantRealAdvector {r} {F} E advector input output → C3.Complex F
reverseCoefficient {E = E} {output = output} witness =
  Transport.transportCoefficient E output (negativeCoefficient witness)

divergenceDefect :
  ∀ {r F E advector input output} →
  ResonantRealAdvector {r} {F} E advector input output → C3.Complex F
divergenceDefect {F = F} {E = E} {advector = advector} witness =
  C3.complexMultiply
    (C3.complexNegate (C3.complexI F))
    (Transport.modeDot E advector (coefficient witness))

transportAdjointDefectExact :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {advector input output : Z3.FourierMode}
    (witness : ResonantRealAdvector E advector input output) →
  C3.complexAdd
    (C3.complexConjugate (reverseCoefficient witness))
    (forwardCoefficient witness)
  ≡ divergenceDefect witness
transportAdjointDefectExact {F = F} {E = E}
    {advector} {input} {output} witness =
  let
    conjugateReverseDot :
      C3.complexConjugate
        (Transport.modeDot E output (negativeCoefficient witness))
      ≡ Transport.modeDot E output (coefficient witness)
    conjugateReverseDot =
      trans
        (cong
          (λ selected →
            C3.complexConjugate (Transport.modeDot E output selected))
          (reality witness))
        (Transport.conjugateModeDotConjugateValue
          E output (coefficient witness))

    outputDotSplit :
      Transport.modeDot E output (coefficient witness)
      ≡ C3.complexAdd
          (Transport.modeDot E advector (coefficient witness))
          (Transport.modeDot E input (coefficient witness))
    outputDotSplit =
      trans
        (cong
          (λ selected → Transport.modeDot E selected (coefficient witness))
          (sym (resonance witness)))
        (Transport.modeDotAdd E advector input (coefficient witness))
  in
  trans
    (cong
      (λ reverse → C3.complexAdd reverse (forwardCoefficient witness))
      (trans
        (Algebra.complexConjugateMultiply
          (C3.complexI F)
          (Transport.modeDot E output (negativeCoefficient witness)))
        (cong₂ C3.complexMultiply
          (Transport.conjugateImaginaryUnitIsNegative F)
          conjugateReverseDot)))
    (trans
      (cong
        (λ outputDot →
          C3.complexAdd
            (C3.complexMultiply
              (C3.complexNegate (C3.complexI F)) outputDot)
            (C3.complexMultiply
              (C3.complexI F)
              (Transport.modeDot E input (coefficient witness))))
        outputDotSplit)
      (C.solve 3
        (λ i div inputDot →
          (((C.⊝ i) C.⊗ (div C.⊕ inputDot))
            C.⊕ (i C.⊗ inputDot))
          C.⊜ ((C.⊝ i) C.⊗ div))
        refl
        (C3.complexI F)
        (Transport.modeDot E advector (coefficient witness))
        (Transport.modeDot E input (coefficient witness))))
  where
  module C = CRing.Solver F

------------------------------------------------------------------------
-- Pressure specialization: defect is minus the literal Poisson source.
------------------------------------------------------------------------

pressureAdvectorWitness :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Galerkin.FiniteComplex3GalerkinSystem F E I)
    (advector input output : Z3.FourierMode) →
  Z3.addMode advector input ≡ output →
  Audit.RealityCondition (AP.pressureNonlinearity system) →
  ResonantRealAdvector E advector input output
pressureAdvectorWitness system advector input output resonance reality = record
  { coefficient = AP.pressureNonlinearity system advector
  ; negativeCoefficient = AP.pressureNonlinearity system (Z3.negateMode advector)
  ; resonance = resonance
  ; reality = reality advector
  }

pressureModeDivergence :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Galerkin.FiniteComplex3GalerkinSystem F E I)
    (mode : Z3.FourierMode) →
  C3.complexMultiply
    (Potential.minusI F)
    (Transport.modeDot E mode (AP.pressureNonlinearity system mode))
  ≡ C3.complexNegate
      (Poisson.pressurePoissonSourceCoefficient system mode)
pressureModeDivergence {F = F} {E = E} {I = I} system mode =
  let
    pHat = Potential.pressurePotential system mode
    mI = Potential.minusI F
    normC = C3.realEmbed F (C3.normSquared I mode)
    source = Poisson.pressurePoissonSourceCoefficient system mode

    modeDotPressure :
      Transport.modeDot E mode (AP.pressureNonlinearity system mode)
      ≡ C3.complexMultiply
          (C3.complexMultiply mI pHat) normC
    modeDotPressure =
      trans
        (cong
          (Transport.modeDot E mode)
          (Potential.pressureNonlinearityIsNegativeGradientOfPotential
            system mode))
        (trans
          (Algebra.bilinearDotCommutative
            (C3.modeVector E mode)
            (Potential.negativeGradient E mode pHat))
          (trans
            (Scaling.bilinearDot3ScaleRight
              (C3.complexMultiply mI pHat)
              (C3.modeVector E mode)
              (C3.modeVector E mode))
            (cong
              (C3.complexMultiply (C3.complexMultiply mI pHat))
              (LerayOut.modeSelfDotIsEmbeddedNormSquared E I mode))))

    regroup :
      C3.complexMultiply mI
        (C3.complexMultiply (C3.complexMultiply mI pHat) normC)
      ≡ C3.complexMultiply
          (C3.complexMultiply mI mI)
          (C3.complexMultiply pHat normC)
    regroup =
      C.solve 4
        (λ m p n dummy →
          (m C.⊗ ((m C.⊗ p) C.⊗ n))
          C.⊜ ((m C.⊗ m) C.⊗ (p C.⊗ n)))
        refl mI pHat normC (C3.complexOne F)

    sourceNegated :
      C3.complexMultiply
        (C3.complexNegate (C3.complexOne F))
        (C3.complexMultiply pHat normC)
      ≡ C3.complexNegate source
    sourceNegated =
      trans
        (Additive.complexMultiplyMinusOneLeft
          (C3.complexMultiply pHat normC))
        refl
  in
  trans
    (cong (C3.complexMultiply mI) modeDotPressure)
    (trans
      regroup
      (trans
        (cong
          (λ square →
            C3.complexMultiply square (C3.complexMultiply pHat normC))
          (Potential.minusISquared F))
        sourceNegated))
  where
  module C = CRing.Solver F

pressureTransportAdjointDefectIsMinusPoissonSource :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Galerkin.FiniteComplex3GalerkinSystem F E I)
    (advector input output : Z3.FourierMode)
    (resonance : Z3.addMode advector input ≡ output)
    (reality : Audit.RealityCondition (AP.pressureNonlinearity system)) →
  C3.complexAdd
    (C3.complexConjugate
      (reverseCoefficient
        (pressureAdvectorWitness system advector input output resonance reality)))
    (forwardCoefficient
      (pressureAdvectorWitness system advector input output resonance reality))
  ≡ C3.complexNegate
      (Poisson.pressurePoissonSourceCoefficient system advector)
pressureTransportAdjointDefectIsMinusPoissonSource
    system advector input output resonance reality =
  trans
    (transportAdjointDefectExact
      (pressureAdvectorWitness system advector input output resonance reality))
    (pressureModeDivergence system advector)

round85TransportAdjointDivergenceDefectConstructed : Bool
round85TransportAdjointDivergenceDefectConstructed = true

round85PressureTransportAdjointDefectIsMinusPoissonSource : Bool
round85PressureTransportAdjointDefectIsMinusPoissonSource = true

round85PressureTransportAdjointDefectIsMinusPoissonSourceIsTrue :
  round85PressureTransportAdjointDefectIsMinusPoissonSource ≡ true
round85PressureTransportAdjointDefectIsMinusPoissonSourceIsTrue = refl
