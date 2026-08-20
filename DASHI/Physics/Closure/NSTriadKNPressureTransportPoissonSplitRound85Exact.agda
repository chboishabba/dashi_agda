module DASHI.Physics.Closure.NSTriadKNPressureTransportPoissonSplitRound85Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Marco Cannone.
-- Title: "Harmonic Analysis Tools for Solving the Incompressible
-- Navier-Stokes Equations".
-- DOI: 10.1016/S1874-5792(05)80006-0.
--
-- Authors: Jinhee Jeong; Fazle Hussain.
-- Title: "On the identification of a vortex".
-- DOI: 10.1017/S0022112095000462.
--
-- Authors: J. C. R. Hunt; A. A. Wray; P. Moin.
-- Title: "Eddies, streams, and convergence zones in turbulent flows".
-- Center for Turbulence Research, Proceedings of the 1988 Summer Program.
-- NASA NTRS: 19890015184. DOI: not assigned in the cited report record.
--
-- ROUND85 / PRESSURE-AS-TRANSPORT LEG = RELOCATED DERIVATIVE + POISSON SOURCE
--
-- The remaining mixed term after the Hessian split is B(P,u).  On one
-- resonant triad p+q=k, with
--
--   P_p = - i p pHat_p,
--
-- its scalar coefficient contains
--
--   - pHat_p (p dot q).
--
-- Resonance gives exactly
--
--   p dot q = p dot k - |p|^2,
--
-- hence
--
--   -pHat_p (p dot q)
--     = -pHat_p (p dot k) + |p|^2 pHat_p.
--
-- The second term is the Fourier coefficient of -Delta p, i.e. the pressure
-- Poisson source and therefore -2Q in the Round85 Q convention.  The first is
-- the derivative relocated onto the selected/test packet and is the exact
-- localization/commutator residual that periodic mean-Q zero does not remove.
--
-- This file proves that split on the literal C3 Fourier carrier and lifts it
-- over the physical output fibre.  Combined with the companion Hessian file,
-- DN(u)[P] is therefore a THREE-WAY exact sum:
--
--   pressure-Hessian fold
--   + relocated packet-derivative fold
--   + pressure-Poisson/Q-source fold.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as CRing
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNLerayOutputTransversalityRound30Exact as LerayOut
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as LerayLin
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityFirstVariationRound82Exact as First
import DASHI.Physics.Closure.NSTriadKNLiteralAdvectivePressureRHSSplitRound84Exact as AP
import DASHI.Physics.Closure.NSTriadKNPressurePotentialGradientHessianSameModeRound85Exact as Potential
import DASHI.Physics.Closure.NSTriadKNDNPressureHessianTransportSplitRound85Exact as HessianSplit

modeDot :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Z3.FourierMode → Z3.FourierMode → C3.Complex F
modeDot E left right =
  C3.bilinearDot3 (C3.modeVector E left) (C3.modeVector E right)

modeDotOutputSplitsOnResonance :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    {p q k : Z3.FourierMode} →
  Z3.addMode p q ≡ k →
  modeDot E p k
  ≡ C3.complexAdd (modeDot E p p) (modeDot E p q)
modeDotOutputSplitsOnResonance E {p} {q} {k} resonance =
  trans
    (cong
      (C3.bilinearDot3 (C3.modeVector E p))
      (sym (cong (C3.modeVector E) resonance)))
    (trans
      (cong
        (C3.bilinearDot3 (C3.modeVector E p))
        (Algebra.modeVectorAdd E p q))
      (Algebra.bilinearDot3RightAdd
        (C3.modeVector E p) (C3.modeVector E p) (C3.modeVector E q)))

modeDotInputSplit :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    {p q k : Z3.FourierMode} →
  Z3.addMode p q ≡ k →
  modeDot E p q
  ≡ C3.complexSubtract (modeDot E p k) (modeDot E p p)
modeDotInputSplit {F = F} E {p} {q} {k} resonance =
  let
    pp = modeDot E p p
    pq = modeDot E p q
    pk = modeDot E p k
    pkSplit = modeDotOutputSplitsOnResonance E resonance
  in
  trans
    (C.solve 2
      (λ self input →
        input C.⊜ ((self C.⊕ input) C.⊕ C.⊝ self))
      refl pp pq)
    (cong
      (λ total → C3.complexSubtract total pp)
      (sym pkSplit))
  where module C = CRing.Solver F

------------------------------------------------------------------------
-- Scalar coefficient of the literal B(P,u) ordered interaction.
------------------------------------------------------------------------

pressureTransportTotalScalar :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex F
pressureTransportTotalScalar {F = F} {E = E}
    system incidence =
  let
    p = Physical.p incidence
    q = Physical.q incidence
    pHat = Potential.pressurePotential system p
    pressureScalar = C3.complexMultiply (Potential.minusI F) pHat
    derivative = C3.complexMultiply pressureScalar (modeDot E p q)
  in
  C3.complexMultiply (Potential.minusI F) derivative

pressureRelocatedScalar :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex F
pressureRelocatedScalar {F = F} {E = E} system incidence =
  C3.complexNegate
    (C3.complexMultiply
      (Potential.pressurePotential system (Physical.p incidence))
      (modeDot E (Physical.p incidence) (Physical.k incidence)))

pressurePoissonScalar :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex F
pressurePoissonScalar {F = F} {E = E} system incidence =
  C3.complexMultiply
    (Potential.pressurePotential system (Physical.p incidence))
    (modeDot E (Physical.p incidence) (Physical.p incidence))

pressureTransportScalarSplitsRelocatedPoisson :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidence : Physical.PhysicalTriadIncidence) →
  pressureTransportTotalScalar system incidence
  ≡ C3.complexAdd
      (pressureRelocatedScalar system incidence)
      (pressurePoissonScalar system incidence)
pressureTransportScalarSplitsRelocatedPoisson {F = F} {E = E}
    system incidence =
  let
    p = Physical.p incidence
    q = Physical.q incidence
    k = Physical.k incidence
    pHat = Potential.pressurePotential system p
    pp = modeDot E p p
    pq = modeDot E p q
    pk = modeDot E p k
    m = Potential.minusI F
  in
  trans
    (C.solve 3
      (λ m pHat pq →
        (m C.⊗ ((m C.⊗ pHat) C.⊗ pq))
        C.⊜ ((m C.⊗ m) C.⊗ (pHat C.⊗ pq)))
      refl m pHat pq)
    (trans
      (cong
        (λ square → C3.complexMultiply square
          (C3.complexMultiply pHat pq))
        (Potential.minusISquared F))
      (trans
        (Additive.complexMultiplyMinusOneLeft
          (C3.complexMultiply pHat pq))
        (trans
          (cong
            (λ input → C3.complexNegate
              (C3.complexMultiply pHat input))
            (modeDotInputSplit E (Physical.resonance incidence)))
          (C.solve 3
            (λ pHat pk pp →
              (C.⊝ (pHat C.⊗ (pk C.⊕ C.⊝ pp)))
              C.⊜ ((C.⊝ (pHat C.⊗ pk)) C.⊕ (pHat C.⊗ pp)))
            refl pHat pk pp))))
  where module C = CRing.Solver F

------------------------------------------------------------------------
-- The Poisson term really is |p|^2 pHat = -Delta pHat.
------------------------------------------------------------------------

pressurePoissonSourceCoefficient :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → C3.Complex F
pressurePoissonSourceCoefficient {F = F} {I = I} system mode =
  C3.complexMultiply
    (Potential.pressurePotential system mode)
    (C3.realEmbed F (C3.normSquared I mode))

pressurePoissonScalarIsSourceCoefficient :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidence : Physical.PhysicalTriadIncidence) →
  pressurePoissonScalar system incidence
  ≡ pressurePoissonSourceCoefficient system (Physical.p incidence)
pressurePoissonScalarIsSourceCoefficient {F = F} {E = E} {I = I}
    system incidence =
  cong
    (C3.complexMultiply
      (Potential.pressurePotential system (Physical.p incidence)))
    (LerayOut.modeSelfDotIsEmbeddedNormSquared
      E I (Physical.p incidence))

------------------------------------------------------------------------
-- Ordered vector split and finite output-fibre lift.
------------------------------------------------------------------------

pressureRelocatedOrderedTerm :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
pressureRelocatedOrderedTerm {E = E} {I = I} system incidence =
  C3.lerayProject3 E I (Physical.k incidence)
    (C3.complex3Scale
      (pressureRelocatedScalar system incidence)
      (Audit.velocity system (Physical.q incidence)))

pressurePoissonOrderedTerm :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
pressurePoissonOrderedTerm {E = E} {I = I} system incidence =
  C3.lerayProject3 E I (Physical.k incidence)
    (C3.complex3Scale
      (pressurePoissonScalar system incidence)
      (Audit.velocity system (Physical.q incidence)))

orderedPressureTransportSplitsRelocatedPoisson :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidence : Physical.PhysicalTriadIncidence) →
  First.mixedProjectedOrderedTerm
    system (AP.pressureNonlinearity system) (Audit.velocity system) incidence
  ≡ C3.complex3Add
      (pressureRelocatedOrderedTerm system incidence)
      (pressurePoissonOrderedTerm system incidence)
orderedPressureTransportSplitsRelocatedPoisson {F = F} {E = E} {I = I}
    system incidence =
  let
    k = Physical.k incidence
    p = Physical.p incidence
    q = Physical.q incidence
    pHat = Potential.pressurePotential system p
    pressureScalar = C3.complexMultiply (Potential.minusI F) pHat
    derivativeFactor =
      C3.bilinearDot3 (AP.pressureNonlinearity system p) (C3.modeVector E q)
    total = pressureTransportTotalScalar system incidence
    relocated = pressureRelocatedScalar system incidence
    source = pressurePoissonScalar system incidence
  in
  trans
    (cong
      (λ pressureP →
        C3.complex3Scale (Potential.minusI F)
          (C3.lerayProject3 E I k
            (C3.complex3Scale
              (C3.bilinearDot3 pressureP (C3.modeVector E q))
              (Audit.velocity system q))))
      (Potential.pressureNonlinearityIsNegativeGradientOfPotential system p))
    (trans
      (cong
        (λ derivative →
          C3.complex3Scale (Potential.minusI F)
            (C3.lerayProject3 E I k
              (C3.complex3Scale derivative (Audit.velocity system q))))
        (Scaling.bilinearDot3ScaleLeft
          pressureScalar (C3.modeVector E p) (C3.modeVector E q)))
      (trans
        (cong
          (C3.complex3Scale (Potential.minusI F))
          (LerayLin.lerayProjectComplexScale
            E I k
            (C3.complexMultiply pressureScalar (modeDot E p q))
            (Audit.velocity system q)))
        (trans
          (Potential.complex3ScaleCompose
            (Potential.minusI F)
            (C3.complexMultiply pressureScalar (modeDot E p q))
            (C3.lerayProject3 E I k (Audit.velocity system q)))
          (trans
            (cong
              (λ scalar → C3.complex3Scale scalar
                (C3.lerayProject3 E I k (Audit.velocity system q)))
              (pressureTransportScalarSplitsRelocatedPoisson system incidence))
            (trans
              (First.complex3ScaleScalarAdd relocated source
                (C3.lerayProject3 E I k (Audit.velocity system q)))
              (cong₂ C3.complex3Add
                (sym (LerayLin.lerayProjectComplexScale
                  E I k relocated (Audit.velocity system q)))
                (sym (LerayLin.lerayProjectComplexScale
                  E I k source (Audit.velocity system q)))))))))

mapPressureRelocatedTerms :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  List Physical.PhysicalTriadIncidence → List (C3.Complex3 F)
mapPressureRelocatedTerms system [] = []
mapPressureRelocatedTerms system (incidence ∷ rest) =
  pressureRelocatedOrderedTerm system incidence
  ∷ mapPressureRelocatedTerms system rest

mapPressurePoissonTerms :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  List Physical.PhysicalTriadIncidence → List (C3.Complex3 F)
mapPressurePoissonTerms system [] = []
mapPressurePoissonTerms system (incidence ∷ rest) =
  pressurePoissonOrderedTerm system incidence
  ∷ mapPressurePoissonTerms system rest

sumPressureTransportSplits :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidences : List Physical.PhysicalTriadIncidence) →
  Audit.sumVectors
    (First.mixedTerms system
      (AP.pressureNonlinearity system) (Audit.velocity system) incidences)
  ≡ C3.complex3Add
      (Audit.sumVectors (mapPressureRelocatedTerms system incidences))
      (Audit.sumVectors (mapPressurePoissonTerms system incidences))
sumPressureTransportSplits {F = F} system [] =
  sym (First.complex3AddZeroLeft (C3.complex3Zero F))
sumPressureTransportSplits system (incidence ∷ rest) =
  trans
    (cong₂ C3.complex3Add
      (orderedPressureTransportSplitsRelocatedPoisson system incidence)
      (sumPressureTransportSplits system rest))
    (First.complex3Interchange
      (pressureRelocatedOrderedTerm system incidence)
      (pressurePoissonOrderedTerm system incidence)
      (Audit.sumVectors (mapPressureRelocatedTerms system rest))
      (Audit.sumVectors (mapPressurePoissonTerms system rest)))

pressureRelocatedFold :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → C3.Complex3 F
pressureRelocatedFold system output =
  Audit.sumVectors
    (mapPressureRelocatedTerms system (Audit.concreteTriadsAt system output))

pressurePoissonFold :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → C3.Complex3 F
pressurePoissonFold system output =
  Audit.sumVectors
    (mapPressurePoissonTerms system (Audit.concreteTriadsAt system output))

pressureTransportVariationSplitsRelocatedPoisson :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    output →
  HessianSplit.pressureTransportVariation system output
  ≡ C3.complex3Add
      (pressureRelocatedFold system output)
      (pressurePoissonFold system output)
pressureTransportVariationSplitsRelocatedPoisson system output =
  sumPressureTransportSplits
    system (Audit.concreteTriadsAt system output)

projectedNonlinearityPressureVariationThreeWay :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    output →
  First.projectedNonlinearityFirstVariation
    system (AP.pressureNonlinearity system) output
  ≡ C3.complex3Add
      (HessianSplit.pressureHessianFold system output)
      (C3.complex3Add
        (pressureRelocatedFold system output)
        (pressurePoissonFold system output))
projectedNonlinearityPressureVariationThreeWay system output =
  trans
    (HessianSplit.projectedNonlinearityPressureVariationSplitsHessianTransport
      system output)
    (cong
      (C3.complex3Add (HessianSplit.pressureHessianFold system output))
      (pressureTransportVariationSplitsRelocatedPoisson system output))

round85PressureTransportSplitsRelocatedAndPoisson : Bool
round85PressureTransportSplitsRelocatedAndPoisson = true

round85PressurePoissonTermIsLiteralMinusLaplacianSource : Bool
round85PressurePoissonTermIsLiteralMinusLaplacianSource = true

round85DNPressureVariationThreeWayConstructed : Bool
round85DNPressureVariationThreeWayConstructed = true

round85RelocatedPressurePacketDerivativeAbsorbed : Bool
round85RelocatedPressurePacketDerivativeAbsorbed = false

round85DNPressureVariationThreeWayConstructedIsTrue :
  round85DNPressureVariationThreeWayConstructed ≡ true
round85DNPressureVariationThreeWayConstructedIsTrue = refl
