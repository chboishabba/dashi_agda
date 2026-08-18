module DASHI.Physics.Closure.NSTriadKNDNPressureHessianTransportSplitRound85Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Authors: Dhawal Buaria; Alain Pumir.
-- Title: "Role of pressure in generation of intense velocity gradients in
-- turbulent flows".
-- DOI: 10.48550/arXiv.2308.03902.
--
-- ROUND85 / OPEN DN(u)[P] INTO HESSIAN WORK + PRESSURE TRANSPORT
--
-- The pressure tangent P is the literal negative gradient constructed by the
-- companion same-mode potential bridge.  The first variation is
--
--   DN(u)[P] = B(u,P) + B(P,u).
--
-- For every ordered triad k=p+q, inserting
--
--   P_q = - i q pHat_q
--
-- into the advected slot gives two Fourier derivative factors.  Exactly,
--
--   -i P_k [ (u_p dot q) P_q ]
--     = P_k [ H(q) u_p ],
--
-- where
--
--   H(q) u_p = - q (q dot u_p) pHat_q.
--
-- Thus B(u,P) is a literal projected pressure-Hessian fold.  The other mixed
-- term B(P,u), in which pressure is the TRANSPORT leg, remains explicit rather
-- than being hidden in the Hessian estimate.  Consequently
--
--   DN(u)[P] = HessianFold(u,p) + PressureTransportFold(p,u)
--
-- on the actual physical output fibre.  This identifies the precise remaining
-- C4 residual after the pressure-Hessian bridge.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as CRing
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as LerayLin
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityFirstVariationRound82Exact as First
import DASHI.Physics.Closure.NSTriadKNLiteralAdvectivePressureRHSSplitRound84Exact as AP
import DASHI.Physics.Closure.NSTriadKNPressurePotentialGradientHessianSameModeRound85Exact as Potential

------------------------------------------------------------------------
-- Literal Hessian action H(q)u = -q (q dot u) pHat_q.
------------------------------------------------------------------------

pressureHessianAction :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F →
  Z3.FourierMode → C3.Complex F → C3.Complex3 F → C3.Complex3 F
pressureHessianAction {F = F} E mode potential value =
  C3.complex3Scale
    (C3.complexNegate
      (C3.complexMultiply potential
        (C3.bilinearDot3 (C3.modeVector E mode) value)))
    (C3.modeVector E mode)

minusITwiceScalar :
  ∀ {r} {F : C3.RealField r}
    (dot potential : C3.Complex F) →
  C3.complexMultiply (Potential.minusI F)
    (C3.complexMultiply dot
      (C3.complexMultiply (Potential.minusI F) potential))
  ≡ C3.complexNegate (C3.complexMultiply potential dot)
minusITwiceScalar {F = F} dot potential =
  trans
    (C.solve 3
      (λ m d p →
        (m C.⊗ (d C.⊗ (m C.⊗ p)))
        C.⊜ ((m C.⊗ m) C.⊗ (p C.⊗ d)))
      refl (Potential.minusI F) dot potential)
    (trans
      (cong
        (λ square → C3.complexMultiply square
          (C3.complexMultiply potential dot))
        (Potential.minusISquared F))
      (Additive.complexMultiplyMinusOneLeft
        (C3.complexMultiply potential dot)))
  where module C = CRing.Solver F

orderedAdvectedPressureIsProjectedHessian :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidence : Physical.PhysicalTriadIncidence) →
  First.mixedProjectedOrderedTerm
    system (Audit.velocity system) (AP.pressureNonlinearity system) incidence
  ≡
  C3.lerayProject3 E I (Physical.k incidence)
    (pressureHessianAction E
      (Physical.q incidence)
      (Potential.pressurePotential system (Physical.q incidence))
      (Audit.velocity system (Physical.p incidence)))
orderedAdvectedPressureIsProjectedHessian {F = F} {E = E} {I = I}
    system incidence =
  let
    k = Physical.k incidence
    p = Physical.p incidence
    q = Physical.q incidence
    uP = Audit.velocity system p
    pHat = Potential.pressurePotential system q
    dot = C3.bilinearDot3 uP (C3.modeVector E q)
    pressureScalar = C3.complexMultiply (Potential.minusI F) pHat
    hessianScalar = C3.complexNegate (C3.complexMultiply pHat dot)
  in
  trans
    (cong
      (λ pressureQ →
        C3.complex3Scale (Potential.minusI F)
          (C3.lerayProject3 E I k
            (C3.complex3Scale dot pressureQ)))
      (Potential.pressureNonlinearityIsNegativeGradientOfPotential system q))
    (trans
      (cong
        (λ inside →
          C3.complex3Scale (Potential.minusI F)
            (C3.lerayProject3 E I k inside))
        (Potential.complex3ScaleCompose dot pressureScalar (C3.modeVector E q)))
      (trans
        (cong
          (C3.complex3Scale (Potential.minusI F))
          (LerayLin.lerayProjectComplexScale
            E I k
            (C3.complexMultiply dot pressureScalar)
            (C3.modeVector E q)))
        (trans
          (Potential.complex3ScaleCompose
            (Potential.minusI F)
            (C3.complexMultiply dot pressureScalar)
            (C3.lerayProject3 E I k (C3.modeVector E q)))
          (trans
            (cong
              (λ scalar →
                C3.complex3Scale scalar
                  (C3.lerayProject3 E I k (C3.modeVector E q)))
              (minusITwiceScalar dot pHat))
            (sym
              (LerayLin.lerayProjectComplexScale
                E I k hessianScalar (C3.modeVector E q)))))))

------------------------------------------------------------------------
-- Lift the ordered identity over the exact output fibre.
------------------------------------------------------------------------

hessianOrderedTerm :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
hessianOrderedTerm {E = E} {I = I} system incidence =
  C3.lerayProject3 E I (Physical.k incidence)
    (pressureHessianAction E
      (Physical.q incidence)
      (Potential.pressurePotential system (Physical.q incidence))
      (Audit.velocity system (Physical.p incidence)))

mapHessianTerms :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  List Physical.PhysicalTriadIncidence → List (C3.Complex3 F)
mapHessianTerms system [] = []
mapHessianTerms system (incidence ∷ rest) =
  hessianOrderedTerm system incidence ∷ mapHessianTerms system rest

sumAdvectedPressureTermsIsHessianFold :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidences : List Physical.PhysicalTriadIncidence) →
  Audit.sumVectors
    (First.mixedTerms system
      (Audit.velocity system) (AP.pressureNonlinearity system) incidences)
  ≡ Audit.sumVectors (mapHessianTerms system incidences)
sumAdvectedPressureTermsIsHessianFold system [] = refl
sumAdvectedPressureTermsIsHessianFold system (incidence ∷ rest) =
  cong₂ C3.complex3Add
    (orderedAdvectedPressureIsProjectedHessian system incidence)
    (sumAdvectedPressureTermsIsHessianFold system rest)

pressureHessianFold :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → C3.Complex3 F
pressureHessianFold system output =
  Audit.sumVectors
    (mapHessianTerms system (Audit.concreteTriadsAt system output))

advectedPressureVariationIsHessianFold :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    output →
  First.mixedProjectedNonlinearity
    system (Audit.velocity system) (AP.pressureNonlinearity system) output
  ≡ pressureHessianFold system output
advectedPressureVariationIsHessianFold system output =
  sumAdvectedPressureTermsIsHessianFold
    system (Audit.concreteTriadsAt system output)

pressureTransportVariation :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → C3.Complex3 F
pressureTransportVariation system output =
  First.mixedProjectedNonlinearity
    system (AP.pressureNonlinearity system) (Audit.velocity system) output

projectedNonlinearityPressureVariationSplitsHessianTransport :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    output →
  First.projectedNonlinearityFirstVariation
    system (AP.pressureNonlinearity system) output
  ≡ C3.complex3Add
      (pressureHessianFold system output)
      (pressureTransportVariation system output)
projectedNonlinearityPressureVariationSplitsHessianTransport
    system output =
  cong
    (λ advected →
      C3.complex3Add advected (pressureTransportVariation system output))
    (advectedPressureVariationIsHessianFold system output)

round85AdvectedPressureVariationIsLiteralHessianFold : Bool
round85AdvectedPressureVariationIsLiteralHessianFold = true

round85DNPressureSplitsHessianAndTransport : Bool
round85DNPressureSplitsHessianAndTransport = true

round85PressureTransportResidualEliminatedOrAbsorbed : Bool
round85PressureTransportResidualEliminatedOrAbsorbed = false

round85DNPressureSplitsHessianAndTransportIsTrue :
  round85DNPressureSplitsHessianAndTransport ≡ true
round85DNPressureSplitsHessianAndTransportIsTrue = refl
