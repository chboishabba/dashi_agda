module DASHI.Physics.Closure.NSTriadKNPressurePotentialGradientHessianSameModeRound85Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Dhawal Buaria; Alain Pumir.
-- Title: "Role of pressure in generation of intense velocity gradients in
-- turbulent flows".
-- DOI: 10.48550/arXiv.2308.03902.
--
-- ROUND85 / SAME-MODE PRESSURE POTENTIAL -> GRADIENT -> HESSIAN
--
-- Round84 exposed the literal pressure contribution in each ordered Galerkin
-- interaction as
--
--   + i |k|^{-2} (k dot w) k.
--
-- Define on the SAME output mode
--
--   pHat = - |k|^{-2} (k dot w).
--
-- Then that contribution is exactly the negative pressure gradient
--
--   - i k pHat.
--
-- This module folds those scalar potentials over the actual physical output
-- fibre and proves that the complete Round84 pressure RHS is the negative
-- Fourier gradient of the folded potential.  It then differentiates the same
-- potential once more and proves the exact Hessian relation
--
--   H_ij = - k_i k_j pHat
--        = (- i k_j) (- i k_i pHat).
--
-- Thus the C4 pressure tangent and the Round78--81 pressure-Hessian lane can
-- share one literal source coefficient.  No norm estimate or sign is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as CRing
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityFirstVariationRound82Exact as First
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralAdvectivePressureRHSSplitRound84Exact as AP

minusI : ∀ {r} (F : C3.RealField r) → C3.Complex F
minusI F = C3.complexNegate (C3.complexI F)

complex3ScaleCompose :
  ∀ {r} {F : C3.RealField r}
    (a b : C3.Complex F) (value : C3.Complex3 F) →
  C3.complex3Scale a (C3.complex3Scale b value)
  ≡ C3.complex3Scale (C3.complexMultiply a b) value
complex3ScaleCompose a b (C3.complex3 vx vy vz) =
  Field.complex3Ext
    (Field.complexMultiplyAssociative a b vx)
    (Field.complexMultiplyAssociative a b vy)
    (Field.complexMultiplyAssociative a b vz)

complex3ScaleScalarAdd :
  ∀ {r} {F : C3.RealField r}
    (a b : C3.Complex F) (value : C3.Complex3 F) →
  C3.complex3Scale (C3.complexAdd a b) value
  ≡ C3.complex3Add
      (C3.complex3Scale a value)
      (C3.complex3Scale b value)
complex3ScaleScalarAdd = First.complex3ScaleScalarAdd

negativeGradient :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Z3.FourierMode → C3.Complex F → C3.Complex3 F
negativeGradient {F = F} E mode potential =
  C3.complex3Scale
    (C3.complexMultiply (minusI F) potential)
    (C3.modeVector E mode)

negativeGradientZero :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) mode →
  negativeGradient E mode (C3.complexZero F) ≡ C3.complex3Zero F
negativeGradientZero {F = F} E mode =
  trans
    (cong
      (λ scalar → C3.complex3Scale scalar (C3.modeVector E mode))
      (Hermitian.complexMultiplyZeroRight (minusI F)))
    (Hermitian.complex3ScaleZero (C3.modeVector E mode))

negativeGradientAdd :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) mode
    (left right : C3.Complex F) →
  negativeGradient E mode (C3.complexAdd left right)
  ≡ C3.complex3Add
      (negativeGradient E mode left)
      (negativeGradient E mode right)
negativeGradientAdd {F = F} E mode left right =
  trans
    (cong
      (λ scalar → C3.complex3Scale scalar (C3.modeVector E mode))
      (CRing.complexDistributeLeft (minusI F) left right))
    (complex3ScaleScalarAdd
      (C3.complexMultiply (minusI F) left)
      (C3.complexMultiply (minusI F) right)
      (C3.modeVector E mode))

------------------------------------------------------------------------
-- Scalar pressure potential on one ordered term and on the complete output
-- fibre.
------------------------------------------------------------------------

orderedPressurePotentialAt :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → Physical.PhysicalTriadIncidence → C3.Complex F
orderedPressurePotentialAt {F = F} {E = E} {I = I}
    system output incidence =
  C3.complexNegate
    (C3.complexMultiply
      (C3.realEmbed F (C3.inverseNormSquared I output))
      (C3.bilinearDot3
        (C3.modeVector E output)
        (AP.rawOrderedValue system incidence)))

pressureOrderedTermAtOutputIsNegativeGradient :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode)
    (incidence : Physical.PhysicalTriadIncidence) →
  Physical.k incidence ≡ output →
  AP.pressureOrderedTerm system incidence
  ≡ negativeGradient E output
      (orderedPressurePotentialAt system output incidence)
pressureOrderedTermAtOutputIsNegativeGradient {F = F} {E = E} {I = I}
    system output incidence outputExact =
  subst
    (λ selected →
      AP.pressureOrderedTerm system incidence
      ≡ negativeGradient E selected
          (orderedPressurePotentialAt system selected incidence))
    outputExact
    proofAtLiteralOutput
  where
  literalOutput = Physical.k incidence
  scalar =
    C3.complexMultiply
      (C3.realEmbed F (C3.inverseNormSquared I literalOutput))
      (C3.bilinearDot3
        (C3.modeVector E literalOutput)
        (AP.rawOrderedValue system incidence))

  scalarDoubleNegate :
    C3.complexMultiply (C3.complexI F) scalar
    ≡ C3.complexMultiply (minusI F) (C3.complexNegate scalar)
  scalarDoubleNegate =
    C.solve 2
      (λ i a → (i C.⊗ a) C.⊜ ((C.⊝ i) C.⊗ (C.⊝ a)))
      refl (C3.complexI F) scalar
    where module C = CRing.Solver F

  proofAtLiteralOutput :
    AP.pressureOrderedTerm system incidence
    ≡ negativeGradient E literalOutput
        (orderedPressurePotentialAt system literalOutput incidence)
  proofAtLiteralOutput =
    trans
      (AP.pressureOrderedTermIsPlusImaginaryRankOne system incidence)
      (trans
        (complex3ScaleCompose
          (C3.complexI F) scalar (C3.modeVector E literalOutput))
        (cong
          (λ selected → C3.complex3Scale selected (C3.modeVector E literalOutput))
          scalarDoubleNegate))

sumComplex :
  ∀ {r} {F : C3.RealField r} → List (C3.Complex F) → C3.Complex F
sumComplex {F = F} [] = C3.complexZero F
sumComplex (value ∷ rest) = C3.complexAdd value (sumComplex rest)

mapOrderedPotentials :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → List Physical.PhysicalTriadIncidence → List (C3.Complex F)
mapOrderedPotentials system output [] = []
mapOrderedPotentials system output (incidence ∷ rest) =
  orderedPressurePotentialAt system output incidence
  ∷ mapOrderedPotentials system output rest

pressurePotentialFromList :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → List Physical.PhysicalTriadIncidence → C3.Complex F
pressurePotentialFromList system output incidences =
  sumComplex (mapOrderedPotentials system output incidences)

pressureListIsNegativeGradient :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode)
    (incidences : List Physical.PhysicalTriadIncidence) →
  (∀ incidence → incidence Cube.∈ incidences → Physical.k incidence ≡ output) →
  Audit.sumVectors (AP.mapPressureTerms system incidences)
  ≡ negativeGradient E output
      (pressurePotentialFromList system output incidences)
pressureListIsNegativeGradient {F = F} {E = E}
    system output [] outputs =
  sym (negativeGradientZero E output)
pressureListIsNegativeGradient {F = F} {E = E}
    system output (incidence ∷ rest) outputs =
  trans
    (cong₂ C3.complex3Add
      (pressureOrderedTermAtOutputIsNegativeGradient
        system output incidence (outputs incidence (Cube.here refl)))
      (pressureListIsNegativeGradient system output rest
        (λ selected member → outputs selected (Cube.there member))))
    (sym
      (negativeGradientAdd E output
        (orderedPressurePotentialAt system output incidence)
        (pressurePotentialFromList system output rest)))

pressurePotential :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → C3.Complex F
pressurePotential system output =
  pressurePotentialFromList system output (Audit.concreteTriadsAt system output)

pressureNonlinearityIsNegativeGradientOfPotential :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode) →
  AP.pressureNonlinearity system output
  ≡ negativeGradient E output (pressurePotential system output)
pressureNonlinearityIsNegativeGradientOfPotential system output =
  pressureListIsNegativeGradient system output
    (Audit.concreteTriadsAt system output)
    (λ incidence member → Audit.concreteTriadsAtOutputAgreement member)

------------------------------------------------------------------------
-- One more derivative of the SAME potential gives the Hessian.
------------------------------------------------------------------------

minusISquared :
  ∀ {r} (F : C3.RealField r) →
  C3.complexMultiply (minusI F) (minusI F)
  ≡ C3.complexNegate (C3.complexOne F)
minusISquared F
  rewrite C3.negateZero F
        | Algebra.realMultiplyZeroLeft F (C3.zero F)
        | Algebra.realDoubleNegateProduct F (C3.one F) (C3.one F)
        | C3.multiplyOneLeft F (C3.one F)
        | C3.addZeroLeft F (C3.negate F (C3.one F))
        | Algebra.realMultiplyZeroLeft F (C3.negate F (C3.one F))
        | Algebra.realMultiplyZeroRight F (C3.negate F (C3.one F))
        | C3.addZeroLeft F (C3.zero F) = refl

pressureGradientComponent :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Complex F → C3.Complex F
pressureGradientComponent {F = F} coordinate potential =
  C3.complexMultiply (minusI F)
    (C3.complexMultiply (C3.realEmbed F coordinate) potential)

pressureHessianComponent :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Complex F → C3.Complex F
pressureHessianComponent {F = F} left right potential =
  C3.complexNegate
    (C3.complexMultiply
      (C3.realEmbed F left)
      (C3.complexMultiply (C3.realEmbed F right) potential))

negativeDerivativeOfPressureRHS :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Complex F → C3.Complex F
negativeDerivativeOfPressureRHS {F = F} derivativeCoordinate rhsComponent =
  C3.complexMultiply (minusI F)
    (C3.complexMultiply (C3.realEmbed F derivativeCoordinate) rhsComponent)

pressureHessianIsNegativeDerivativeOfPressureRHS :
  ∀ {r} {F : C3.RealField r}
    (left right : C3.Carrier F)
    (potential : C3.Complex F) →
  pressureHessianComponent left right potential
  ≡ negativeDerivativeOfPressureRHS right
      (pressureGradientComponent left potential)
pressureHessianIsNegativeDerivativeOfPressureRHS {F = F}
    left right potential =
  trans
    classicalToGrouped
    (sym groupedDerivative)
  where
  li = C3.realEmbed F left
  ri = C3.realEmbed F right
  mI = minusI F

  classicalToGrouped :
    C3.complexNegate (C3.complexMultiply li (C3.complexMultiply ri potential))
    ≡ C3.complexMultiply
        (C3.complexNegate (C3.complexOne F))
        (C3.complexMultiply ri (C3.complexMultiply li potential))
  classicalToGrouped =
    C.solve 3
      (λ l r p →
        (C.⊝ (l C.⊗ (r C.⊗ p)))
        C.⊜ ((C.⊝ C.Κ (C3.complexOne F)) C.⊗ (r C.⊗ (l C.⊗ p))))
      refl li ri potential
    where module C = CRing.Solver F

  groupedDerivative :
    negativeDerivativeOfPressureRHS right
      (pressureGradientComponent left potential)
    ≡ C3.complexMultiply
        (C3.complexNegate (C3.complexOne F))
        (C3.complexMultiply ri (C3.complexMultiply li potential))
  groupedDerivative =
    trans
      (C.solve 4
        (λ m r l p →
          (m C.⊗ (r C.⊗ (m C.⊗ (l C.⊗ p))))
          C.⊜ ((m C.⊗ m) C.⊗ (r C.⊗ (l C.⊗ p))))
        refl mI ri li potential)
      (cong
        (λ square → C3.complexMultiply square
          (C3.complexMultiply ri (C3.complexMultiply li potential)))
        (minusISquared F))
    where module C = CRing.Solver F

round85LiteralPressurePotentialConstructed : Bool
round85LiteralPressurePotentialConstructed = true

round85PressureRHSIsNegativeGradientOfSamePotential : Bool
round85PressureRHSIsNegativeGradientOfSamePotential = true

round85PressureGradientToHessianSameModeBridgeConstructed : Bool
round85PressureGradientToHessianSameModeBridgeConstructed = true

round85PressureGradientToHessianSameModeBridgeConstructedIsTrue :
  round85PressureGradientToHessianSameModeBridgeConstructed ≡ true
round85PressureGradientToHessianSameModeBridgeConstructedIsTrue = refl
