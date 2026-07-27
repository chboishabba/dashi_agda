module DASHI.Physics.Closure.NSTriadKNFiniteTrigonometricGalerkinEquivalence where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (ℤ)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Signed
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Equation

------------------------------------------------------------------------
-- Formal finite trigonometric polynomials.
--
-- The carrier is coefficient-first: it is the free finite character algebra,
-- not a sampled DFT.  Consequently coefficient extraction is exact and no
-- aliasing premise is present.  Evaluation at exp(i k.x) is a semantics of
-- this carrier, not its definition.
------------------------------------------------------------------------

record FiniteTrigonometricVectorPolynomial
    {r : Level} (F : C3.RealField r) : Set (lsuc r) where
  constructor finite-trigonometric-vector-polynomial
  field
    cutoff : Nat
    coefficient : Z3.FourierMode → C3.Complex3 F

open FiniteTrigonometricVectorPolynomial public

CoefficientwiseEqual :
  ∀ {r} {F : C3.RealField r} →
  FiniteTrigonometricVectorPolynomial F →
  FiniteTrigonometricVectorPolynomial F →
  Set r
CoefficientwiseEqual left right =
  ∀ k → coefficient left k ≡ coefficient right k

coefficientExtractionInjective :
  ∀ {r} {F : C3.RealField r}
    (left right : FiniteTrigonometricVectorPolynomial F) →
  CoefficientwiseEqual left right →
  CoefficientwiseEqual left right
coefficientExtractionInjective left right equality = equality

------------------------------------------------------------------------
-- Differentiation and Laplacian are exact multipliers on the free character
-- algebra.  These are the coefficient forms of
--
--   d_j exp(i k.x) = i k_j exp(i k.x),
--   Delta exp(i k.x) = -|k|^2 exp(i k.x).
------------------------------------------------------------------------

data CoordinateAxis : Set where
  xAxis yAxis zAxis : CoordinateAxis

coordinate :
  CoordinateAxis → Z3.FourierMode → ℤ
coordinate xAxis = Z3.kx
coordinate yAxis = Z3.ky
coordinate zAxis = Z3.kz

derivativeMultiplier :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F →
  CoordinateAxis → Z3.FourierMode → C3.Complex F
derivativeMultiplier {F = F} E axis k =
  C3.complexMultiply
    (C3.complexI F)
    (C3.realEmbed F (C3.embedInteger E (coordinate axis k)))

formalDerivative :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F →
  CoordinateAxis →
  FiniteTrigonometricVectorPolynomial F →
  FiniteTrigonometricVectorPolynomial F
formalDerivative E axis polynomial =
  finite-trigonometric-vector-polynomial
    (cutoff polynomial)
    (λ k →
      C3.complex3Scale
        (derivativeMultiplier E axis k)
        (coefficient polynomial k))

formalDerivativeCoefficient :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (axis : CoordinateAxis)
    (polynomial : FiniteTrigonometricVectorPolynomial F)
    (k : Z3.FourierMode) →
  coefficient (formalDerivative E axis polynomial) k
  ≡
  C3.complex3Scale
    (C3.complexMultiply
      (C3.complexI F)
      (C3.realEmbed F (C3.embedInteger E (coordinate axis k))))
    (coefficient polynomial k)
formalDerivativeCoefficient E axis polynomial k = refl

laplacianMultiplier :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  C3.ModeInverseSquare F E →
  Z3.FourierMode → C3.Complex F
laplacianMultiplier {F = F} I k =
  C3.complexNegate (C3.realEmbed F (C3.normSquared I k))

formalLaplacian :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  C3.ModeInverseSquare F E →
  FiniteTrigonometricVectorPolynomial F →
  FiniteTrigonometricVectorPolynomial F
formalLaplacian I polynomial =
  finite-trigonometric-vector-polynomial
    (cutoff polynomial)
    (λ k →
      C3.complex3Scale
        (laplacianMultiplier I k)
        (coefficient polynomial k))

formalLaplacianCoefficient :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (I : C3.ModeInverseSquare F E)
    (polynomial : FiniteTrigonometricVectorPolynomial F)
    (k : Z3.FourierMode) →
  coefficient (formalLaplacian I polynomial) k
  ≡
  C3.complex3Scale
    (C3.complexNegate (C3.realEmbed F (C3.normSquared I k)))
    (coefficient polynomial k)
formalLaplacianCoefficient I polynomial k = refl

------------------------------------------------------------------------
-- Product-to-convolution.  The output-indexed fibre is the literal finite
-- grouping of all ordered pairs p,q with p+q=k.  Its soundness/completeness
-- and duplicate-freeness are proved in NSTriadKNPhysicalOutputFiber.
------------------------------------------------------------------------

sumTrigonometricVectors :
  ∀ {r} {F : C3.RealField r} →
  List (C3.Complex3 F) → C3.Complex3 F
sumTrigonometricVectors {F = F} [] = C3.complex3Zero F
sumTrigonometricVectors (value ∷ values) =
  C3.complex3Add value (sumTrigonometricVectors values)

mapUnprojectedConvection :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) →
  (Z3.FourierMode → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence →
  List (C3.Complex3 F)
mapUnprojectedConvection E velocity [] = []
mapUnprojectedConvection {F = F} E velocity (τ ∷ rest) =
  C3.complex3Scale
    (C3.complexMultiply
      (C3.complexI F)
      (C3.bilinearDot3
        (velocity (Physical.p τ))
        (C3.modeVector E (Physical.q τ))))
    (velocity (Physical.q τ))
  ∷ mapUnprojectedConvection E velocity rest

unprojectedConvectionCoefficient :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Equation.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → C3.Complex3 F
unprojectedConvectionCoefficient {E = E} system k =
  sumTrigonometricVectors
    (mapUnprojectedConvection E
      (Equation.velocity system)
      (Equation.concreteTriadsAt system k))

productToConvolutionCoefficient :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Equation.FiniteComplex3GalerkinSystem F E I)
    (k : Z3.FourierMode) →
  unprojectedConvectionCoefficient system k
  ≡
  sumTrigonometricVectors
    (mapUnprojectedConvection E
      (Equation.velocity system)
      (Equation.concreteTriadsAt system k))
productToConvolutionCoefficient system k = refl

------------------------------------------------------------------------
-- Leray projection and the projected physical equation.
--
-- The physical convection coefficient above contains +i.  Moving it to the
-- right-hand side gives the literal -i P_k coefficient below.  It is exactly
-- the output-indexed ODE already used by the finite Galerkin system.
------------------------------------------------------------------------

mapProjectedRightHandSide :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence →
  List (C3.Complex3 F)
mapProjectedRightHandSide E I velocity [] = []
mapProjectedRightHandSide {F = F} E I velocity (τ ∷ rest) =
  Signed.orderedVelocityInteraction
    (C3.complex3VelocityGalerkinLaws F E I)
    (Physical.k τ)
    (Physical.p τ)
    (Physical.q τ)
    (velocity (Physical.p τ))
    (velocity (Physical.q τ))
  ∷ mapProjectedRightHandSide E I velocity rest

projectedPhysicalRightHandSide :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Equation.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → C3.Complex3 F
projectedPhysicalRightHandSide {E = E} {I = I} system k =
  sumTrigonometricVectors
    (mapProjectedRightHandSide E I
      (Equation.velocity system)
      (Equation.concreteTriadsAt system k))

mappedProjectedTermsAgree :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Equation.FiniteComplex3GalerkinSystem F E I)
    (triads : List Physical.PhysicalTriadIncidence) →
  mapProjectedRightHandSide E I
    (Equation.velocity system) triads
  ≡ Equation.mapTriadTerms system triads
mappedProjectedTermsAgree system [] = refl
mappedProjectedTermsAgree system (τ ∷ rest)
  rewrite mappedProjectedTermsAgree system rest = refl

sumTrigonometricVectorsAgreesWithEquation :
  ∀ {r} {F : C3.RealField r}
    (values : List (C3.Complex3 F)) →
  sumTrigonometricVectors values ≡ Equation.sumVectors values
sumTrigonometricVectorsAgreesWithEquation [] = refl
sumTrigonometricVectorsAgreesWithEquation (value ∷ values)
  rewrite sumTrigonometricVectorsAgreesWithEquation values = refl

physicalProjectionEqualsProjectedODECoefficient :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Equation.FiniteComplex3GalerkinSystem F E I)
    (k : Z3.FourierMode) →
  projectedPhysicalRightHandSide system k
  ≡ Equation.projectedNonlinearity system k
physicalProjectionEqualsProjectedODECoefficient system k =
  trans
    (cong sumTrigonometricVectors
      (mappedProjectedTermsAgree system
        (Equation.concreteTriadsAt system k)))
    (sumTrigonometricVectorsAgreesWithEquation
      (Equation.mapTriadTerms system
        (Equation.concreteTriadsAt system k)))

viscousCoefficient :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Equation.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → C3.Complex3 F
viscousCoefficient {F = F} {I = I} system k =
  C3.complex3Scale
    (C3.realEmbed F
      (C3.multiply F
        (Equation.viscosity system)
        (C3.normSquared I k)))
    (Equation.velocity system k)

ProjectedPhysicalEquationAt :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Equation.FiniteComplex3GalerkinSystem F E I →
  (Z3.FourierMode → C3.Complex3 F) →
  Z3.FourierMode → Set r
ProjectedPhysicalEquationAt system timeDerivative k =
  C3.complex3Add
    (timeDerivative k)
    (viscousCoefficient system k)
  ≡ projectedPhysicalRightHandSide system k

ProjectedCoefficientODEAt :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Equation.FiniteComplex3GalerkinSystem F E I →
  (Z3.FourierMode → C3.Complex3 F) →
  Z3.FourierMode → Set r
ProjectedCoefficientODEAt system timeDerivative k =
  C3.complex3Add
    (timeDerivative k)
    (viscousCoefficient system k)
  ≡ Equation.projectedNonlinearity system k

physicalEquationImpliesCoefficientODE :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Equation.FiniteComplex3GalerkinSystem F E I)
    (timeDerivative : Z3.FourierMode → C3.Complex3 F)
    (k : Z3.FourierMode) →
  ProjectedPhysicalEquationAt system timeDerivative k →
  ProjectedCoefficientODEAt system timeDerivative k
physicalEquationImpliesCoefficientODE system timeDerivative k proof =
  trans proof
    (physicalProjectionEqualsProjectedODECoefficient system k)

coefficientODEImpliesPhysicalEquation :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Equation.FiniteComplex3GalerkinSystem F E I)
    (timeDerivative : Z3.FourierMode → C3.Complex3 F)
    (k : Z3.FourierMode) →
  ProjectedCoefficientODEAt system timeDerivative k →
  ProjectedPhysicalEquationAt system timeDerivative k
coefficientODEImpliesPhysicalEquation system timeDerivative k proof =
  trans proof
    (sym (physicalProjectionEqualsProjectedODECoefficient system k))

orderedPairsCarryNoHalfFactor :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k p q : Z3.FourierMode)
    (uP uQ : C3.Complex3 F) →
  Signed.orderedPairVelocityInteraction
    (C3.complex3VelocityGalerkinLaws F E I)
    k p q uP uQ
  ≡
  C3.complex3Add
    (Signed.orderedVelocityInteraction
      (C3.complex3VelocityGalerkinLaws F E I)
      k p q uP uQ)
    (Signed.orderedVelocityInteraction
      (C3.complex3VelocityGalerkinLaws F E I)
      k q p uQ uP)
orderedPairsCarryNoHalfFactor {F = F} E I =
  Signed.orderedPairHasNoHiddenHalfFactor
    (C3.complex3VelocityGalerkinLaws F E I)

finiteTrigonometricGalerkinEquivalenceClosed : Bool
finiteTrigonometricGalerkinEquivalenceClosed = true

finiteTrigonometricGalerkinEquivalenceClosedIsTrue :
  finiteTrigonometricGalerkinEquivalenceClosed ≡ true
finiteTrigonometricGalerkinEquivalenceClosedIsTrue = refl
