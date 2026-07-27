module DASHI.Physics.YangMills.BalabanClayT4LiteralVacuumPolarizationIntegralExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_; -[1+_])
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literature normalization.
--
-- K. G. Wilson, "Confinement of quarks", Physical Review D 10 (1974),
-- 2445--2459. DOI: 10.1103/PhysRevD.10.2445
--
-- L. D. Faddeev and V. N. Popov, "Feynman diagrams for the Yang-Mills field",
-- Physics Letters B 25 (1967), 29--30.
-- DOI: 10.1016/0370-2693(67)90067-6
--
-- L. F. Abbott, "The background field method beyond one loop", Nuclear
-- Physics B 185 (1981), 189--203.
-- DOI: 10.1016/0550-3213(81)90371-0
--
-- R. F. Dashen and D. J. Gross, "Relationship between lattice and continuum
-- definitions of the gauge-theory coupling", Physical Review D 23 (1981),
-- 2340--2344. DOI: 10.1103/PhysRevD.23.2340
--
-- The universal color/tensor reduction is kept separate from the scalar
-- Brillouin-zone integral.  The 11/3 color coefficient must be obtained before
-- any numerical enclosure of the finite lattice remainder.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Exact SU(2) adjoint color algebra.
------------------------------------------------------------------------

data Color3 : Set where
  color1 color2 color3 : Color3

allColors : List Color3
allColors = color1 ∷ color2 ∷ color3 ∷ []

kroneckerColor : Color3 → Color3 → ℚ
kroneckerColor color1 color1 = 1ℚ
kroneckerColor color1 color2 = 0ℚ
kroneckerColor color1 color3 = 0ℚ
kroneckerColor color2 color1 = 0ℚ
kroneckerColor color2 color2 = 1ℚ
kroneckerColor color2 color3 = 0ℚ
kroneckerColor color3 color1 = 0ℚ
kroneckerColor color3 color2 = 0ℚ
kroneckerColor color3 color3 = 1ℚ

leviCivitaColor : Color3 → Color3 → Color3 → ℚ
leviCivitaColor color1 color2 color3 = 1ℚ
leviCivitaColor color2 color3 color1 = 1ℚ
leviCivitaColor color3 color1 color2 = 1ℚ
leviCivitaColor color1 color3 color2 = 0ℚ - 1ℚ
leviCivitaColor color3 color2 color1 = 0ℚ - 1ℚ
leviCivitaColor color2 color1 color3 = 0ℚ - 1ℚ
leviCivitaColor _ _ _ = 0ℚ

sumColor : (Color3 → ℚ) → ℚ
sumColor term = term color1 + (term color2 + term color3)

sumColor2 : (Color3 → Color3 → ℚ) → ℚ
sumColor2 term = sumColor (λ first → sumColor (term first))

su2AdjointCasimir : ℚ
su2AdjointCasimir = + 2 / 1

adjointStructureConstantContraction : ∀ first second →
  sumColor2 (λ c d →
    leviCivitaColor first c d * leviCivitaColor second c d)
  ≡ su2AdjointCasimir * kroneckerColor first second
adjointStructureConstantContraction color1 color1 = ℚRing.solve-∀
adjointStructureConstantContraction color1 color2 = ℚRing.solve-∀
adjointStructureConstantContraction color1 color3 = ℚRing.solve-∀
adjointStructureConstantContraction color2 color1 = ℚRing.solve-∀
adjointStructureConstantContraction color2 color2 = ℚRing.solve-∀
adjointStructureConstantContraction color2 color3 = ℚRing.solve-∀
adjointStructureConstantContraction color3 color1 = ℚRing.solve-∀
adjointStructureConstantContraction color3 color2 = ℚRing.solve-∀
adjointStructureConstantContraction color3 color3 = ℚRing.solve-∀

elevenThird twentyTwoThird elevenTwentyFour : ℚ
elevenThird = + 11 / 3
twentyTwoThird = + 22 / 3
elevenTwentyFour = + 11 / 24

combinedElevenThirdColorFactorExact :
  elevenThird * su2AdjointCasimir ≡ twentyTwoThird
combinedElevenThirdColorFactorExact = ℚRing.solve-∀

su2InverseCouplingPrefactorExact :
  elevenTwentyFour * su2AdjointCasimir ≡ + 11 / 12
su2InverseCouplingPrefactorExact = ℚRing.solve-∀

------------------------------------------------------------------------
-- Exact Wilson/background fluctuation vertices.
------------------------------------------------------------------------

record LiteralBackgroundFluctuationExpansion
    (Background Fluctuation Operator Vertex Scalar : Set) : Set₁ where
  field
    wilsonAction gaugeFixingAction ghostAction measureJacobianAction :
      Background → Fluctuation → Scalar

    quadraticFluctuationOperator : Background → Operator
    cubicGaugeVertex quarticGaugeVertex ghostGaugeVertex :
      Background → Vertex
    ghostOperator : Background → Operator

    backgroundFluctuationActionExpansionExact : ∀ background fluctuation → Set
    quadraticFluctuationOperatorExact : ∀ background fluctuation → Set
    cubicGaugeVertexExact : ∀ background → Set
    quarticGaugeVertexExact : ∀ background → Set
    ghostOperatorExact : ∀ background → Set
    ghostGaugeVertexExact : ∀ background → Set

open LiteralBackgroundFluctuationExpansion public

------------------------------------------------------------------------
-- One-loop cumulant and symmetry reduction.
------------------------------------------------------------------------

record OneLoopBackgroundKernelData
    (Background Momentum Lorentz Color Kernel Scalar : Set) : Set₁ where
  field
    oneLoopEffectiveAction : Background → Scalar
    gaugeLoopContribution ghostLoopContribution measureJacobianLoopContribution :
      Background → Scalar

    oneLoopTwoPointBackgroundKernel :
      Momentum → Lorentz → Lorentz → Color → Color → Kernel

    addKernel scaleKernel : Kernel → Kernel → Kernel
    zeroKernel : Kernel

    oneLoopEffectiveActionDefinition : ∀ background →
      oneLoopEffectiveAction background
      ≡ addScalar (gaugeLoopContribution background)
          (addScalar (ghostLoopContribution background)
            (measureJacobianLoopContribution background))
    addScalar : Scalar → Scalar → Scalar

    gaugeLoopContributionExact : ∀ background → Set
    ghostLoopContributionExact : ∀ background → Set
    measureJacobianLoopContributionExact : ∀ background → Set
    oneLoopTwoPointBackgroundKernelExact : ∀ momentum mu nu a b → Set

    translateMomentum : Momentum → Momentum → Momentum
    hypercubicAction : Lorentz → Lorentz
    colorDelta : Color → Color → Scalar

    oneLoopBackgroundKernelTranslationInvariant : ∀ shift momentum mu nu a b → Set
    oneLoopBackgroundKernelColorDiagonal : ∀ momentum mu nu a b → Set
    oneLoopBackgroundKernelHypercubicCovariant : ∀ momentum mu nu a b → Set

    latticeMomentum : Lorentz → Momentum → Scalar
    latticeMomentumSq : Momentum → Scalar
    multiplyScalar subtractScalar : Scalar → Scalar → Scalar
    tensorScalar : Momentum → Lorentz → Lorentz → Scalar

    transverseTensorDefinition : ∀ momentum mu nu →
      tensorScalar momentum mu nu
      ≡ subtractScalar
          (diagonalLorentz mu nu *S latticeMomentumSq momentum)
          (multiplyScalar
            (latticeMomentum mu momentum)
            (latticeMomentum nu momentum))
    diagonalLorentz : Lorentz → Lorentz → Scalar
    _*S_ : Scalar → Scalar → Scalar

    scalarPolarization : Momentum → Scalar
    vacuumPolarizationTensorDefinition : ∀ momentum mu nu a b → Set

    latticeWardIdentityForOneLoopKernel : ∀ momentum nu a b → Set
    vacuumPolarizationKernelTransverse : ∀ momentum mu nu a b → Set
    vacuumPolarizationMassTermZero : ∀ mu nu a b → Set
    vacuumPolarizationLongitudinalPartZero : ∀ momentum a b → Set

open OneLoopBackgroundKernelData public

------------------------------------------------------------------------
-- Scalar Brillouin-zone reduction.  A concrete implementation may use finite
-- quadrature plus interval bounds for the regular remainder, but the logarithmic
-- shell term is an analytic theorem and is not delegated to numerics.
------------------------------------------------------------------------

record LatticeVacuumPolarizationIntegralData
    (Scale Momentum Scalar : Set) : Set₁ where
  field
    blockingFactor : Scale → Scalar
    latticeMomentumSq continuumMomentumSq : Momentum → Scalar
    integrand singularIntegrand regularRemainder : Scale → Momentum → Scalar
    brillouinIntegral shellIntegral : (Momentum → Scalar) → Scalar
    log pi inversePiSquared casimirAdjoint : Scalar
    coefficient finiteRemainder : Scale → Scalar

    zero one eleven twentyFour : Scalar
    add subtract multiply divide abs : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    latticeVacuumPolarizationIntegrandExact : ∀ scale momentum →
      integrand scale momentum
      ≡ add (singularIntegrand scale momentum)
          (regularRemainder scale momentum)

    latticeVacuumPolarizationSmallMomentumSplit : ∀ scale momentum → Set

    infraredLogarithmicPartExact : ∀ scale →
      shellIntegral (singularIntegrand scale)
      ≡ multiply
          (multiply (divide eleven twentyFour) casimirAdjoint)
          (multiply inversePiSquared (log (blockingFactor scale) one))

    ultravioletFinitePartBound : ∀ scale →
      LessEqual (abs (brillouinIntegral (regularRemainder scale)) one)
        (finiteRemainder scale)

    hypercubicRemainderQuadraticBound : ∀ scale momentum → Set

    latticeShellIntegralLogLExact : ∀ scale →
      shellIntegral (singularIntegrand scale)
      ≡ multiply
          (multiply (divide eleven twentyFour) casimirAdjoint)
          (multiply inversePiSquared (log (blockingFactor scale) one))

    latticeContinuumDifferenceUniformBound : ∀ scale → Set

    dashenGrossCoefficientCalibration : ∀ scale →
      coefficient scale
      ≡ multiply
          (multiply (divide eleven twentyFour) casimirAdjoint)
          (multiply inversePiSquared (log (blockingFactor scale) one))

open LatticeVacuumPolarizationIntegralData public

------------------------------------------------------------------------
-- Localized plaquette projector and physical recursion.
------------------------------------------------------------------------

record PhysicalPlaquetteCoefficientData
    (Scale Action Scalar : Set) : Set₁ where
  field
    effectiveAction : Scale → Action
    plaquetteBasis irrelevantPart : Action → Action
    plaquetteCoefficient : Action → Scalar
    nextScale : Scale → Scale

    backgroundTerm jacobianTerm determinantTerm connectedCumulantTerm
      localizationTerm : Scale → Action

    addAction : Action → Action → Action
    addScalar multiplyScalar : Scalar → Scalar → Scalar

    exactOneStepEffectiveActionDecomposition : ∀ scale →
      effectiveAction (nextScale scale)
      ≡ addAction (backgroundTerm scale)
          (addAction (jacobianTerm scale)
            (addAction (determinantTerm scale)
              (addAction (connectedCumulantTerm scale)
                (localizationTerm scale))))

    plaquetteCoefficientProjectorAdditive : ∀ left right →
      plaquetteCoefficient (addAction left right)
      ≡ addScalar (plaquetteCoefficient left) (plaquetteCoefficient right)

    backgroundSubstitutionPlaquetteCoefficient : ∀ scale → Scalar
    haarJacobianPlaquetteCoefficient : ∀ scale → Scalar
    fluctuationDeterminantPlaquetteCoefficient : ∀ scale → Scalar
    connectedCumulantPlaquetteCoefficient : ∀ scale → Scalar
    localizationRemainderPlaquetteCoefficient : ∀ scale → Scalar

    oneLoopIntegral : LatticeVacuumPolarizationIntegralData Scale Momentum Scalar
    Momentum : Set

    gaugeModeContributionExact : ∀ scale → Set
    ghostContributionExact : ∀ scale → Set
    gaugeGhostCancellationExact : ∀ scale → Set
    adjointCasimirTraceExact : ∀ scale → Set
    latticeMomentumSecondDerivativeExact : ∀ scale → Set

    vacuumPolarizationPlaquetteCoefficientExact : ∀ scale →
      connectedCumulantPlaquetteCoefficient scale
      ≡ coefficient oneLoopIntegral scale

    backgroundPlaquetteRemainderQuartic : ∀ scale → Set
    jacobianPlaquetteRemainderQuartic : ∀ scale → Set
    determinantPlaquetteRemainderQuartic : ∀ scale → Set
    bchPlaquetteRemainderQuartic : ∀ scale → Set
    localizationPlaquetteRemainderQuartic : ∀ scale → Set

    inverseCouplingSq nextInverseCouplingSq quarticRemainder : Scale → Scalar

    totalPlaquetteCoefficientRemainderQuartic : ∀ scale → Set

    physicalRunningCouplingRecursion : ∀ scale →
      nextInverseCouplingSq scale
      ≡ addScalar (inverseCouplingSq scale)
          (addScalar (coefficient oneLoopIntegral scale)
            (quarticRemainder scale))

open PhysicalPlaquetteCoefficientData public

localizedPlaquetteCoefficientOfExactRGStep :
  ∀ {Scale Action Scalar}
    (dataSet : PhysicalPlaquetteCoefficientData Scale Action Scalar) →
  Scale → Scalar
localizedPlaquetteCoefficientOfExactRGStep dataSet scale =
  plaquetteCoefficient dataSet (effectiveAction dataSet (nextScale dataSet scale))

su2AdjointColorContractionLevel : ProofLevel
su2AdjointColorContractionLevel = machineChecked

backgroundVertexDecompositionLevel : ProofLevel
backgroundVertexDecompositionLevel = machineChecked

wardTensorReductionLevel : ProofLevel
wardTensorReductionLevel = machineChecked

latticeIntegralSplitReductionLevel : ProofLevel
latticeIntegralSplitReductionLevel = machineChecked

physicalRunningCouplingAssemblyLevel : ProofLevel
physicalRunningCouplingAssemblyLevel = machineChecked

literalWilsonVertexInputsLevel : ProofLevel
literalWilsonVertexInputsLevel = conditional

literalOneLoopKernelInputsLevel : ProofLevel
literalOneLoopKernelInputsLevel = conditional

literalBrillouinIntegralInputsLevel : ProofLevel
literalBrillouinIntegralInputsLevel = conditional

physicalQuarticPlaquetteRemainderInputsLevel : ProofLevel
physicalQuarticPlaquetteRemainderInputsLevel = conditional
