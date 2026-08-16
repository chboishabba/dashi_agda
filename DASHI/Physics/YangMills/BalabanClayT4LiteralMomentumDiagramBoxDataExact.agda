module DASHI.Physics.YangMills.BalabanClayT4LiteralMomentumDiagramBoxDataExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; _+_; _-_; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4LiteralDiagramWardCancellationExact as Ward
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Boxes
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinIntegralCertificateExact as Integral
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quotient

------------------------------------------------------------------------
-- Literature normalization.
--
-- Kenneth G. Wilson, "Confinement of Quarks", Physical Review D 10 (1974),
-- 2445--2459. DOI: 10.1103/PhysRevD.10.2445
--
-- Ludwig D. Faddeev and Victor N. Popov, "Feynman Diagrams for the Yang--Mills
-- Field", Physics Letters B 25 (1967), 29--30.
-- DOI: 10.1016/0370-2693(67)90067-6
--
-- Luis F. Abbott, "The Background Field Method Beyond One Loop", Nuclear
-- Physics B 185 (1981), 189--203. DOI: 10.1016/0550-3213(81)90371-0
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I", Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223
-- Relationship: Eqs. (5.36)--(5.41) are the transverse-kernel and coefficient
-- falsification target. All lattice numerators below are derived from the fixed
-- Wilson, ghost and Haar conventions.
--
-- The regular-box quotient endpoints are sign-aware.  A positive denominator
-- interval is not by itself enough to justify nL/dU and nU/dL: the appropriate
-- denominator endpoint depends on the sign of the numerator enclosure.
------------------------------------------------------------------------

record LatticeMomentum4 (Momentum Lorentz Scalar : Set) : Set₁ where
  field
    zeroMomentum : Momentum
    component : Momentum → Lorentz → Scalar
    addMomentum negateMomentum : Momentum → Momentum → Momentum
    sineHalf cosine : Scalar → Scalar
    two zero add multiply : Scalar → Scalar → Scalar

    hatMomentum : Momentum → Lorentz → Scalar
    hatMomentumDefinition : ∀ momentum mu →
      hatMomentum momentum mu
      ≡ multiply two (sineHalf (component momentum mu))

    hatMomentumSquared : Momentum → Scalar
    hatMomentumSquaredDefinition : ∀ momentum → Set

open LatticeMomentum4 public

record LiteralMomentumVertices
    (Background Momentum Lorentz Color Scalar Vertex Operator : Set) : Set₁ where
  field
    momentum : LatticeMomentum4 Momentum Lorentz Scalar

    wilsonQuadraticVertex wilsonCubicVertex wilsonQuarticVertex :
      Background → Momentum → Vertex
    faddeevPopovOperator : Background → Momentum → Operator
    ghostBackgroundVertex haarQuadraticMeasureVertex :
      Background → Momentum → Vertex

    wilsonQuadraticBackgroundVertexMomentumExact :
      ∀ background momentum → Set
    wilsonCubicBackgroundVertexMomentumExact :
      ∀ background momentum → Set
    wilsonQuarticBackgroundVertexMomentumExact :
      ∀ background momentum → Set
    faddeevPopovOperatorMomentumExact :
      ∀ background momentum → Set
    ghostBackgroundVertexMomentumExact :
      ∀ background momentum → Set
    haarQuadraticMeasureVertexMomentumExact :
      ∀ background momentum → Set

    colorStructureConstant : Color → Color → Color → Scalar
    adjointCasimirContractionExact : ∀ a b → Set
    latticeMomentumConservationExact : ∀ momentum → Set

open LiteralMomentumVertices public

record LiteralMomentumDiagramKernels
    (Momentum Lorentz Color Scalar Kernel : Set) : Set₁ where
  field
    zero add : Scalar → Scalar → Scalar
    gaugeBubble gaugeTadpole ghostLoop haarMeasureLoop combinedKernel :
      Momentum → Lorentz → Lorentz → Color → Color → Scalar

    gaugeBubbleKernelExact : ∀ momentum mu nu a b → Set
    gaugeTadpoleKernelExact : ∀ momentum mu nu a b → Set
    ghostLoopKernelExact : ∀ momentum mu nu a b → Set
    haarMeasureLoopKernelExact : ∀ momentum mu nu a b → Set

    combinedVacuumPolarizationKernelExact : ∀ momentum mu nu a b →
      combinedKernel momentum mu nu a b
      ≡ add (gaugeBubble momentum mu nu a b)
          (add (gaugeTadpole momentum mu nu a b)
            (add (ghostLoop momentum mu nu a b)
              (haarMeasureLoop momentum mu nu a b)))

    latticeDerivative : Momentum → Lorentz → Scalar
    longitudinalContract :
      (Momentum → Lorentz → Lorentz → Color → Color → Scalar) →
      Momentum → Lorentz → Color → Color → Scalar

    gaugeBubbleWardContractionExact : ∀ momentum nu a b → Set
    gaugeTadpoleWardContractionExact : ∀ momentum nu a b → Set
    ghostKernelWardContractionExact : ∀ momentum nu a b → Set
    haarKernelWardContractionExact : ∀ momentum nu a b → Set
    combinedWardCancellationExact : ∀ momentum nu a b → Set

    combinedKernelAtZeroMomentumExact : ∀ mu nu a b → Set
    massTermCoefficientZero : ∀ mu nu a b → Set
    longitudinalCoefficientZero : ∀ momentum mu nu a b → Set

    transverseProjector : Momentum → Lorentz → Lorentz → Scalar
    transverseScalar : Momentum → Scalar
    colorDelta : Color → Color → Scalar
    transverseProjectorFactorization : ∀ momentum mu nu a b → Set

open LiteralMomentumDiagramKernels public

record LiteralVacuumPolarizationScalarData
    (Momentum Scalar : Set) : Set₁ where
  field
    numerator denominator scalarIntegrand continuumSingular regularIntegrand :
      Momentum → Scalar
    divide subtract : Scalar → Scalar → Scalar

    transverseScalarNumeratorExact : ∀ momentum → Set
    transverseScalarDenominatorExact : ∀ momentum → Set
    denominatorBuiltFromHatMomentumSquared : ∀ momentum → Set

    vacuumPolarizationScalarIntegrandExact : ∀ momentum →
      scalarIntegrand momentum ≡ divide (numerator momentum) (denominator momentum)

    infraredContinuumComparisonExact : ∀ momentum → Set
    singularRegularSplitExact : ∀ momentum →
      scalarIntegrand momentum
      ≡ subtract (continuumSingular momentum)
          (subtract (continuumSingular momentum) (regularIntegrand momentum))

    infraredShellIntegralLogLExact : Set
    regularRemainderIntegrable : Set

open LiteralVacuumPolarizationScalarData public

record GeneratedRegularMomentumBox : Set₁ where
  field
    box : Integral.MomentumBox4

    sinHalfLower sinHalfUpper : ℚ
    cosineLower cosineUpper : ℚ

    denominatorLower denominatorUpper : ℚ
    numeratorLower numeratorUpper : ℚ
    integrandLower integrandUpper : ℚ
    quadratureRemainder : ℚ

    sinHalfMomentumEnclosure : Set
    cosineMomentumEnclosure : Set
    propagatorDenominatorEnclosure : Set
    propagatorDenominatorStrictlyPositive : Set
    diagramNumeratorEnclosure : Set

    numeratorSignCase :
      Quotient.NumeratorSignCase numeratorLower numeratorUpper

    quotientLowerExact :
      integrandLower
      ≡ Quotient.quotientLowerEndpoint
          numeratorSignCase denominatorLower denominatorUpper
    quotientUpperExact :
      integrandUpper
      ≡ Quotient.quotientUpperEndpoint
          numeratorSignCase denominatorLower denominatorUpper
    integrandEnclosure : Set
    quadratureRemainderUpper : Set

    lowerContribution upperContribution : ℚ
    lowerContributionExact :
      lowerContribution
      ≡ Boxes.boxVolume box * integrandLower - quadratureRemainder
    upperContributionExact :
      upperContribution
      ≡ Boxes.boxVolume box * integrandUpper + quadratureRemainder
    contributionsOrdered : lowerContribution ≤ upperContribution

open GeneratedRegularMomentumBox public

asLiteralRegularBoxIntegrandData :
  GeneratedRegularMomentumBox → Boxes.LiteralRegularBoxIntegrandData
asLiteralRegularBoxIntegrandData dataSet = record
  { box = box dataSet
  ; denominatorLower = denominatorLower dataSet
  ; denominatorUpper = denominatorUpper dataSet
  ; numeratorLower = numeratorLower dataSet
  ; numeratorUpper = numeratorUpper dataSet
  ; integrandLower = integrandLower dataSet
  ; integrandUpper = integrandUpper dataSet
  ; quadratureError = quadratureRemainder dataSet
  ; denominatorLowerPositive = propagatorDenominatorStrictlyPositive dataSet
  ; denominatorEnclosureValid = propagatorDenominatorEnclosure dataSet
  ; numeratorTaylorEnclosureOnBox = diagramNumeratorEnclosure dataSet
  ; numeratorSignCase = numeratorSignCase dataSet
  ; quotientLowerCorrect = quotientLowerExact dataSet
  ; quotientUpperCorrect = quotientUpperExact dataSet
  ; integrandEnclosureOnBox = integrandEnclosure dataSet
  ; quadratureRemainderEnclosed = quadratureRemainderUpper dataSet
  ; lowerContribution = lowerContribution dataSet
  ; upperContribution = upperContribution dataSet
  ; lowerContributionDefinition = lowerContributionExact dataSet
  ; upperContributionDefinition = upperContributionExact dataSet
  ; contributionOrdered = contributionsOrdered dataSet
  }

mapGeneratedBoxes : List GeneratedRegularMomentumBox →
  List Boxes.LiteralRegularBoxIntegrandData
mapGeneratedBoxes [] = []
mapGeneratedBoxes (box ∷ boxes) =
  asLiteralRegularBoxIntegrandData box ∷ mapGeneratedBoxes boxes

record GeneratedBrillouinPartition : Set₁ where
  field
    infraredBoxes regularBoxes : List GeneratedRegularMomentumBox
    regularBoxesCoverInfraredComplement : Set
    regularBoxInteriorsDisjoint : Set
    regularBoxesClosedUnderHypercubicSymmetry : Set
    allDenominatorsPositive : Set
    allNumeratorsEnclosed : Set
    allIntegrandsEnclosed : Set
    allQuadratureErrorsEnclosed : Set
    sumLowerContributionsExact : Set
    sumUpperContributionsExact : Set
    regularRemainderInsideCertifiedInterval : Set

open GeneratedBrillouinPartition public

asRationalBrillouinBoxPartition :
  GeneratedBrillouinPartition → Boxes.RationalBrillouinBoxPartition
asRationalBrillouinBoxPartition dataSet = record
  { infraredBoxes = mapGeneratedBoxes (infraredBoxes dataSet)
  ; regularBoxData = mapGeneratedBoxes (regularBoxes dataSet)
  ; infraredNeighbourhoodRemovedExactly = regularBoxesCoverInfraredComplement dataSet
  ; regularBoxesPairwiseInteriorDisjoint = regularBoxInteriorsDisjoint dataSet
  ; regularBoxesCoverComplementExactly = regularBoxesCoverInfraredComplement dataSet
  ; hypercubicOrbitClosureExact = regularBoxesClosedUnderHypercubicSymmetry dataSet
  ; everyRegularDenominatorPositive = allDenominatorsPositive dataSet
  ; everyRegularNumeratorEnclosed = allNumeratorsEnclosed dataSet
  ; everyRegularIntegrandEnclosed = allIntegrandsEnclosed dataSet
  ; everyRegularQuadratureRemainderEnclosed = allQuadratureErrorsEnclosed dataSet
  }

record LiteralMomentumOneLoopPackage
    (Background Momentum Lorentz Color Scalar Vertex Operator Kernel : Set) : Set₂ where
  field
    vertices : LiteralMomentumVertices
      Background Momentum Lorentz Color Scalar Vertex Operator
    kernels : LiteralMomentumDiagramKernels Momentum Lorentz Color Scalar Kernel
    scalarReduction : LiteralVacuumPolarizationScalarData Momentum Scalar
    boxes : GeneratedBrillouinPartition
    kernelScalarCoherence : Set
    scalarBoxCoherence : Set
    balaban536To541TargetConstructed : Set

open LiteralMomentumOneLoopPackage public

literalMomentumVertexReductionLevel : ProofLevel
literalMomentumVertexReductionLevel = machineChecked

literalWardKernelReductionLevel : ProofLevel
literalWardKernelReductionLevel = machineChecked

generatedBoxAdapterLevel : ProofLevel
generatedBoxAdapterLevel = machineChecked

literalMomentumNumeratorDenominatorBoxInputsLevel : ProofLevel
literalMomentumNumeratorDenominatorBoxInputsLevel = conditional
