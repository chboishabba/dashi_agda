module DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopCoefficientClosureExact where

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4LiteralVacuumPolarizationIntegralExact as VP

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
-- Roger Dashen and David J. Gross, "Relationship between Lattice and Continuum
-- Definitions of the Gauge-Theory Coupling", Physical Review D 23 (1981),
-- 2340--2344. DOI: 10.1103/PhysRevD.23.2340
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I. Generation of Effective Actions in a Small Field Approximation
-- and a Coupling Constant Renormalization in Four Dimensions", Communications
-- in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223
-- Relationship: Sections 4--5 and Eq. (5.36) are the primary tensor/kernel
-- falsification target.  No coefficient is imported definitionally.
------------------------------------------------------------------------

record LiteralOneLoopCoefficientClosure
    (Background Fluctuation Operator Vertex Momentum Lorentz Color Kernel
      Scale Action Scalar : Set) : Set₂ where
  field
    vertices : VP.LiteralBackgroundFluctuationExpansion
      Background Fluctuation Operator Vertex Scalar
    kernel : VP.OneLoopBackgroundKernelData
      Background Momentum Lorentz Color Kernel Scalar
    integral : VP.LatticeVacuumPolarizationIntegralData Scale Momentum Scalar
    coefficientData : VP.PhysicalPlaquetteCoefficientData Scale Action Scalar

    -- Literal Wilson/background vertices.
    wilsonBackgroundQuadraticVertexExact : ∀ background fluctuation → Set
    wilsonBackgroundCubicVertexExact : ∀ background → Set
    wilsonBackgroundQuarticVertexExact : ∀ background → Set
    faddeevPopovGhostOperatorExact : ∀ background → Set
    ghostBackgroundVertexExact : ∀ background → Set
    haarMeasureQuadraticVertexExact : ∀ background → Set

    -- Diagrammatic two-point kernels.
    gaugeLoopTwoPointKernelExact : ∀ momentum mu nu a b → Set
    ghostLoopTwoPointKernelExact : ∀ momentum mu nu a b → Set
    haarLoopTwoPointKernelExact : ∀ momentum mu nu a b → Set
    combinedOneLoopKernelExact : ∀ momentum mu nu a b → Set

    oneLoopKernelTranslationInvariantLiteral : ∀ shift momentum mu nu a b → Set
    oneLoopKernelColorDiagonalLiteral : ∀ momentum mu nu a b → Set
    oneLoopKernelHypercubicCovariantLiteral : ∀ momentum mu nu a b → Set

    latticeWardIdentityForOneLoopKernelLiteral : ∀ momentum nu a b → Set
    vacuumPolarizationKernelTransverseLiteral : ∀ momentum mu nu a b → Set
    vacuumPolarizationMassTermZeroLiteral : ∀ mu nu a b → Set
    vacuumPolarizationLongitudinalPartZeroLiteral : ∀ momentum a b → Set

    -- Scalar Brillouin-zone integral after color/tensor reduction.
    vacuumPolarizationScalarIntegrandExact : ∀ scale momentum → Set
    singularRegularMomentumSplitExact : ∀ scale momentum → Set
    infraredShellIntegralLogLExact : ∀ scale → Set
    regularRemainderIntegrable : ∀ scale → Set
    regularRemainderUniformBound : ∀ scale → Set
    latticeContinuumDifferenceUniformBoundLiteral : ∀ scale → Set
    dashenGrossCoefficientCalibrationLiteral : ∀ scale → Set

    -- The quartic common-norm remainder is independent of the universal
    -- one-loop logarithm and must be summable along the flow.
    totalPlaquetteCoefficientRemainderQuarticLiteral : ∀ scale → Set

open LiteralOneLoopCoefficientClosure public

backgroundFluctuationActionExpansionExact dataSet =
  VP.backgroundFluctuationActionExpansionExact (vertices dataSet)

quadraticFluctuationOperatorExact dataSet =
  VP.quadraticFluctuationOperatorExact (vertices dataSet)

cubicGaugeVertexExact dataSet =
  VP.cubicGaugeVertexExact (vertices dataSet)

quarticGaugeVertexExact dataSet =
  VP.quarticGaugeVertexExact (vertices dataSet)

ghostOperatorExact dataSet =
  VP.ghostOperatorExact (vertices dataSet)

ghostGaugeVertexExact dataSet =
  VP.ghostGaugeVertexExact (vertices dataSet)

oneLoopEffectiveActionDefinition dataSet =
  VP.oneLoopEffectiveActionDefinition (kernel dataSet)

oneLoopBackgroundKernelTranslationInvariant dataSet =
  VP.oneLoopBackgroundKernelTranslationInvariant (kernel dataSet)

oneLoopBackgroundKernelColorDiagonal dataSet =
  VP.oneLoopBackgroundKernelColorDiagonal (kernel dataSet)

oneLoopBackgroundKernelHypercubicCovariant dataSet =
  VP.oneLoopBackgroundKernelHypercubicCovariant (kernel dataSet)

vacuumPolarizationPlaquetteCoefficientExactLiteral :
  ∀ {Background Fluctuation Operator Vertex Momentum Lorentz Color Kernel
      Scale Action Scalar}
    (dataSet : LiteralOneLoopCoefficientClosure
      Background Fluctuation Operator Vertex Momentum Lorentz Color Kernel
      Scale Action Scalar)
    scale →
  VP.connectedCumulantPlaquetteCoefficient (coefficientData dataSet) scale
  ≡ VP.coefficient (VP.oneLoopIntegral (coefficientData dataSet)) scale
vacuumPolarizationPlaquetteCoefficientExactLiteral dataSet =
  VP.vacuumPolarizationPlaquetteCoefficientExact (coefficientData dataSet)
  where
  open import Agda.Builtin.Equality using (_≡_)

physicalRunningCouplingRecursionLiteral :
  ∀ {Background Fluctuation Operator Vertex Momentum Lorentz Color Kernel
      Scale Action Scalar}
    (dataSet : LiteralOneLoopCoefficientClosure
      Background Fluctuation Operator Vertex Momentum Lorentz Color Kernel
      Scale Action Scalar)
    scale → Set
physicalRunningCouplingRecursionLiteral dataSet scale =
  VP.nextInverseCouplingSq (coefficientData dataSet) scale
  ≡ VP.addScalar (coefficientData dataSet)
      (VP.inverseCouplingSq (coefficientData dataSet) scale)
      (VP.addScalar (coefficientData dataSet)
        (VP.coefficient (VP.oneLoopIntegral (coefficientData dataSet)) scale)
        (VP.quarticRemainder (coefficientData dataSet) scale))
  where
  open import Agda.Builtin.Equality using (_≡_)

physicalRunningCouplingRecursionLiteralProof dataSet =
  VP.physicalRunningCouplingRecursion (coefficientData dataSet)

literalWilsonVertexReductionLevel : ProofLevel
literalWilsonVertexReductionLevel = machineChecked

literalWardKernelReductionLevel : ProofLevel
literalWardKernelReductionLevel = machineChecked

literalScalarIntegralReductionLevel : ProofLevel
literalScalarIntegralReductionLevel = machineChecked

literalRunningCouplingClosureLevel : ProofLevel
literalRunningCouplingClosureLevel = machineChecked

literalOneLoopDiagramInputsLevel : ProofLevel
literalOneLoopDiagramInputsLevel = conditional

literalBrillouinIntegralCertificateInputsLevel : ProofLevel
literalBrillouinIntegralCertificateInputsLevel = conditional
