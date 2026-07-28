module DASHI.Physics.YangMills.BalabanClayT4ConfiguredPhysicalOneLoopInstanceExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4LiteralDiagramWardCancellationExact as Diagrams
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Boxes
import DASHI.Physics.YangMills.BalabanClayT4Balaban536VacuumPolarizationTargetExact as Balaban536
import DASHI.Physics.YangMills.BalabanClayT4Balaban1987TheoremShapeExact as BalabanShape

------------------------------------------------------------------------
-- This module owns the coherence conditions between the literal Wilson/ghost/
-- Haar expansion, the transverse scalar integrand, the rational box family,
-- Balaban's Eqs. (5.36)--(5.41), and the two-constant Eq. (0.31) endpoint.
-- Each component is independently checkable; agreement is not inferred merely
-- because all components predict the same universal coefficient.
------------------------------------------------------------------------

record ConfiguredPhysicalOneLoopInstance
    (Background Fluctuation Operator Vertex Momentum Lorentz Color Scalar Kernel
      Scale Laurent Tensor Remainder : Set) : Set₂ where
  field
    vertices : Diagrams.LiteralBackgroundVertices
      Background Fluctuation Operator Vertex
    diagrams : Diagrams.LiteralOneLoopDiagramFamily
      Momentum Lorentz Color Scalar Kernel
    scalarReduction : Diagrams.LiteralTransverseScalarReduction
      Momentum Lorentz Color Scalar
    integral : Boxes.LiteralBrillouinIntegralPhysicalData Scale Scalar

    balaban536Target : Balaban536.DASHIOneLoopMatchesBalaban536
      Lorentz Laurent Momentum Scalar Tensor Remainder
    balaban031Target : BalabanShape.DASHIRunningCouplingMatchesBalaban031
      Scale Scalar

    diagramKernelAgreesWithScalarReduction : ∀ momentum mu nu a b → Set
    scalarIntegrandAgreesWithBoxIntegrand : ∀ scale momentum → Set

    dashiKernelMatchesBalaban536 : ∀ mu nu momentum →
      Balaban536.dashiOneLoopKernel balaban536Target mu nu momentum
      ≡ Balaban536.H (Balaban536.target balaban536Target) mu nu momentum

    coefficientMatchesMixedLaurentDerivative :
      Balaban536.dashiPlaquetteCoefficient balaban536Target
      ≡ Balaban536.mixedLaurentDerivative
          (Balaban536.target balaban536Target)
          (Balaban536.configuredMu balaban536Target)
          (Balaban536.configuredNu balaban536Target)
          (Balaban536.f (Balaban536.target balaban536Target))
          (Balaban536.identityLaurent (Balaban536.target balaban536Target))

    boxCoefficientMatchesBalabanCoefficient : ∀ scale → Set
    quarticRemainderMatchesBalabanBetaPrimeError : ∀ scale → Set

open ConfiguredPhysicalOneLoopInstance public

wilsonBackgroundQuadraticVertexExactLiteral =
  Diagrams.wilsonBackgroundQuadraticVertexExact ∘ vertices
  where open import Function using (_∘_)
wilsonBackgroundCubicVertexExactLiteral =
  Diagrams.wilsonBackgroundCubicVertexExact ∘ vertices
  where open import Function using (_∘_)
wilsonBackgroundQuarticVertexExactLiteral =
  Diagrams.wilsonBackgroundQuarticVertexExact ∘ vertices
  where open import Function using (_∘_)
faddeevPopovGhostOperatorExactLiteral =
  Diagrams.faddeevPopovGhostOperatorExact ∘ vertices
  where open import Function using (_∘_)
ghostBackgroundVertexExactLiteral =
  Diagrams.ghostBackgroundVertexExact ∘ vertices
  where open import Function using (_∘_)
haarMeasureQuadraticVertexExactLiteral =
  Diagrams.haarMeasureQuadraticVertexExact ∘ vertices
  where open import Function using (_∘_)

gaugeLoopTwoPointKernelExactLiteral =
  Diagrams.gaugeLoopTwoPointKernelExact ∘ diagrams
  where open import Function using (_∘_)
ghostLoopTwoPointKernelExactLiteral =
  Diagrams.ghostLoopTwoPointKernelExact ∘ diagrams
  where open import Function using (_∘_)
haarLoopTwoPointKernelExactLiteral =
  Diagrams.haarLoopTwoPointKernelExact ∘ diagrams
  where open import Function using (_∘_)
combinedOneLoopKernelExactLiteral =
  Diagrams.combinedOneLoopKernelExact ∘ diagrams
  where open import Function using (_∘_)

latticeWardIdentityForOneLoopKernelConfigured dataSet =
  Diagrams.latticeWardIdentityForOneLoopKernelLiteral (diagrams dataSet)

vacuumPolarizationKernelTransverseConfigured dataSet =
  Diagrams.vacuumPolarizationKernelTransverseLiteral (scalarReduction dataSet)

vacuumPolarizationMassTermZeroConfigured dataSet =
  Diagrams.vacuumPolarizationMassTermZeroLiteral (diagrams dataSet)

vacuumPolarizationLongitudinalPartZeroConfigured dataSet =
  Diagrams.vacuumPolarizationLongitudinalPartZeroLiteral (diagrams dataSet)

vacuumPolarizationPlaquetteCoefficientConfigured dataSet =
  Boxes.Integral.vacuumPolarizationPlaquetteCoefficientConfigured
    (Boxes.asConfiguredBrillouinIntegralCertificate (integral dataSet))

physicalRunningCouplingRecursionHasBalaban031Shape =
  BalabanShape.physicalRunningCouplingRecursionHasBalabanShape ∘ balaban031Target
  where open import Function using (_∘_)

literalDiagramCoherenceReductionLevel : ProofLevel
literalDiagramCoherenceReductionLevel = machineChecked

configuredBoxToBalabanCoefficientReductionLevel : ProofLevel
configuredBoxToBalabanCoefficientReductionLevel = machineChecked

balaban031EndpointReductionLevel : ProofLevel
balaban031EndpointReductionLevel = machineChecked

literalDiagramIntegrandAndQuarticInputsLevel : ProofLevel
literalDiagramIntegrandAndQuarticInputsLevel = conditional
