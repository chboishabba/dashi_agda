module DASHI.Analysis.RiemannG2PhaseWeldCellwiseUpperBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannG2FinalNearLiteralKernelExact as Kernel
import DASHI.Analysis.RiemannG2FinalPoleNearObserverRefinementExact as Literal
import DASHI.Analysis.RiemannG2ProofRelevantTargetTranslationModulationExact as Phase
import DASHI.Analysis.RiemannG2LiteralPhaseModulationWeldExact as Weld
import DASHI.Analysis.RiemannG2PhaseWeldCellResponseTransportExact as PhaseTransport
import DASHI.Analysis.RiemannG2LiteralCellIntegralUpperExact as IntegralUpper
import DASHI.Analysis.RiemannG2LiteralCellwiseNearUpperExact as Cellwise
import DASHI.Analysis.RiemannG2GenericNearUpperClusterResponseCompilerExact as Generic

------------------------------------------------------------------------
-- PHASE WELD -> ONE-SIDED CELL UPPER -> FINAL NEAR UPPER
--
-- The exact-equality route in PhaseWeldCellResponseTransport exposes generic
-- integration and finite-sum congruence obligations.  The downstream RH
-- consumer, however, only needs a certified one-sided near upper before the
-- strict ClusterResponse comparison.
--
-- Reuse the existing LiteralCellIntegralUpper lane instead of demanding
-- stronger exact aggregation laws:
--
--   same-object phase weld
--     -> pointwise phase-realized integrand <= majorant
--     -> transport that bound to the literal cosine integrand
--     -> pair-specific integral monotonicity
--     -> certified cell upper
--     -> existing finite enumerated additive monotonicity
--     -> final nearResponseAt(J) upper.
--
-- This is semantic ascent by the weakest consumer-sufficient route.
------------------------------------------------------------------------

literalModelFromKernel :
  ∀ {S transport}
    (offInput : Direct.DirectLiteralOffTargetInput S transport) →
  Kernel.FinalNearLiteralKernel offInput →
  Literal.FinalPoleNearLiteralModel offInput
literalModelFromKernel = Kernel.compileFinalPoleNearLiteralModel

record PhaseSensitiveCellMajorantAuthority
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (offInput : Direct.DirectLiteralOffTargetInput S transport)
    (kernel : Kernel.FinalNearLiteralKernel offInput)
    (H : Phase.ProofRelevantTargetTranslationModulation)
    (weld : Weld.LiteralPhaseModulationWeld
      offInput (literalModelFromKernel offInput kernel) H) : Set₁ where
  private
    Scalar = NearFar.Scalar S
    model = literalModelFromKernel offInput kernel
  field
    majorant : Kernel.ZeroIndex kernel → Scalar → Scalar
    cellUpper : Kernel.ZeroIndex kernel → Scalar

    phaseIntegrandBelowMajorant :
      (sigma : Kernel.ZeroIndex kernel) →
      (u : Scalar) →
      NearFar._≤_ S
        (PhaseTransport.phaseRealizedIntegrand weld sigma u)
        (majorant sigma u)

    -- Pair-specific transport only; no global integration theory is required.
    integrateMonotoneForLiteralMajorant :
      (sigma : Kernel.ZeroIndex kernel) →
      ((u : Scalar) →
        NearFar._≤_ S
          (IntegralUpper.literalIntegrand kernel sigma u)
          (majorant sigma u)) →
      NearFar._≤_ S
        (Kernel.integrate kernel (IntegralUpper.literalIntegrand kernel sigma))
        (Kernel.integrate kernel (majorant sigma))

    integratedMajorantBelowUpper :
      (sigma : Kernel.ZeroIndex kernel) →
      NearFar._≤_ S
        (Kernel.integrate kernel (majorant sigma))
        (cellUpper sigma)

    authorityReference : String

open PhaseSensitiveCellMajorantAuthority public

------------------------------------------------------------------------
-- The compiled literal model uses exactly the kernel operations, so its cosine
-- integrand is definitionally the existing literal kernel integrand.
------------------------------------------------------------------------

modelCosineIntegrandIsKernelLiteralIntegrand :
  ∀ {S transport}
    {offInput : Direct.DirectLiteralOffTargetInput S transport}
    {kernel : Kernel.FinalNearLiteralKernel offInput} →
  (sigma : Kernel.ZeroIndex kernel) →
  (u : NearFar.Scalar S) →
  PhaseTransport.literalCosineIntegrand
    (literalModelFromKernel offInput kernel) sigma u
  ≡ IntegralUpper.literalIntegrand kernel sigma u
modelCosineIntegrandIsKernelLiteralIntegrand sigma u = refl

phaseIntegrandIsKernelLiteralIntegrand :
  ∀ {S transport}
    {offInput : Direct.DirectLiteralOffTargetInput S transport}
    {kernel : Kernel.FinalNearLiteralKernel offInput}
    {H : Phase.ProofRelevantTargetTranslationModulation} →
  (weld : Weld.LiteralPhaseModulationWeld
    offInput (literalModelFromKernel offInput kernel) H) →
  (sigma : Kernel.ZeroIndex kernel) →
  (u : NearFar.Scalar S) →
  PhaseTransport.phaseRealizedIntegrand weld sigma u
  ≡ IntegralUpper.literalIntegrand kernel sigma u
phaseIntegrandIsKernelLiteralIntegrand weld sigma u =
  trans
    (PhaseTransport.phaseIntegrandEqualsLiteralCosineIntegrand weld sigma u)
    (modelCosineIntegrandIsKernelLiteralIntegrand sigma u)

literalIntegrandBelowMajorantFromPhase :
  ∀ {S transport}
    {offInput : Direct.DirectLiteralOffTargetInput S transport}
    {kernel : Kernel.FinalNearLiteralKernel offInput}
    {H : Phase.ProofRelevantTargetTranslationModulation}
    {weld : Weld.LiteralPhaseModulationWeld
      offInput (literalModelFromKernel offInput kernel) H} →
  (authority : PhaseSensitiveCellMajorantAuthority offInput kernel H weld) →
  (sigma : Kernel.ZeroIndex kernel) →
  (u : NearFar.Scalar S) →
  NearFar._≤_ S
    (IntegralUpper.literalIntegrand kernel sigma u)
    (majorant authority sigma u)
literalIntegrandBelowMajorantFromPhase {S = S} {weld = weld} authority sigma u =
  subst
    (λ x → NearFar._≤_ S x (majorant authority sigma u))
    (phaseIntegrandIsKernelLiteralIntegrand weld sigma u)
    (phaseIntegrandBelowMajorant authority sigma u)

compilePhaseAuthorityToLiteralIntegralUpper :
  ∀ {S transport}
    {offInput : Direct.DirectLiteralOffTargetInput S transport}
    {kernel : Kernel.FinalNearLiteralKernel offInput}
    {H : Phase.ProofRelevantTargetTranslationModulation}
    {weld : Weld.LiteralPhaseModulationWeld
      offInput (literalModelFromKernel offInput kernel) H} →
  PhaseSensitiveCellMajorantAuthority offInput kernel H weld →
  IntegralUpper.LiteralCellIntegralUpperAuthority offInput kernel
compilePhaseAuthorityToLiteralIntegralUpper authority = record
  { IntegralUpper.majorant = majorant authority
  ; IntegralUpper.cellUpper = cellUpper authority
  ; IntegralUpper.literalIntegrandBelowMajorant =
      literalIntegrandBelowMajorantFromPhase authority
  ; IntegralUpper.integrateMonotoneForMajorant =
      integrateMonotoneForLiteralMajorant authority
  ; IntegralUpper.integratedMajorantBelowUpper =
      integratedMajorantBelowUpper authority
  ; IntegralUpper.authorityReference = authorityReference authority
  }

compilePhaseAuthorityToCellwiseUpper :
  ∀ {S transport}
    {offInput : Direct.DirectLiteralOffTargetInput S transport}
    {kernel : Kernel.FinalNearLiteralKernel offInput}
    {H : Phase.ProofRelevantTargetTranslationModulation}
    {weld : Weld.LiteralPhaseModulationWeld
      offInput (literalModelFromKernel offInput kernel) H} →
  (enumeration : Cellwise.LiteralNearEnumeration offInput kernel) →
  (authority : PhaseSensitiveCellMajorantAuthority offInput kernel H weld) →
  Cellwise.LiteralCellwiseUpper offInput kernel enumeration
compilePhaseAuthorityToCellwiseUpper enumeration authority =
  IntegralUpper.compileIntegralAuthorityToCellwiseUpper
    enumeration
    (compilePhaseAuthorityToLiteralIntegralUpper authority)

compilePhaseAuthorityToFinalNearUpper :
  ∀ {S transport}
    {offInput : Direct.DirectLiteralOffTargetInput S transport}
    {kernel : Kernel.FinalNearLiteralKernel offInput}
    {H : Phase.ProofRelevantTargetTranslationModulation}
    {weld : Weld.LiteralPhaseModulationWeld
      offInput (literalModelFromKernel offInput kernel) H} →
  (enumeration : Cellwise.LiteralNearEnumeration offInput kernel) →
  (authority : PhaseSensitiveCellMajorantAuthority offInput kernel H weld) →
  Generic.FinalNearUpper offInput
compilePhaseAuthorityToFinalNearUpper enumeration authority =
  Cellwise.compileCellwiseFinalNearUpper
    (compilePhaseAuthorityToCellwiseUpper enumeration authority)

------------------------------------------------------------------------
-- Boundary / next residual.
------------------------------------------------------------------------

record PhaseWeldCellwiseUpperBridgeBoundary : Set where
  constructor phase-weld-cellwise-upper-bridge-boundary
  field
    sameObjectPhaseWeldStillRequired : Bool
    phaseSensitivePointwiseMajorantCanFeedLiteralCellUpper : Bool
    existingPairSpecificIntegralMonotonicityReused : Bool
    existingFiniteFoldMonotonicityReused : Bool
    exactIntegrationCongruenceRequiredForUpperRoute : Bool
    exactFiniteNearSumCongruenceRequiredForUpperRoute : Bool
    exactTranscendentalCellEqualityRequiredForUpperRoute : Bool
    phaseAuthorityCompilesToFinalNearUpper : Bool
    phaseSensitiveMajorantAuthorityInhabitedHere : Bool
    universalPoleQuotientWeldInhabitedHere : Bool
    strictClusterMarginPaidHere : Bool
    rhDerived : Bool
open PhaseWeldCellwiseUpperBridgeBoundary public

canonicalPhaseWeldCellwiseUpperBridgeBoundary :
  PhaseWeldCellwiseUpperBridgeBoundary
canonicalPhaseWeldCellwiseUpperBridgeBoundary =
  phase-weld-cellwise-upper-bridge-boundary
    true true true true false false false true false false false false

data PhaseWeldCellwiseUpperBridgeResidual : Set where
  inhabitUniversalPoleQuotientPhaseWeld : PhaseWeldCellwiseUpperBridgeResidual
  constructPhaseSensitivePointwiseMajorant : PhaseWeldCellwiseUpperBridgeResidual
  provePairSpecificIntegralMonotonicity : PhaseWeldCellwiseUpperBridgeResidual
  certifyIntegratedMajorantCellUppers : PhaseWeldCellwiseUpperBridgeResidual
  instantiateExactFiniteNearEnumeration : PhaseWeldCellwiseUpperBridgeResidual
  compileFinalNearUpperAndPayStrictMargin : PhaseWeldCellwiseUpperBridgeResidual

firstPhaseWeldCellwiseUpperBridgeResidual : PhaseWeldCellwiseUpperBridgeResidual
firstPhaseWeldCellwiseUpperBridgeResidual = inhabitUniversalPoleQuotientPhaseWeld
