{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact where

------------------------------------------------------------------------
-- ROUND122: ONE BIDI PHYSICAL INPUT OBJECT FOR THE ENTIRE PRESENT CUT
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as ℕ
open import Data.Rational.Base as ℚ using (1ℚ; _<_)
open import DASHI.Foundations.RealAnalysisAxioms using (_-ℝ_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCutoffBetaLaw as BetaLaw
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Real
import DASHI.Physics.YangMills.BalabanA1HistoryUniformTwoSidedBetaRound102Exact as Cert
import DASHI.Physics.YangMills.BalabanA1FiveChannelEvaluatorBidiRound117Exact as A1
import DASHI.Physics.YangMills.BalabanA1Equation51FiveChannelSameObjectRound103Exact as A1Old
import DASHI.Physics.YangMills.BalabanYM4WardQuarticResponseProducerAdapterExact as A2Producer
import DASHI.Physics.YangMills.BalabanA2PresentCutFallbackRound120Exact as A2
import DASHI.Physics.YangMills.BalabanBC1CanonicalCarrierCompilerRound115Exact as BC1
import DASHI.Physics.YangMills.BalabanBC1PhysicalCompositeChainRuleRound118Exact as BC1Chain
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanBC2CompactGroupSameDensityRound119Exact as BC2
import DASHI.Physics.YangMills.BalabanHeatDoobSameDensityLogHessianRound103Exact as Heat

record PresentCutPhysicalSourceInputs
    (History Cell : Set) (cutoff : Nat) : Set₁ where
  field
    -- A1: one physical two-jet whose current source decomposition is Gaussian
    -- W/Q/R plus the exact finite-g five-channel evaluator.
    a1 : A1.A1ReducedSameObjectInputs History Cell

    -- A2: explicit response-kernel route selected after auditing betaMark.
    a2 : A2Producer.WardQuarticResponseProducer cutoff

    -- BC1: exact continuation/Eq.(5.1)/finite demands/full A=A(B) chain rule.
    bc1 : BC1Chain.BC1PhysicalCompositeInputs

    -- BC2 is forced to use the EXACT BC1 carrier by type.
    bc2 : BC2.CompactGroupHeatDoobOnCarrier
      (BC1.bc1CanonicalCarrier (BC1Chain.canonical bc1))

open PresentCutPhysicalSourceInputs public

------------------------------------------------------------------------
-- A1: five-channel evaluator and Eq.(5.42) are generated.
------------------------------------------------------------------------

a1SameObjectData :
  ∀ {History Cell cutoff} →
  PresentCutPhysicalSourceInputs History Cell cutoff →
  A1Old.Equation51FiveChannelSameObjectData History Cell
a1SameObjectData dataSet =
  A1.asEquation51FiveChannelSameObjectData (a1 dataSet)

a1Equation542MixedDerivativeExact :
  ∀ {History Cell cutoff}
    (dataSet : PresentCutPhysicalSourceInputs History Cell cutoff)
    K k (k<K : k ℕ.< K) →
  BetaLaw.negativeOffDiagonalSecondMomentumDerivative
    (BetaLaw.vacuumPolarisationCoefficient
      (A1.dynamics (a1 dataSet) K)) k
  ≡ Real.embed (A1.embedding (a1 dataSet))
      (Cert.beta
        (A1.certificate (a1 dataSet))
        (A1.historyForShell (a1 dataSet) K k k<K))
a1Equation542MixedDerivativeExact dataSet =
  A1Old.mixedDerivativeExact (a1SameObjectData dataSet)

------------------------------------------------------------------------
-- A2: complete finite-prefix contraction is generated.
------------------------------------------------------------------------

a2TotalSensitivityFullPrefixBelowOne :
  ∀ {History Cell cutoff}
    (dataSet : PresentCutPhysicalSourceInputs History Cell cutoff) →
  A2.presentCutTotalSensitivity (a2 dataSet) cutoff < 1ℚ
a2TotalSensitivityFullPrefixBelowOne dataSet =
  A2.presentCutFullSensitivityBelowOne (a2 dataSet)

------------------------------------------------------------------------
-- BC1: same localized action, full physical composite D_B^2 and Eq.(5.1).
------------------------------------------------------------------------

bc1Carrier :
  ∀ {History Cell cutoff} →
  PresentCutPhysicalSourceInputs History Cell cutoff →
  Carrier.LiteralDifferentiatedEffectiveDensityCarrier
bc1Carrier dataSet =
  BC1.bc1CanonicalCarrier (BC1Chain.canonical (bc1 dataSet))

bc1PhysicalHessianIsSameEffectivePotentialD2 :
  ∀ {History Cell cutoff}
    (dataSet : PresentCutPhysicalSourceInputs History Cell cutoff) →
  ∀ background u v →
  Carrier.cmp116PhysicalMarkedHessian (bc1Carrier dataSet) background u v
  ≡ Finite.secondVariation
      (BC1.calculus (BC1Chain.canonical (bc1 dataSet)))
      (Source.cmp109EffectivePotential
        (BC1.source (BC1Chain.canonical (bc1 dataSet)))
        (BC1.scale (BC1Chain.canonical (bc1 dataSet)))
        (BC1.volume (BC1Chain.canonical (bc1 dataSet))))
      background u v
bc1PhysicalHessianIsSameEffectivePotentialD2 dataSet =
  BC1Chain.bc1GlobalHessianIsSamePotentialD2 (bc1 dataSet)

------------------------------------------------------------------------
-- BC2: exact same BC1 potential/density, static Hessian minus covariance.
------------------------------------------------------------------------

bc2SameDensityCalculus :
  ∀ {History Cell cutoff}
    (dataSet : PresentCutPhysicalSourceInputs History Cell cutoff) →
  Heat.HeatDoobSameDensityCalculus (bc1Carrier dataSet)
bc2SameDensityCalculus dataSet =
  BC2.asRound103SameDensityCalculus (bc2 dataSet)

bc2HessianIsSameStaticMinusCovariance :
  ∀ {History Cell cutoff}
    (dataSet : PresentCutPhysicalSourceInputs History Cell cutoff) →
  ∀ time background u v →
  BC2.heatDoobHessian (bc2 dataSet) time background u v
  ≡ Heat.conditionalExpectedStaticHessian
      (bc2SameDensityCalculus dataSet) time background u v
    -ℝ Heat.conditionalGradientCovariance
      (bc2SameDensityCalculus dataSet) time background u v
bc2HessianIsSameStaticMinusCovariance dataSet =
  BC2.compactGroupHessianIsStaticMinusCovariance (bc2 dataSet)

presentCutA1CompilerLevel : ProofLevel
presentCutA1CompilerLevel = machineChecked

presentCutA2CompilerLevel : ProofLevel
presentCutA2CompilerLevel = machineChecked

presentCutBC1CompilerLevel : ProofLevel
presentCutBC1CompilerLevel = machineChecked

presentCutBC2CompilerLevel : ProofLevel
presentCutBC2CompilerLevel = machineChecked

presentCutEndToEndCompilerLevel : ProofLevel
presentCutEndToEndCompilerLevel = machineChecked

-- Only honest frontier statement for this cut: inhabit the exact source record
-- above from the finite-cutoff Yang--Mills implementation and primary sources.
literalPresentCutPhysicalSourceInputsLevel : ProofLevel
literalPresentCutPhysicalSourceInputsLevel = conditional
