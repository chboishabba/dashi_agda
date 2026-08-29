{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact where

------------------------------------------------------------------------
-- ROUND122: ONE BIDI PHYSICAL INPUT OBJECT FOR THE ENTIRE PRESENT CUT
--
-- The point of this module is to prevent a final round of receipt shuffling.
-- A1, A2, BC1 and BC2 are not four unrelated abstract consumers: BC2 must use
-- the exact BC1 carrier, and every downstream theorem is compiled from explicit
-- evidence-bearing source objects.
--
-- This record is therefore the irreducible present-cut source contract.  It does
-- not claim the physical inputs exist merely because their types are written.
-- Instead, once an implementation inhabits this ONE record, the mathematical
-- arrows requested in the present cut are all theorem-generated below.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as ℕ
open import Data.Rational.Base as ℚ using (1ℚ; _<_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
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
import DASHI.Physics.YangMills.BalabanYM4RowAAugmentedShootingGateExact as Aug

record PresentCutPhysicalSourceInputs
    (History Cell : Set) (cutoff : Nat) : Set₁ where
  field
    -- A1: one physical two-jet whose current source decomposition is Gaussian
    -- W/Q/R plus the exact finite-g five-channel evaluator.
    a1 : A1.A1ReducedSameObjectInputs History Cell

    -- A2: the explicit response-kernel route chosen after the betaMark audit.
    a2 : A2Producer.WardQuarticResponseProducer cutoff

    -- BC1: actual CMP109->CMP116 continuation, Eq.(5.1), finite analytic demands
    -- and the full A=A(B) physical component chain rule.
    bc1 : BC1Chain.BC1PhysicalCompositeInputs

    -- BC2 is FORCED to run on the exact BC1 carrier by its type.  There is no
    -- second potential/density equality field to forget or fake later.
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
  DASHI.Physics.YangMills.BalabanCutoffBetaLaw.negativeOffDiagonalSecondMomentumDerivative
    (DASHI.Physics.YangMills.BalabanCutoffBetaLaw.vacuumPolarisationCoefficient
      (A1.dynamics (a1 dataSet) K)) k
  ≡ DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact.embed
      (A1.embedding (a1 dataSet))
      (DASHI.Physics.YangMills.BalabanA1HistoryUniformTwoSidedBetaRound102Exact.beta
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
    DASHI.Foundations.RealAnalysisAxioms.-ℝ
      Heat.conditionalGradientCovariance
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

-- This is now the only honest frontier statement for the present cut: construct
-- the exact source object above from the literal finite-cutoff Yang--Mills
-- implementation and primary-source identities.  There is no additional hidden
-- consumer-side mathematics after that construction.
literalPresentCutPhysicalSourceInputsLevel : ProofLevel
literalPresentCutPhysicalSourceInputsLevel = conditional
