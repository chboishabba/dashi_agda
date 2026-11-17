{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact where

------------------------------------------------------------------------
-- ROUND103 BC1 CAPSTONE: STRICT SAME DIFFERENTIATED CARRIER
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP109Equation51LocalizedHessianRound103Exact as Eq51
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Radius
import DASHI.Physics.YangMills.BalabanCMP109116SameDifferentiatedCarrierRound102Exact as Legacy

record LiteralDifferentiatedEffectiveDensityCarrier : Set₁ where
  field
    source : Source.CMP109116LiteralEffectiveActionContinuation
    calculus : Finite.SecondVariationLinearity
      (Source.Background source) (Source.Tangent source)
    equation51 : Eq51.CMP109Equation51OnContinuation source calculus

    scale : Source.Scale source
    volume : Source.Volume source

    -- This record now contains actual membership witnesses for every scale and
    -- volume, so there is no second local "inside domain" receipt here.
    radiusData :
      Radius.CMP116CommonAnalyticRadius
        (Source.Scale source) (Source.Volume source)

open LiteralDifferentiatedEffectiveDensityCarrier public

backgroundInsideCommonDomain :
  (dataSet : LiteralDifferentiatedEffectiveDensityCarrier) →
  Radius.BackgroundCoordinateInside
    (radiusData dataSet) (scale dataSet) (volume dataSet)
backgroundInsideCommonDomain dataSet =
  Radius.backgroundCoordinateInside
    (radiusData dataSet) (scale dataSet) (volume dataSet)

sourceInsideCommonDomain :
  (dataSet : LiteralDifferentiatedEffectiveDensityCarrier) →
  Radius.SourceCoordinateInside
    (radiusData dataSet) (scale dataSet) (volume dataSet)
sourceInsideCommonDomain dataSet =
  Radius.sourceCoordinateInside
    (radiusData dataSet) (scale dataSet) (volume dataSet)

localActivityInsideCommonDomain :
  (dataSet : LiteralDifferentiatedEffectiveDensityCarrier) →
  Radius.LocalActivityCoordinateInside
    (radiusData dataSet) (scale dataSet) (volume dataSet)
localActivityInsideCommonDomain dataSet =
  Radius.localActivityCoordinateInside
    (radiusData dataSet) (scale dataSet) (volume dataSet)

substitutedBackgroundInsideCommonDomain :
  (dataSet : LiteralDifferentiatedEffectiveDensityCarrier) →
  Radius.SubstitutedBackgroundInside
    (radiusData dataSet) (scale dataSet) (volume dataSet)
substitutedBackgroundInsideCommonDomain dataSet =
  Radius.substitutedBackgroundInside
    (radiusData dataSet) (scale dataSet) (volume dataSet)

finiteAction :
  LiteralDifferentiatedEffectiveDensityCarrier →
  Finite.FiniteLocalizedEffectiveAction
finiteAction dataSet =
  Source.atScaleVolume (source dataSet) (scale dataSet) (volume dataSet)

effectivePotential :
  (dataSet : LiteralDifferentiatedEffectiveDensityCarrier) →
  Source.Background (source dataSet) → ℝ
effectivePotential dataSet =
  Source.cmp109EffectivePotential (source dataSet) (scale dataSet) (volume dataSet)

cmp109Polarization :
  (dataSet : LiteralDifferentiatedEffectiveDensityCarrier) →
  Source.Background (source dataSet) →
  Source.Tangent (source dataSet) → Source.Tangent (source dataSet) → ℝ
cmp109Polarization dataSet =
  Eq51.polarizationSecondVariation
    (equation51 dataSet) (scale dataSet) (volume dataSet)

cmp116PhysicalMarkedHessian :
  (dataSet : LiteralDifferentiatedEffectiveDensityCarrier) →
  Source.Background (source dataSet) →
  Source.Tangent (source dataSet) → Source.Tangent (source dataSet) → ℝ
cmp116PhysicalMarkedHessian dataSet =
  Finite.finiteLocalizedSecondVariation
    (finiteAction dataSet) (calculus dataSet)

cmp109PolarizationIsCMP116PhysicalMarkedHessian :
  (dataSet : LiteralDifferentiatedEffectiveDensityCarrier) →
  ∀ background u v →
  cmp109Polarization dataSet background u v
  ≡ cmp116PhysicalMarkedHessian dataSet background u v
cmp109PolarizationIsCMP116PhysicalMarkedHessian dataSet =
  Eq51.polarizationIsLocalizedCompositeHessianSum
    (equation51 dataSet) (scale dataSet) (volume dataSet)

cmp109PolarizationIsSecondVariationOfEffectivePotential :
  (dataSet : LiteralDifferentiatedEffectiveDensityCarrier) →
  ∀ background u v →
  cmp109Polarization dataSet background u v
  ≡ Finite.secondVariation (calculus dataSet)
      (effectivePotential dataSet) background u v
cmp109PolarizationIsSecondVariationOfEffectivePotential dataSet =
  Eq51.equation51 (equation51 dataSet) (scale dataSet) (volume dataSet)

cmp116MarkedHessianIsSecondVariationOfEffectivePotential :
  (dataSet : LiteralDifferentiatedEffectiveDensityCarrier) →
  ∀ background u v →
  cmp116PhysicalMarkedHessian dataSet background u v
  ≡ Finite.secondVariation (calculus dataSet)
      (effectivePotential dataSet) background u v
cmp116MarkedHessianIsSecondVariationOfEffectivePotential dataSet background u v =
  trans
    (sym (cmp109PolarizationIsCMP116PhysicalMarkedHessian dataSet background u v))
    (cmp109PolarizationIsSecondVariationOfEffectivePotential dataSet background u v)

-- Compatibility only.  All Round103 source equalities are proved before entering
-- the older permissive Round102 alias carrier.
asLegacySameDifferentiatedCarrier :
  (dataSet : LiteralDifferentiatedEffectiveDensityCarrier) →
  Legacy.SameDifferentiatedEffectiveDensityCarrier
asLegacySameDifferentiatedCarrier dataSet = record
  { Legacy.SameDifferentiatedEffectiveDensityCarrier.Configuration =
      Source.Background (source dataSet)
  ; Legacy.SameDifferentiatedEffectiveDensityCarrier.Tangent =
      Source.Tangent (source dataSet)
  ; Legacy.SameDifferentiatedEffectiveDensityCarrier.Scalar = ℝ
  ; Legacy.SameDifferentiatedEffectiveDensityCarrier.effectivePotential =
      effectivePotential dataSet
  ; Legacy.SameDifferentiatedEffectiveDensityCarrier.secondVariation =
      cmp109Polarization dataSet
  ; Legacy.SameDifferentiatedEffectiveDensityCarrier.cmp109EffectiveActionIsThisPotential =
      ∀ background u v →
        cmp109Polarization dataSet background u v
        ≡ Finite.secondVariation (calculus dataSet)
            (effectivePotential dataSet) background u v
  ; Legacy.SameDifferentiatedEffectiveDensityCarrier.cmp109E2PiIsThisSecondVariation =
      ∀ background u v →
        cmp109Polarization dataSet background u v
        ≡ cmp109Polarization dataSet background u v
  ; Legacy.SameDifferentiatedEffectiveDensityCarrier.cmp116LocalizedActivityIsThisPotential =
      ∀ background →
        Source.cmp109EffectivePotential
          (source dataSet) (scale dataSet) (volume dataSet) background
        ≡ Finite.localizedPotential (finiteAction dataSet) background
  ; Legacy.SameDifferentiatedEffectiveDensityCarrier.cmp116HessianMarkIsThisSecondVariation =
      ∀ background u v →
        cmp116PhysicalMarkedHessian dataSet background u v
        ≡ cmp109Polarization dataSet background u v
  ; Legacy.SameDifferentiatedEffectiveDensityCarrier.heatDoobInitialDensityIsExpMinusThisPotential =
      ℝ ≡ ℝ
  }

literalDifferentiatedCarrierAssemblyLevel : ProofLevel
literalDifferentiatedCarrierAssemblyLevel = machineChecked

cmp109CMP116PhysicalHessianIdentityLevel : ProofLevel
cmp109CMP116PhysicalHessianIdentityLevel = machineChecked

literalDifferentiatedCarrierInstantiationLevel : ProofLevel
literalDifferentiatedCarrierInstantiationLevel = conditional
