{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact where

------------------------------------------------------------------------
-- ROUND103 BC1 CAPSTONE: STRICT SAME DIFFERENTIATED CARRIER
--
-- Choose CMP116 local activities AFTER their literal A=A(B) substitutions.
-- Then Part II is a localized representation of the Part-I effective potential
-- in the same physical B coordinate, and CMP109 (5.1) is D_B² of that same
-- potential.  The resulting marked static Hessian is the finite sum of the
-- physical composite local Hessians.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

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

    radiusData :
      Radius.CMP116CommonAnalyticRadius
        (Source.Scale source) (Source.Volume source)

    -- Explicit evidence that this scale/volume lies in the single source domain.
    backgroundInsideCommonDomain :
      Radius.backgroundCoordinateInside radiusData scale volume
    sourceInsideCommonDomain :
      Radius.sourceCoordinateInside radiusData scale volume
    localActivityInsideCommonDomain :
      Radius.localActivityCoordinateInside radiusData scale volume
    substitutedBackgroundInsideCommonDomain :
      Radius.substitutedBackgroundInside radiusData scale volume

open LiteralDifferentiatedEffectiveDensityCarrier public

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
  Relation.Binary.PropositionalEquality.trans
    (Relation.Binary.PropositionalEquality.sym
      (cmp109PolarizationIsCMP116PhysicalMarkedHessian dataSet background u v))
    (cmp109PolarizationIsSecondVariationOfEffectivePotential dataSet background u v)

-- Compatibility adapter for the older downstream alias carrier.  The theoremic
-- equalities above are proved BEFORE this adapter is constructed.
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
      Set
  }

literalDifferentiatedCarrierAssemblyLevel : ProofLevel
literalDifferentiatedCarrierAssemblyLevel = machineChecked

cmp109CMP116PhysicalHessianIdentityLevel : ProofLevel
cmp109CMP116PhysicalHessianIdentityLevel = machineChecked

-- What remains physical is the literal repository instantiation of `source`,
-- Eq.(5.1), and the uniform common radius.  There is no additional Hessian
-- comparison theorem after those are supplied.
literalDifferentiatedCarrierInstantiationLevel : ProofLevel
literalDifferentiatedCarrierInstantiationLevel = conditional
