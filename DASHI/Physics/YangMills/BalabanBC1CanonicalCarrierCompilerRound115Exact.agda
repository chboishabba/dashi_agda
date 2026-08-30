{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanBC1CanonicalCarrierCompilerRound115Exact where

------------------------------------------------------------------------
-- ROUND115 BC1 BIDI COMPILER
--
-- Backward consumer: Round103's strict differentiated carrier needs only
--
--   * the literal CMP109->CMP116 effective-action continuation,
--   * the second-variation calculus / Eq.(5.1) identification,
--   * one scale and volume,
--   * a common CMP116 analytic-radius object.
--
-- Forward source: Round104/114 already construct that common-radius object from
-- the finite normalized CMP116 Sect.1 demand constants.  Therefore the physical
-- BC1 theorem must NOT separately produce an abstract radius witness.
--
-- This file compiles the two directions literally: source continuation + Eq.(5.1)
-- + finite CMP116 demands -> the exact Round103 differentiated carrier.
--
-- Cross-pollination payoff: the SAME Eq.(5.1) source object used by A1's
-- mixed two-jet is also the Hessian identity consumed by BC1.  A1 and BC1 do not
-- require two unrelated identifications of the effective action.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP109Equation51LocalizedHessianRound103Exact as Eq51
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as Canon
import DASHI.Physics.YangMills.BalabanCMP116CanonicalRadiusToCommonDomainRound114Exact as Radius114

record BC1CanonicalPhysicalInputs : Set₁ where
  field
    source : Source.CMP109116LiteralEffectiveActionContinuation

    calculus : Finite.SecondVariationLinearity
      (Source.Background source) (Source.Tangent source)

    equation51 : Eq51.CMP109Equation51OnContinuation source calculus

    scale : Source.Scale source
    volume : Source.Volume source

    -- These are the only radius-side data left after Round114.  Their physical
    -- extraction is from the literal CMP116 Sect.1 inequalities; the common
    -- radius itself is constructed, not assumed.
    analyticDemands : Canon.CMP116FiniteNormalizedAnalyticDemands

open BC1CanonicalPhysicalInputs public

bc1CanonicalCarrier :
  BC1CanonicalPhysicalInputs →
  Carrier.LiteralDifferentiatedEffectiveDensityCarrier
bc1CanonicalCarrier dataSet = record
  { Carrier.LiteralDifferentiatedEffectiveDensityCarrier.source = source dataSet
  ; Carrier.LiteralDifferentiatedEffectiveDensityCarrier.calculus = calculus dataSet
  ; Carrier.LiteralDifferentiatedEffectiveDensityCarrier.equation51 = equation51 dataSet
  ; Carrier.LiteralDifferentiatedEffectiveDensityCarrier.scale = scale dataSet
  ; Carrier.LiteralDifferentiatedEffectiveDensityCarrier.volume = volume dataSet
  ; Carrier.LiteralDifferentiatedEffectiveDensityCarrier.radiusData =
      Radius114.canonicalCMP116CommonDomain (analyticDemands dataSet)
  }

bc1GeneratedPotentialIsCMP116LocalizedSum :
  (dataSet : BC1CanonicalPhysicalInputs) →
  ∀ background →
  Source.cmp109EffectivePotential
      (source dataSet) (scale dataSet) (volume dataSet) background
  ≡ Finite.localizedPotential
      (Carrier.finiteAction (bc1CanonicalCarrier dataSet)) background
bc1GeneratedPotentialIsCMP116LocalizedSum dataSet =
  Source.effectivePotentialIsLocalizedCompositeSum
    (source dataSet) (scale dataSet) (volume dataSet)

bc1CMP109PolarizationIsCMP116PhysicalHessian :
  (dataSet : BC1CanonicalPhysicalInputs) →
  ∀ background u v →
  Carrier.cmp109Polarization (bc1CanonicalCarrier dataSet) background u v
  ≡ Carrier.cmp116PhysicalMarkedHessian
      (bc1CanonicalCarrier dataSet) background u v
bc1CMP109PolarizationIsCMP116PhysicalHessian dataSet =
  Carrier.cmp109PolarizationIsCMP116PhysicalMarkedHessian
    (bc1CanonicalCarrier dataSet)

bc1CMP116HessianIsSameEffectivePotentialD2 :
  (dataSet : BC1CanonicalPhysicalInputs) →
  ∀ background u v →
  Carrier.cmp116PhysicalMarkedHessian
      (bc1CanonicalCarrier dataSet) background u v
  ≡ Finite.secondVariation (calculus dataSet)
      (Source.cmp109EffectivePotential
        (source dataSet) (scale dataSet) (volume dataSet))
      background u v
bc1CMP116HessianIsSameEffectivePotentialD2 dataSet =
  Carrier.cmp116MarkedHessianIsSecondVariationOfEffectivePotential
    (bc1CanonicalCarrier dataSet)

bc1CanonicalCarrierCompilerLevel : ProofLevel
bc1CanonicalCarrierCompilerLevel = machineChecked

bc1GeneratedActionLocalizedSumCompilerLevel : ProofLevel
bc1GeneratedActionLocalizedSumCompilerLevel = machineChecked

bc1SamePotentialHessianCompilerLevel : ProofLevel
bc1SamePotentialHessianCompilerLevel = machineChecked

-- Honest remaining BC1 physical seam after the BIDI compilation:
--
--   1. instantiate `source` by the repository's literal generated CMP109 action
--      and CMP116 localized activities on the same scale/volume/background;
--   2. instantiate `equation51` by the source-exact Eq.(5.1) polarization identity;
--   3. extract the finite normalized analytic demand constants from CMP116
--      (1.13)--(1.22).
--
-- No additional common-radius, finite-sum differentiation, Hessian-localization,
-- or same-potential theorem remains after those source identifications.
literalBC1CanonicalPhysicalInputsLevel : ProofLevel
literalBC1CanonicalPhysicalInputsLevel = conditional
