{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119RegularEPreferredBC1Round223Exact where

------------------------------------------------------------------------
-- ROUND223 / DIRECT PREFERRED CMP119 E_k -> BC1
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119RegularEPreferredContinuationRound222Exact as Regular
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109Equation51LocalizedHessianRound103Exact as Eq51
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as Canon
import DASHI.Physics.YangMills.BalabanBC1CanonicalCarrierCompilerRound115Exact as BC1
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP119RegularESourceProjectionRound221Exact as ESource

record PreferredRegularEBC1Inputs
    {trajectory split inputs projection}
    (regular : Regular.PreferredRegularERealization
      {trajectory = trajectory} {split = split} {inputs = inputs} projection) : Set₁ where
  field
    calculus :
      Finite.SecondVariationLinearity
        (Regular.Background regular) (Regular.Tangent regular)

    equation51 :
      Eq51.CMP109Equation51OnContinuation
        (Regular.asCMP109116Continuation regular) calculus

    scale : Nat
    volume : Regular.Volume regular

    analyticDemands : Canon.CMP116FiniteNormalizedAnalyticDemands

open PreferredRegularEBC1Inputs public

asBC1CanonicalPhysicalInputs :
  ∀ {trajectory split inputs projection regular} →
  PreferredRegularEBC1Inputs
    {trajectory = trajectory} {split = split} {inputs = inputs}
    {projection = projection} regular →
  BC1.BC1CanonicalPhysicalInputs
asBC1CanonicalPhysicalInputs {regular = regular} dataSet = record
  { BC1.BC1CanonicalPhysicalInputs.source =
      Regular.asCMP109116Continuation regular
  ; BC1.BC1CanonicalPhysicalInputs.calculus = calculus dataSet
  ; BC1.BC1CanonicalPhysicalInputs.equation51 = equation51 dataSet
  ; BC1.BC1CanonicalPhysicalInputs.scale = scale dataSet
  ; BC1.BC1CanonicalPhysicalInputs.volume = volume dataSet
  ; BC1.BC1CanonicalPhysicalInputs.analyticDemands = analyticDemands dataSet
  }

bc1PotentialIsSelectedCMP119RegularE :
  ∀ {trajectory split inputs projection regular}
    (dataSet : PreferredRegularEBC1Inputs
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {projection = projection} regular) →
  ∀ background →
  Carrier.effectivePotential
      (BC1.bc1CanonicalCarrier (asBC1CanonicalPhysicalInputs dataSet)) background
  ≡ Regular.evaluateRegularE regular
      (ESource.selectedRegularE projection (scale dataSet)) background
bc1PotentialIsSelectedCMP119RegularE dataSet background = refl

preferredRegularEBC1CompilerLevel : ProofLevel
preferredRegularEBC1CompilerLevel = machineChecked

preferredRegularEBC1SamePotentialLevel : ProofLevel
preferredRegularEBC1SamePotentialLevel = machineChecked

-- Remaining physical inputs are now exactly the source projection, pointwise /
-- localized E realization, D2 calculus, Eq.(5.1) binding and four normalized
-- CMP116 analytic-demand constants.
literalPreferredRegularEBC1InputsLevel : ProofLevel
literalPreferredRegularEBC1InputsLevel = conditional
