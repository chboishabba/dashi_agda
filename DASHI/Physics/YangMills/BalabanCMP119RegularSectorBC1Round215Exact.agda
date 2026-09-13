{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119RegularSectorBC1Round215Exact where

------------------------------------------------------------------------
-- ROUND215 / DIRECT CMP119 E_k -> BC1 CONSTRUCTOR
--
-- BC1 consumes a CMP109/CMP116 continuation.  Round215 now constructs that
-- continuation directly from the literal CMP119 regular small-field E_k sector
-- on the RAW source state.  Section-2 predicates remain theorem output rather
-- than data-model assumptions.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as CMP119
import DASHI.Physics.YangMills.BalabanCMP119RegularSectorCMP109116Round215Exact as Regular
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109Equation51LocalizedHessianRound103Exact as Eq51
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as Canon
import DASHI.Physics.YangMills.BalabanBC1CanonicalCarrierCompilerRound115Exact as BC1
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier

record CMP119RegularSectorBC1Inputs
    {Density Background Fluctuation Action WilsonTerm SmallFieldTerm
      RTerm BoundaryTerm Vacuum : Set}
    {source : CMP119.CMP119SourceNativeRawState
      Density Background Fluctuation Action WilsonTerm SmallFieldTerm
      RTerm BoundaryTerm Vacuum}
    (regular : Regular.CMP119RegularSectorRealization source) : Set₁ where
  field
    calculus :
      Finite.SecondVariationLinearity Background (Regular.Tangent regular)

    equation51 :
      Eq51.CMP109Equation51OnContinuation
        (Regular.asCMP109116Continuation regular) calculus

    scale : Nat
    volume : Regular.Volume regular

    analyticDemands : Canon.CMP116FiniteNormalizedAnalyticDemands

open CMP119RegularSectorBC1Inputs public

asBC1CanonicalPhysicalInputs :
  ∀ {Density Background Fluctuation Action WilsonTerm SmallFieldTerm
      RTerm BoundaryTerm Vacuum source regular} →
  CMP119RegularSectorBC1Inputs
    {Density} {Background} {Fluctuation} {Action} {WilsonTerm} {SmallFieldTerm}
    {RTerm} {BoundaryTerm} {Vacuum} {source} regular →
  BC1.BC1CanonicalPhysicalInputs
asBC1CanonicalPhysicalInputs {regular = regular} inputs = record
  { BC1.BC1CanonicalPhysicalInputs.source =
      Regular.asCMP109116Continuation regular
  ; BC1.BC1CanonicalPhysicalInputs.calculus = calculus inputs
  ; BC1.BC1CanonicalPhysicalInputs.equation51 = equation51 inputs
  ; BC1.BC1CanonicalPhysicalInputs.scale = scale inputs
  ; BC1.BC1CanonicalPhysicalInputs.volume = volume inputs
  ; BC1.BC1CanonicalPhysicalInputs.analyticDemands = analyticDemands inputs
  }

bc1EffectivePotentialIsLiteralCMP119RegularE :
  ∀ {Density Background Fluctuation Action WilsonTerm SmallFieldTerm
      RTerm BoundaryTerm Vacuum source regular}
    (inputs : CMP119RegularSectorBC1Inputs
      {Density} {Background} {Fluctuation} {Action} {WilsonTerm} {SmallFieldTerm}
      {RTerm} {BoundaryTerm} {Vacuum} {source} regular) →
  ∀ background →
  Carrier.effectivePotential
      (BC1.bc1CanonicalCarrier (asBC1CanonicalPhysicalInputs inputs)) background
  ≡ Regular.evaluateRegularTerm regular
      (CMP119.regularSmallFieldTerm source (scale inputs)) background
bc1EffectivePotentialIsLiteralCMP119RegularE inputs background = refl

cmp119RegularSectorBC1CompilerLevel : ProofLevel
cmp119RegularSectorBC1CompilerLevel = machineChecked

cmp119RegularSectorBC1SamePotentialLevel : ProofLevel
cmp119RegularSectorBC1SamePotentialLevel = machineChecked

literalCMP119RegularSectorBC1InputsLevel : ProofLevel
literalCMP119RegularSectorBC1InputsLevel = conditional
