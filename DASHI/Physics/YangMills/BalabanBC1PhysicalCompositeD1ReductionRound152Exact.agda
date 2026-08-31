{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanBC1PhysicalCompositeD1ReductionRound152Exact where

------------------------------------------------------------------------
-- ROUND152: LOCALIZED D1 IDENTITY REDUCES TO ONE PHYSICAL COMPOSITE CHAIN RULE
--
-- Round118 already proves pointwise that each literal CMP116 localized activity
-- is the same physical composite activity after A=A(B).  Round143 supplies the
-- first-variation congruence law.  Therefore the only remaining componentwise
-- D1 physics is the derivative chain rule through the explicit background and
-- tangent transports; the localized-vs-composite function replacement is
-- theorem-generated.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanBC1PhysicalCompositeChainRuleRound118Exact as R118
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionFirstVariationRound142Exact as D1
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as R143
import DASHI.Physics.YangMills.BalabanBC1PhysicalCompositeFirstVariationRound145Exact as R145
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityFirstVariationRound105Exact as First

physicalCompositeFunction :
  ∀ {History Cell cutoff}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    {laws : R143.PresentCutBC2FirstVariationLinearity present}
    (family : R145.BC1PhysicalCompositeFirstVariationFamily present laws) →
  Finite.Component (Carrier.finiteAction (Present.bc1Carrier present)) →
  Finite.Configuration (Carrier.finiteAction (Present.bc1Carrier present)) → ℝ
physicalCompositeFunction family component background =
  let sourceFamily = R145.secondOrderFamily family
      activity = R118.physicalActivity sourceFamily component
  in
  Chain.localActivity activity
    (Chain.substitution activity
      (R118.toPhysicalBackground sourceFamily component background))

localizedActivityIsPhysicalCompositeFunction :
  ∀ {History Cell cutoff}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    {laws : R143.PresentCutBC2FirstVariationLinearity present}
    (family : R145.BC1PhysicalCompositeFirstVariationFamily present laws) →
  ∀ component background →
  Finite.localActivity (Carrier.finiteAction (Present.bc1Carrier present))
      component background
  ≡ physicalCompositeFunction family component background
localizedActivityIsPhysicalCompositeFunction family component background =
  R118.localizedActivityIsPhysicalComposite
    (R145.secondOrderFamily family) component background

localizedD1IsCompositeFunctionD1 :
  ∀ {History Cell cutoff}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    {laws : R143.PresentCutBC2FirstVariationLinearity present}
    (family : R145.BC1PhysicalCompositeFirstVariationFamily present laws) →
  ∀ component background tangent →
  D1.firstVariation (R143.asFirstVariationLinearity laws)
    (Finite.localActivity
      (Carrier.finiteAction (Present.bc1Carrier present)) component)
    background tangent
  ≡ D1.firstVariation (R143.asFirstVariationLinearity laws)
      (physicalCompositeFunction family component) background tangent
localizedD1IsCompositeFunctionD1 {present = present} {laws = laws}
    family component background tangent =
  R143.firstVariationCong laws
    (Finite.localActivity
      (Carrier.finiteAction (Present.bc1Carrier present)) component)
    (physicalCompositeFunction family component)
    (localizedActivityIsPhysicalCompositeFunction family component)
    background tangent

-- Stronger source interface: reuse the existing Round118 component family and
-- ask only for the actual first-order chain rule under its explicit transports.
record PhysicalCompositeD1ChainRule
    {History Cell : Set} {cutoff : Nat}
    (present : Present.PresentCutPhysicalSourceInputs History Cell cutoff)
    (laws : R143.PresentCutBC2FirstVariationLinearity present)
    (secondOrderFamily :
      R118.BC1PhysicalCompositeComponentFamily
        (R118.canonical (Present.bc1 present))) : Set₁ where
  field
    physicalCompositeFunctionD1IsSubstitutedD1 :
      ∀ component background tangent →
      let activity = R118.physicalActivity secondOrderFamily component
          composite = λ x →
            Chain.localActivity activity
              (Chain.substitution activity
                (R118.toPhysicalBackground secondOrderFamily component x))
      in
      D1.firstVariation (R143.asFirstVariationLinearity laws)
          composite background tangent
      ≡ First.substitutedFirstVariation activity
          (R118.toPhysicalBackground secondOrderFamily component background)
          (R118.toPhysicalTangent secondOrderFamily component tangent)

open PhysicalCompositeD1ChainRule public

asRound145PhysicalCompositeFirstVariationFamily :
  ∀ {History Cell cutoff present laws secondOrderFamily} →
  PhysicalCompositeD1ChainRule
    {History = History} {Cell = Cell} {cutoff = cutoff}
    present laws secondOrderFamily →
  R145.BC1PhysicalCompositeFirstVariationFamily present laws
asRound145PhysicalCompositeFirstVariationFamily
    {present = present} {laws = laws} {secondOrderFamily = sourceFamily} chain = record
  { R145.BC1PhysicalCompositeFirstVariationFamily.secondOrderFamily = sourceFamily
  ; R145.BC1PhysicalCompositeFirstVariationFamily.localizedD1IsPhysicalCompositeD1 =
      λ component background tangent →
        trans
          (R143.firstVariationCong laws
            (Finite.localActivity
              (Carrier.finiteAction (Present.bc1Carrier present)) component)
            (λ x →
              let activity = R118.physicalActivity sourceFamily component
              in Chain.localActivity activity
                  (Chain.substitution activity
                    (R118.toPhysicalBackground sourceFamily component x)))
            (R118.localizedActivityIsPhysicalComposite sourceFamily component)
            background tangent)
          (physicalCompositeFunctionD1IsSubstitutedD1
            chain component background tangent)
  }

round152BuildsRound145ComponentD1 :
  ∀ {History Cell cutoff present laws secondOrderFamily}
    (chain : PhysicalCompositeD1ChainRule
      {History = History} {Cell = Cell} {cutoff = cutoff}
      present laws secondOrderFamily) →
  ∀ component background tangent →
  D1.firstVariation (R143.asFirstVariationLinearity laws)
    (Finite.localActivity
      (Carrier.finiteAction (Present.bc1Carrier present)) component)
    background tangent
  ≡ First.substitutedFirstVariation
      (R118.physicalActivity secondOrderFamily component)
      (R118.toPhysicalBackground secondOrderFamily component background)
      (R118.toPhysicalTangent secondOrderFamily component tangent)
round152BuildsRound145ComponentD1 chain =
  R145.localizedD1IsPhysicalCompositeD1
    (asRound145PhysicalCompositeFirstVariationFamily chain)

bc1PhysicalCompositeD1ReductionCompilerLevel : ProofLevel
bc1PhysicalCompositeD1ReductionCompilerLevel = machineChecked

-- Remaining source theorem: first-variation chain rule for the exact Round118
-- physical composite under the declared background/tangent transports.  Pointwise
-- activity identity and localized-function replacement are no longer source debt.
literalPhysicalCompositeD1ChainRuleLevel : ProofLevel
literalPhysicalCompositeD1ChainRuleLevel = conditional
