{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanBC1PhysicalCompositeFirstVariationRound145Exact where

------------------------------------------------------------------------
-- ROUND145: LITERAL LOCALIZED D1 = PHYSICAL COMPOSITE D1, COMPONENT BY COMPONENT
--
-- Round118 already owns the exact component family and the corresponding D2
-- identification including substitution curvature.  Stress is first order.
-- This file adds the missing per-component D1 identification and proves that the
-- whole finite localized first-variation sum is therefore the sum of the
-- physical substituted component first variations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _+ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanBC1PhysicalCompositeChainRuleRound118Exact as Composite
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityFirstVariationRound105Exact as First
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionFirstVariationRound142Exact as D1
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as R143

record BC1PhysicalCompositeFirstVariationFamily
    {History Cell : Set} {cutoff : Nat}
    (present : Present.PresentCutPhysicalSourceInputs History Cell cutoff)
    (laws : R143.PresentCutBC2FirstVariationLinearity present) : Set₁ where
  field
    -- Reuse the exact Round118 component family rather than creating another
    -- collection of local stress activities.
    secondOrderFamily :
      Composite.BC1PhysicalCompositeComponentFamily
        (Composite.canonical (Present.bc1 present))

    localizedD1IsPhysicalCompositeD1 :
      ∀ component background tangent →
      D1.firstVariation (R143.asFirstVariationLinearity laws)
        (Finite.localActivity
          (Carrier.finiteAction (Present.bc1Carrier present)) component)
        background tangent
      ≡ First.substitutedFirstVariation
          (Composite.physicalActivity secondOrderFamily component)
          (Composite.toPhysicalBackground secondOrderFamily component background)
          (Composite.toPhysicalTangent secondOrderFamily component tangent)

open BC1PhysicalCompositeFirstVariationFamily public

physicalComponentFirstVariation :
  ∀ {History Cell cutoff}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    {laws : R143.PresentCutBC2FirstVariationLinearity present} →
  BC1PhysicalCompositeFirstVariationFamily present laws →
  Finite.Component (Carrier.finiteAction (Present.bc1Carrier present)) →
  Finite.Configuration (Carrier.finiteAction (Present.bc1Carrier present)) →
  Finite.Tangent (Carrier.finiteAction (Present.bc1Carrier present)) → ℝ
physicalComponentFirstVariation family component background tangent =
  First.substitutedFirstVariation
    (Composite.physicalActivity (secondOrderFamily family) component)
    (Composite.toPhysicalBackground
      (secondOrderFamily family) component background)
    (Composite.toPhysicalTangent
      (secondOrderFamily family) component tangent)

physicalComponentFirstVariationValues :
  ∀ {History Cell cutoff}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    {laws : R143.PresentCutBC2FirstVariationLinearity present} →
  BC1PhysicalCompositeFirstVariationFamily present laws →
  Finite.Configuration (Carrier.finiteAction (Present.bc1Carrier present)) →
  Finite.Tangent (Carrier.finiteAction (Present.bc1Carrier present)) → List ℝ
physicalComponentFirstVariationValues {present = present} family background tangent =
  Finite.mapList
    (λ component → physicalComponentFirstVariation family component background tangent)
    (Finite.components (Carrier.finiteAction (Present.bc1Carrier present)))

sumComponentD1Cong :
  ∀ {History Cell cutoff}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    {laws : R143.PresentCutBC2FirstVariationLinearity present}
    (family : BC1PhysicalCompositeFirstVariationFamily present laws)
    background tangent
    (components : List
      (Finite.Component (Carrier.finiteAction (Present.bc1Carrier present)))) →
  Finite.sumℝ
    (Finite.mapList
      (λ component →
        D1.firstVariation (R143.asFirstVariationLinearity laws)
          (Finite.localActivity
            (Carrier.finiteAction (Present.bc1Carrier present)) component)
          background tangent)
      components)
  ≡ Finite.sumℝ
    (Finite.mapList
      (λ component → physicalComponentFirstVariation family component background tangent)
      components)
sumComponentD1Cong family background tangent [] = refl
sumComponentD1Cong {present = present} {laws = laws}
    family background tangent (component ∷ components) =
  let
    localHead =
      D1.firstVariation (R143.asFirstVariationLinearity laws)
        (Finite.localActivity
          (Carrier.finiteAction (Present.bc1Carrier present)) component)
        background tangent
    physicalHead =
      physicalComponentFirstVariation family component background tangent
    physicalTail =
      Finite.sumℝ
        (Finite.mapList
          (λ c → physicalComponentFirstVariation family c background tangent)
          components)
    tailEq = sumComponentD1Cong family background tangent components
    headEq = localizedD1IsPhysicalCompositeD1 family component background tangent
  in
  trans
    (cong (λ tail → localHead +ℝ tail) tailEq)
    (cong (λ head → head +ℝ physicalTail) headEq)

finiteLocalizedD1IsPhysicalCompositeD1Sum :
  ∀ {History Cell cutoff}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    {laws : R143.PresentCutBC2FirstVariationLinearity present}
    (family : BC1PhysicalCompositeFirstVariationFamily present laws) →
  ∀ background tangent →
  D1.finiteLocalizedFirstVariation
      (Carrier.finiteAction (Present.bc1Carrier present))
      (R143.asFirstVariationLinearity laws)
      background tangent
  ≡ Finite.sumℝ
      (physicalComponentFirstVariationValues family background tangent)
finiteLocalizedD1IsPhysicalCompositeD1Sum {present = present}
    family background tangent =
  sumComponentD1Cong family background tangent
    (Finite.components (Carrier.finiteAction (Present.bc1Carrier present)))

bc1PhysicalCompositeFirstVariationCompilerLevel : ProofLevel
bc1PhysicalCompositeFirstVariationCompilerLevel = machineChecked

-- Source leaf: the literal derivative of each localized CMP116 activity, in the
-- BC2 derivative calculus, is the Round118 physical substituted first variation
-- of that SAME component.  Once supplied, the global finite sum is automatic.
literalBC1PhysicalCompositeFirstVariationLevel : ProofLevel
literalBC1PhysicalCompositeFirstVariationLevel = conditional
