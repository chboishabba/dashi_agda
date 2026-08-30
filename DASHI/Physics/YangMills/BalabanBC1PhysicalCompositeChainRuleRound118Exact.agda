{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanBC1PhysicalCompositeChainRuleRound118Exact where

------------------------------------------------------------------------
-- ROUND118 BC1 BIDI: THE CMP116 HESSIAN IS THE PHYSICAL B-COMPOSITE HESSIAN
--
-- Do not identify D_A^2 E with Eq.(5.1).  The source local activity is evaluated
-- after the analytic background substitution A=A(B), so the physical Hessian is
--
--   D_B^2(E o A)[u,v]
--     = D_A^2 E[A'u,A'v] + D_A E[A''(u,v)].
--
-- Round103 already owns this exact chain rule in
-- `SubstitutedActivitySecondVariation`.  This file welds that owner to the SAME
-- localized component appearing in Round115's CMP109/CMP116 continuation.
-- Thus the substitution-curvature term cannot disappear by a naming shortcut.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _+ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanBC1CanonicalCarrierCompilerRound115Exact as BC1

record BC1PhysicalCompositeComponentFamily
    (inputs : BC1.BC1CanonicalPhysicalInputs) : Set₁ where
  field
    physicalActivity : Source.Component (BC1.source inputs) →
      Chain.SubstitutedActivitySecondVariation

    toPhysicalBackground :
      (component : Source.Component (BC1.source inputs)) →
      Source.Background (BC1.source inputs) →
      Chain.Background (physicalActivity component)

    toPhysicalTangent :
      (component : Source.Component (BC1.source inputs)) →
      Source.Tangent (BC1.source inputs) →
      Chain.BackgroundTangent (physicalActivity component)

    localizedActivityIsPhysicalComposite :
      ∀ component background →
      Source.cmp116PhysicalLocalizedActivity
          (BC1.source inputs) (BC1.scale inputs) (BC1.volume inputs)
          component background
      ≡ Chain.localActivity (physicalActivity component)
          (Chain.substitution (physicalActivity component)
            (toPhysicalBackground component background))

    localizedD2IsPhysicalCompositeD2 :
      ∀ component background u v →
      Finite.secondVariation (BC1.calculus inputs)
        (Source.cmp116PhysicalLocalizedActivity
          (BC1.source inputs) (BC1.scale inputs) (BC1.volume inputs) component)
        background u v
      ≡ Chain.physicalSecondVariation (physicalActivity component)
          (toPhysicalBackground component background)
          (toPhysicalTangent component u)
          (toPhysicalTangent component v)

open BC1PhysicalCompositeComponentFamily public

componentD2IncludesSubstitutionCurvature :
  ∀ {inputs}
    (family : BC1PhysicalCompositeComponentFamily inputs)
    component background u v →
  Finite.secondVariation (BC1.calculus inputs)
    (Source.cmp116PhysicalLocalizedActivity
      (BC1.source inputs) (BC1.scale inputs) (BC1.volume inputs) component)
    background u v
  ≡ Chain.intrinsicHessianTerm (physicalActivity family component)
      (toPhysicalBackground family component background)
      (toPhysicalTangent family component u)
      (toPhysicalTangent family component v)
    +ℝ Chain.substitutionCurvatureTerm (physicalActivity family component)
      (toPhysicalBackground family component background)
      (toPhysicalTangent family component u)
      (toPhysicalTangent family component v)
componentD2IncludesSubstitutionCurvature family component background u v =
  trans
    (localizedD2IsPhysicalCompositeD2 family component background u v)
    (Chain.physicalHessianSplitsIntrinsicPlusSubstitution
      (physicalActivity family component)
      (toPhysicalBackground family component background)
      (toPhysicalTangent family component u)
      (toPhysicalTangent family component v))

record BC1PhysicalCompositeInputs : Set₁ where
  field
    canonical : BC1.BC1CanonicalPhysicalInputs
    compositeFamily : BC1PhysicalCompositeComponentFamily canonical

open BC1PhysicalCompositeInputs public

bc1GlobalHessianIsSamePotentialD2 :
  (dataSet : BC1PhysicalCompositeInputs) →
  ∀ background u v →
  let inputs = canonical dataSet
  in
  Carrier.cmp116PhysicalMarkedHessian
      (BC1.bc1CanonicalCarrier inputs) background u v
  ≡ Finite.secondVariation (BC1.calculus inputs)
      (Source.cmp109EffectivePotential
        (BC1.source inputs) (BC1.scale inputs) (BC1.volume inputs))
      background u v
bc1GlobalHessianIsSamePotentialD2 dataSet =
  BC1.bc1CMP116HessianIsSameEffectivePotentialD2 (canonical dataSet)

bc1PhysicalCompositeChainRuleCompilerLevel : ProofLevel
bc1PhysicalCompositeChainRuleCompilerLevel = machineChecked

bc1PhysicalCompositeSamePotentialCompilerLevel : ProofLevel
bc1PhysicalCompositeSamePotentialCompilerLevel = machineChecked

literalBC1PhysicalCompositeComponentInstantiationLevel : ProofLevel
literalBC1PhysicalCompositeComponentInstantiationLevel = conditional
