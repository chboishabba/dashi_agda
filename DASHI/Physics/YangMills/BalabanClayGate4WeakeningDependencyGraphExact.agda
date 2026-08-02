module DASHI.Physics.YangMills.BalabanClayGate4WeakeningDependencyGraphExact where

open import Agda.Builtin.Sigma using (Σ; _,_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Dependency-graph propagation of weakening-variable locality.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization II: Localization, Exponentiation, and Bounds
-- for the R-Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- Physical activities are not primitive products only.  A weakening variable
-- first influences local factors, which feed local operators/determinants and
-- finally a connected activity.  This module packages the relational
-- composition and the zero-derivative passage through that dependency graph.
------------------------------------------------------------------------

record TwoStageSupport
    (Primitive Intermediate Output : Set) : Set₁ where
  field
    primitiveSupportsIntermediate : Primitive → Intermediate → Set
    intermediateSupportsOutput : Intermediate → Output → Set

open TwoStageSupport public

CompositeSupport :
  ∀ {Primitive Intermediate Output} →
  TwoStageSupport Primitive Intermediate Output →
  Primitive → Output → Set
CompositeSupport graph primitive output =
  Σ _ (λ intermediate →
    Σ (primitiveSupportsIntermediate graph primitive intermediate)
      (λ _ → intermediateSupportsOutput graph intermediate output))

OutsideCompositeSupport :
  ∀ {Primitive Intermediate Output} →
  TwoStageSupport Primitive Intermediate Output →
  Primitive → Output → Set
OutsideCompositeSupport {Intermediate = Intermediate}
    graph primitive output =
  ∀ intermediate →
  intermediateSupportsOutput graph intermediate output →
  primitiveSupportsIntermediate graph primitive intermediate →
  Agda.Builtin.Sigma.Σ Agda.Builtin.Sigma.⊥ (λ impossible → impossible)

-- A constructive negation carrier independent of the standard-library
-- bottom type.  The dependency theorem below uses this directly.
data Empty : Set where

Not : Set → Set
Not proposition = proposition → Empty

OutsideComposite :
  ∀ {Primitive Intermediate Output} →
  TwoStageSupport Primitive Intermediate Output →
  Primitive → Output → Set
OutsideComposite {Intermediate = Intermediate} graph primitive output =
  ∀ intermediate →
  intermediateSupportsOutput graph intermediate output →
  Not (primitiveSupportsIntermediate graph primitive intermediate)

outsideCompositeRejectsCompositeSupport :
  ∀ {Primitive Intermediate Output}
    {graph : TwoStageSupport Primitive Intermediate Output}
    {primitive output} →
  OutsideComposite graph primitive output →
  Not (CompositeSupport graph primitive output)
outsideCompositeRejectsCompositeSupport outside
    (intermediate , primitiveSupport , outputSupport) =
  outside intermediate outputSupport primitiveSupport

record DerivativeDependencyGraph
    (Primitive Intermediate Output Derivative : Set) : Set₁ where
  field
    support : TwoStageSupport Primitive Intermediate Output
    zeroDerivative : Derivative

    intermediateDerivative : Primitive → Intermediate → Derivative
    outputDerivative : Primitive → Output → Derivative

    intermediateDerivativeVanishesOutside : ∀ primitive intermediate →
      Not (primitiveSupportsIntermediate support primitive intermediate) →
      intermediateDerivative primitive intermediate ≡ zeroDerivative

    allContributorsZeroImpliesOutputZero : ∀ primitive output →
      (∀ intermediate →
        intermediateSupportsOutput support intermediate output →
        intermediateDerivative primitive intermediate ≡ zeroDerivative) →
      outputDerivative primitive output ≡ zeroDerivative

open DerivativeDependencyGraph public

outputDerivativeVanishesOutsideCompositeSupport :
  ∀ {Primitive Intermediate Output Derivative}
    (graph : DerivativeDependencyGraph
      Primitive Intermediate Output Derivative)
    primitive output →
  OutsideComposite (support graph) primitive output →
  outputDerivative graph primitive output ≡ zeroDerivative graph
outputDerivativeVanishesOutsideCompositeSupport graph primitive output outside =
  allContributorsZeroImpliesOutputZero graph primitive output
    (λ intermediate contributes →
      intermediateDerivativeVanishesOutside graph primitive intermediate
        (outside intermediate contributes))

weakeningSupportRelationalCompositionLevel : ProofLevel
weakeningSupportRelationalCompositionLevel = machineChecked

weakeningDependencyDerivativePropagationLevel : ProofLevel
weakeningDependencyDerivativePropagationLevel = machineChecked

physicalWeakeningDependencyGraphInputsLevel : ProofLevel
physicalWeakeningDependencyGraphInputsLevel = conditional
