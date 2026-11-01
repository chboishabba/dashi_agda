module DASHI.Core.RangeRestrictedProjectionComposition where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.ReopenableProjectionComposition as Reopenable
import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- Range-restricted composition theorem.
--
-- #521 already owns exact reopenable-projection composition and the stronger
-- globally-injective post-composition safety theorem.  The only extra theorem
-- retained here is the genuinely weaker hypothesis needed for many semantic
-- pipelines: the second observer need only reflect equality on states that are
-- actually in the image of the first projection.
------------------------------------------------------------------------

record CompositeEqualityReflectsOnImage
    {X Y Z : Set}
    (first : Reopenable.ExactReopenableProjection X Y)
    (second : Reopenable.ExactReopenableProjection Y Z) : Set₁ where
  constructor compositeEqualityReflectsOnImage
  field
    reflectCompositeEquality :
      ∀ {left right : X} →
      Reopenable.project second (Reopenable.project first left)
      ≡ Reopenable.project second (Reopenable.project first right) →
      Reopenable.project first left ≡ Reopenable.project first right

open CompositeEqualityReflectsOnImage public

safeCompositionUnderImageReflection :
  ∀ {X Y Z Action : Set}
    {system : Dependency.DependentActionSystem X Action}
    (first : Reopenable.ExactReopenableProjection X Y)
    (second : Reopenable.ExactReopenableProjection Y Z) →
  Dynamic.DynamicConsumerSafety system (Reopenable.project first) →
  CompositeEqualityReflectsOnImage first second →
  Dynamic.DynamicConsumerSafety
    system
    (Reopenable.project
      (Reopenable.composeExactReopenableProjection first second))
safeCompositionUnderImageReflection first second firstSafety reflection =
  Dynamic.dynamicConsumerSafety
    (λ sameComposite leftExecution rightExecution →
      cong (Reopenable.project second)
        (Dynamic.traceCongruence firstSafety
          (reflectCompositeEquality reflection sameComposite)
          leftExecution
          rightExecution))

------------------------------------------------------------------------
-- Global injectivity implies the weaker image-reflection condition.
------------------------------------------------------------------------

globalInjectivitySuppliesImageReflection :
  ∀ {X Y Z : Set}
    (first : Reopenable.ExactReopenableProjection X Y)
    (second : Reopenable.ExactReopenableProjection Y Z) →
  Dynamic.Injective (Reopenable.project second) →
  CompositeEqualityReflectsOnImage first second
globalInjectivitySuppliesImageReflection first second injective =
  compositeEqualityReflectsOnImage injective
