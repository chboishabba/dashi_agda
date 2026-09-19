module DASHI.Foundations.HyperformChartGluingExact where

------------------------------------------------------------------------
-- GENERIC CHART / SAME-OBJECT / OBSERVER-FIBRE / HYPERFABRIC GLUING
--
-- DASHI CONTRIBUTION
--
-- This is the reusable architecture underneath the analytic-j / 369 /
-- pants / hyperfabric cross-pollination.
--
-- It deliberately separates three notions that must not be collapsed:
--
--   1. two presentations of the same value, with an explicit overlap witness;
--   2. a coarse observation of a fine point, with the lost information retained
--      as an explicit observer fibre;
--   3. a contextual fabric lift, where a local observation plus independent
--      context constructs a larger fabric point and projects back exactly.
--
-- No cardinality coincidence, shared notation, or common downstream consumer
-- creates a same-object theorem.  Every weld is carried by a field below.
------------------------------------------------------------------------

open import Agda.Primitive using (Set; Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

record SameObjectChartGluing
    (Point Value : Set)
    (_≈_ : Value → Value → Set) : Set₁ where
  field
    chartA : Point → Value
    chartB : Point → Value
    glueOnOverlap :
      (point : Point) →
      _≈_ (chartA point) (chartB point)

open SameObjectChartGluing public

record ObserverWithFibre
    (Fine Coarse : Set) : Set₁ where
  field
    observe : Fine → Coarse

open ObserverWithFibre public

ObserverFibre :
  ∀ {Fine Coarse} →
  ObserverWithFibre Fine Coarse →
  Coarse →
  Fine →
  Set
ObserverFibre observer coarse fine =
  observe observer fine ≡ coarse

pointLiesInOwnObserverFibre :
  ∀ {Fine Coarse}
    (observer : ObserverWithFibre Fine Coarse)
    (fine : Fine) →
  ObserverFibre observer (observe observer fine) fine
pointLiesInOwnObserverFibre observer fine = refl

record ContextualFabricLift
    (Fine Local Context Fabric : Set) : Set₁ where
  field
    observeLocal : Fine → Local
    assembleFabric : Fine → Context → Fabric
    projectLocal : Fabric → Local
    projectLocalLaw :
      (fine : Fine) →
      (context : Context) →
      projectLocal (assembleFabric fine context)
      ≡ observeLocal fine

open ContextualFabricLift public

record HyperformChartGluingBoundary : Set where
  constructor hyperform-chart-gluing-boundary
  field
    sharedObservableImpliesSameObject : Bool
    sameObjectRequiresExplicitOverlapWitness : Bool
    observerMayForgetFineInformation : Bool
    observerFibreRetainedExplicitly : Bool
    contextualFabricRequiresIndependentContext : Bool
    fabricProjectionBackToLocalRequired : Bool

open HyperformChartGluingBoundary public

canonicalHyperformChartGluingBoundary :
  HyperformChartGluingBoundary
canonicalHyperformChartGluingBoundary =
  hyperform-chart-gluing-boundary
    false true true true true true
