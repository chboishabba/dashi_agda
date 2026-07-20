module DASHI.Codec.TriadicExplodedTransformCompletion where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Data.Nat using (_≤_)

import DASHI.Codec.TriadicExplodedTransformBridge as Bridge
import DASHI.Geometry.TriadicExplodedTransformCrossPollination as Cross
import DASHI.Geometry.TriadicExplodedTransformTheorems as Thm
import DASHI.Geometry.TriadicExplodedTransformTower as Tower

private
  variable
    ℓG ℓC ℓB ℓD : Level

record CompletedExplodedChart
  (G : Set ℓG)
  (C : Set ℓC)
  (Block : Set ℓB)
  (Distance : Set ℓD)
  (depth : Nat) : Set (lsuc (ℓG ⊔ ℓC ⊔ ℓB ⊔ ℓD)) where
  field
    affine : Thm.AffineWarp G
    firstAtom : Tower.AtomicTransform G
    secondAtom : Tower.AtomicTransform G
    atomNoninterference : Thm.StronglyNoninterfering firstAtom secondAtom
    codecAddress : Thm.CodecPartitionAddress depth
    beforeCost : Thm.ChartCost
    afterCost : Thm.ChartCost
    refinementBound : Thm.ChartRefinementBound beforeCost afterCost
    approximation : Thm.MetricQualifiedApproximation G Block Distance
    causalChart : Bridge.CausalChart G

open CompletedExplodedChart public

completed-chart-affine-roundtrip-left :
  ∀ {G : Set ℓG} {C : Set ℓC} {Block : Set ℓB}
    {Distance : Set ℓD} {depth : Nat} →
  (chart : CompletedExplodedChart G C Block Distance depth) →
  (s : Tower.State G C) → (g : G) → (c : C) →
  Tower.pullback (Thm.inverse (affine chart))
    (Tower.pullback (Thm.map (affine chart)) s) g c ≡ s g c
completed-chart-affine-roundtrip-left chart =
  Thm.pullback-inverse-left (affine chart)

completed-chart-atoms-commute :
  ∀ {G : Set ℓG} {C : Set ℓC} {Block : Set ℓB}
    {Distance : Set ℓD} {depth : Nat} →
  (chart : CompletedExplodedChart G C Block Distance depth) →
  (s : Tower.State G C) → (g : G) → (c : C) →
  Tower.applyAtomic (firstAtom chart)
    (Tower.applyAtomic (secondAtom chart) s) g c
  ≡ Tower.applyAtomic (secondAtom chart)
    (Tower.applyAtomic (firstAtom chart) s) g c
completed-chart-atoms-commute chart =
  Thm.atomic-commutes-under-noninterference
    (firstAtom chart) (secondAtom chart) (atomNoninterference chart)

completed-chart-address-roundtrip :
  ∀ {G : Set ℓG} {C : Set ℓC} {Block : Set ℓB}
    {Distance : Set ℓD} {depth : Nat} →
  (chart : CompletedExplodedChart G C Block Distance depth) →
  Thm.fromSSPAddress (Thm.toSSPAddress (codecAddress chart))
  ≡ codecAddress chart
completed-chart-address-roundtrip chart =
  Thm.fromSSP-toSSP-address (codecAddress chart)

completed-chart-mdl-nonincreasing :
  ∀ {G : Set ℓG} {C : Set ℓC} {Block : Set ℓB}
    {Distance : Set ℓD} {depth : Nat} →
  (chart : CompletedExplodedChart G C Block Distance depth) →
  Thm.chartDescriptionLength (afterCost chart)
  ≤ Thm.chartDescriptionLength (beforeCost chart)
completed-chart-mdl-nonincreasing chart =
  Thm.chart-refinement-implies-mdl-nonincreasing (refinementBound chart)

completed-chart-piecewise-bound :
  ∀ {G : Set ℓG} {C : Set ℓC} {Block : Set ℓB}
    {Distance : Set ℓD} {depth : Nat} →
  (chart : CompletedExplodedChart G C Block Distance depth) →
  (g : G) →
  Thm.Within (approximation chart)
    (Thm.distance (approximation chart)
      (Thm.piecewiseAffine (approximation chart) g)
      (Thm.target (approximation chart) g))
    (Thm.tolerance (approximation chart))
completed-chart-piecewise-bound chart =
  Thm.piecewise-affine-inherits-local-bound (approximation chart)

canonicalCarrierAvailable = Cross.canonicalSSPTritCarrierIsAvailable
currentMDLRouteAvailable = Cross.currentW9MDLRouteIsAvailable
