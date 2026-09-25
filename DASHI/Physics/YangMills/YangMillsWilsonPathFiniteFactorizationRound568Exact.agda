{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsWilsonPathFiniteFactorizationRound568Exact where

------------------------------------------------------------------------
-- GOAL-1 A3/C0 / ROUND568:
-- A WILSON LOOP FACTORS THROUGH FINITELY MANY PATH-EDGE VALUES
--
-- CompactLieLatticeGauge.Path is an inductive finite path.  Therefore the
-- holonomy, and hence every class-function Wilson loop observable, depends only
-- on the finite tuple of group elements carried by those path edges.
--
-- This is generic lattice-gauge algebra, not a new YM analytic estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Relation.Binary.PropositionalEquality using (sym)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.CompactLieGroupCore

import DASHI.Physics.YangMills.CompactLieLatticeGauge as Lattice
import DASHI.Physics.YangMills.YangMillsWilsonLocalObservableFamilyRound529Exact as R529
import DASHI.Physics.YangMills.YangMillsSelectedWilsonFiniteProjectionRound565Exact as R565

data PathValues
    {Vertex GroupElement : Set}
    {Edge : Vertex → Vertex → Set}
    : ∀ {start finish} →
      Lattice.Path Edge start finish → Set where
  emptyValues :
    ∀ {point} →
    PathValues
      (Lattice.empty {x = point})

  stepValues :
    ∀ {start middle finish}
      {edge : Edge start middle}
      {rest : Lattice.Path Edge middle finish} →
    GroupElement →
    PathValues rest →
    PathValues (edge Lattice.▷ rest)

projectPathValues :
  ∀ {Vertex GroupElement : Set}
    {Edge : Vertex → Vertex → Set}
    {start finish}
    (field : Lattice.GaugeField {G = GroupElement} Edge)
    (path : Lattice.Path Edge start finish) →
  PathValues path
projectPathValues field Lattice.empty =
  emptyValues
projectPathValues field
    (edge Lattice.▷ rest) =
  stepValues
    (field start middle edge)
    (projectPathValues field rest)

holonomyFromPathValues :
  ∀ {Vertex GroupElement : Set}
    {Edge : Vertex → Vertex → Set}
    {start finish}
    (H : Group GroupElement)
    (path : Lattice.Path Edge start finish) →
  PathValues path →
  GroupElement
holonomyFromPathValues H Lattice.empty emptyValues =
  identity H
holonomyFromPathValues H
    (edge Lattice.▷ rest)
    (stepValues value values) =
  multiply H value
    (holonomyFromPathValues H rest values)

projectedHolonomyIsLiteralHolonomy :
  ∀ {Vertex GroupElement : Set}
    {Edge : Vertex → Vertex → Set}
    {start finish}
    (H : Group GroupElement)
    (field : Lattice.GaugeField {G = GroupElement} Edge)
    (path : Lattice.Path Edge start finish) →
  holonomyFromPathValues H path
    (projectPathValues field path)
  ≡
  Lattice.holonomy H field path
projectedHolonomyIsLiteralHolonomy H field Lattice.empty =
  refl
projectedHolonomyIsLiteralHolonomy H field
    (edge Lattice.▷ rest)
  rewrite projectedHolonomyIsLiteralHolonomy H field rest =
  refl

projectedWilsonValue :
  ∀ {Configuration Position Vertex GroupElement Edge H}
    (source :
      R529.WilsonLocalObservableAt
        Configuration Position Vertex GroupElement Edge H)
    (position : Position) →
  PathValues (R529.boundaryAt source position) →
  ℝ
projectedWilsonValue {H = H} source position values =
  R529.classValue source
    (holonomyFromPathValues H
      (R529.boundaryAt source position)
      values)

wilsonObservableFactorsThroughPathValues :
  ∀ {Configuration Position Vertex GroupElement Edge H}
    (source :
      R529.WilsonLocalObservableAt
        Configuration Position Vertex GroupElement Edge H)
    position configuration →
  R529.wilsonObservable source position configuration
  ≡
  projectedWilsonValue source position
    (projectPathValues
      (R529.decode source configuration)
      (R529.boundaryAt source position))
wilsonObservableFactorsThroughPathValues {H = H}
    source position configuration =
  cong (R529.classValue source)
    (symProjected H source position configuration)
  where
  symProjected :
    ∀ {Configuration Position Vertex GroupElement Edge}
      (H : Group GroupElement)
      (source :
        R529.WilsonLocalObservableAt
          Configuration Position Vertex GroupElement Edge H)
      position configuration →
    Lattice.holonomy H
      (R529.decode source configuration)
      (R529.boundaryAt source position)
    ≡
    holonomyFromPathValues H
      (R529.boundaryAt source position)
      (projectPathValues
        (R529.decode source configuration)
        (R529.boundaryAt source position))
  symProjected H source position configuration =
    sym
      (projectedHolonomyIsLiteralHolonomy H
        (R529.decode source configuration)
        (R529.boundaryAt source position))

asFiniteProjectiveFactorization :
  ∀ {Configuration Position Vertex GroupElement Edge H}
    (source :
      R529.WilsonLocalObservableAt
        Configuration Position Vertex GroupElement Edge H) →
  R565.FiniteProjectiveFactorization
    Configuration Position
    (R529.wilsonObservable source)
asFiniteProjectiveFactorization source = record
  { R565.FiniteProjectiveFactorization.FiniteCoordinate =
      Position
  ; R565.FiniteProjectiveFactorization.ProjectedConfiguration =
      λ position →
        PathValues (R529.boundaryAt source position)
  ; R565.FiniteProjectiveFactorization.project =
      λ position configuration →
        projectPathValues
          (R529.decode source configuration)
          (R529.boundaryAt source position)
  ; R565.FiniteProjectiveFactorization.coordinateOf =
      λ position → position
  ; R565.FiniteProjectiveFactorization.finiteObservable =
      projectedWilsonValue source
  ; R565.FiniteProjectiveFactorization.factorsThroughFiniteProjection =
      wilsonObservableFactorsThroughPathValues source
  }

round568WilsonPathFactorizationCompilerLevel : ProofLevel
round568WilsonPathFactorizationCompilerLevel = machineChecked

round568PathLocalityCompilerLevel : ProofLevel
round568PathLocalityCompilerLevel =
  R529.round529PathLocalityCompilerLevel

-- No new physical theorem is introduced here.  The remaining A3 realization is
-- that these path-value projections are among the finite coordinates of the
-- selected projective continuum system.
literalRound568PathProjectionBelongsToSelectedProjectiveSystemLevel : ProofLevel
literalRound568PathProjectionBelongsToSelectedProjectiveSystemLevel = conditional
