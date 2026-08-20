module DASHI.Governance.PopulistPlutocraticDualProjection where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Vertical distinction / horizontal identification as independent fibres.
--
-- Reference / motivation:
-- Jo Littler, "Normcore plutocrats in gold elevators: reading the Trump Tower
-- photographs", Cultural Politics 15(1), 2019, pp. 15-28.
-- DOI: 10.1215/17432197-7289458
--
-- Littler motivates the coexistence of spectacular plutocratic distinction
-- and claims to ordinariness/popular identification.  The constructions below
-- are DASHI's generic formalisation, not theorems attributed to Littler.
------------------------------------------------------------------------

record DualPublicProjection : Set₁ where
  field
    Actor : Set
    Vertical : Set
    Horizontal : Set
    MaterialPosition : Set
    verticalProjection : Actor → Vertical
    horizontalProjection : Actor → Horizontal
    materialPosition : Actor → MaterialPosition

open DualPublicProjection public

record SimultaneouslyHigh
    (D : DualPublicProjection) : Set₁ where
  field
    actor : Actor D
    HighVertical : Vertical D → Set
    HighHorizontal : Horizontal D → Set
    verticalHigh : HighVertical (verticalProjection D actor)
    horizontalHigh : HighHorizontal (horizontalProjection D actor)

open SimultaneouslyHigh public

------------------------------------------------------------------------
-- Shared taste / horizontal representation does not establish shared material
-- position.  Nor does vertical distinction by itself establish authority.
------------------------------------------------------------------------

record HorizontalMaterialDifference
    (D : DualPublicProjection)
    (left right : Actor D) : Set₁ where
  field
    SameHorizontal : Horizontal D → Horizontal D → Set
    sameHorizontal :
      SameHorizontal
        (horizontalProjection D left)
        (horizontalProjection D right)
    MaterialDifferent : MaterialPosition D → MaterialPosition D → Set
    materialDifferent :
      MaterialDifferent
        (materialPosition D left)
        (materialPosition D right)

open HorizontalMaterialDifference public

data HorizontalSimilarityAutomaticallyEqualisesMaterialPosition
    {D : DualPublicProjection}
    {left right : Actor D}
    (w : HorizontalMaterialDifference D left right) : Set where

horizontalSimilarityDoesNotEqualiseMaterialPosition :
  ∀ {D left right} {w : HorizontalMaterialDifference D left right} →
  HorizontalSimilarityAutomaticallyEqualisesMaterialPosition w → ⊥
horizontalSimilarityDoesNotEqualiseMaterialPosition ()

------------------------------------------------------------------------
-- Representation is a carrier on which later provenance/policy operators may
-- act.  It is not itself a fascisticity certificate.
------------------------------------------------------------------------

data DualProjectionAutomaticallyCertifiesFascism
    (D : DualPublicProjection) : Set where

dualProjectionDoesNotAutomaticallyCertifyFascism :
  ∀ {D} → DualProjectionAutomaticallyCertifiesFascism D → ⊥
dualProjectionDoesNotAutomaticallyCertifyFascism ()

------------------------------------------------------------------------
-- A visible role performance is kept distinct from occupying the corresponding
-- material relation.
------------------------------------------------------------------------

record RolePerformanceSystem : Set₁ where
  field
    Actor : Set
    Role : Set
    performs : Actor → Role → Set
    occupies : Actor → Role → Set

open RolePerformanceSystem public

data PerformanceAutomaticallyImpliesOccupation
    (R : RolePerformanceSystem)
    {actor : Actor R}
    {role : Role R}
    (p : performs R actor role) : Set where

performanceDoesNotAutomaticallyImplyOccupation :
  ∀ {R actor role} {p : performs R actor role} →
  PerformanceAutomaticallyImpliesOccupation R p → ⊥
performanceDoesNotAutomaticallyImplyOccupation ()
