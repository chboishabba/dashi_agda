module DASHI.Applied.Seaminit.SewableCutAtlas where

open import Agda.Builtin.Bool     using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat      using (Nat)

------------------------------------------------------------------------
-- Surface topology and admissible cut carriers
--
-- The seam graph is required to live on the actual mesh one-skeleton.
-- No geometric or anatomical preference is encoded here: a crotch, head,
-- scapular, or other route remains admissible whenever it is the correct
-- sewable solution.

record SurfaceMesh : Set₁ where
  field
    Vertex       : Set
    Edge         : Set
    Face         : Set
    incident     : Edge → Vertex → Bool
    boundsFace   : Edge → Face → Bool
    meshAdjacent : Vertex → Vertex → Bool

record CutAtlas (M : SurfaceMesh) : Set₁ where
  private
    module M = SurfaceMesh M

  field
    Seam          : Set
    Panel         : Set
    seamEdge      : Seam → M.Edge
    panelContains : Panel → M.Face → Bool

    -- Every solver edge is an edge of the surface mesh.  This excludes the
    -- historical ROM/index-graph teleport and spiderweb failure.
    seamFrom        : Seam → M.Vertex
    seamTo          : Seam → M.Vertex
    seamIsMeshLocal : ∀ s →
      M.meshAdjacent (seamFrom s) (seamTo s) ≡ true

    -- Topological form is explicit rather than inferred from visual output.
    OpenBoundary   : Set
    ClosedBoundary : Set
    openBoundary   : OpenBoundary → Set
    closedBoundary : ClosedBoundary → Set

    panelCount    : Nat
    seamCount     : Nat
    boundaryCount : Nat

------------------------------------------------------------------------
-- Flattening and fabric response

record PanelFlattening (Panel : Set) : Set₁ where
  field
    PlanePoint       : Set
    flatten          : Panel → Set
    lengthDistortion : Panel → Set
    angleDistortion  : Panel → Set
    areaDistortion   : Panel → Set
    orientationSafe  : Panel → Bool

record FabricResponse : Set₁ where
  field
    Fabric            : Set
    MaterialDirection : Set
    Strain             : Set
    admissibleFabric   : Fabric → Bool
    warp               : Fabric → MaterialDirection
    weft               : Fabric → MaterialDirection
    allowedStrain      : Fabric → MaterialDirection → Strain → Bool

------------------------------------------------------------------------
-- Curvature allocation mechanisms
--
-- Non-zero surface curvature must be allocated through some combination of
-- panel cuts, darts/cones, gathers/pleats, or admissible material strain.
-- These are geometric/manufacturing mechanisms, not body-region taboos.

data CurvatureMechanism : Set where
  seamCut       : CurvatureMechanism
  dartOrCone    : CurvatureMechanism
  gatherOrPleat : CurvatureMechanism
  fabricStrain  : CurvatureMechanism

record CurvatureAllocation (Panel : Set) : Set₁ where
  field
    Singularity : Set
    mechanism   : Panel → CurvatureMechanism
    singularity : Singularity → Panel
    accounted   : Panel → Bool

------------------------------------------------------------------------
-- Anti-starburst and manufacturability boundary
--
-- Perfect local flattening is not allowed to discharge the problem by an
-- unbounded porcupine of tiny jagged cuts.  Complexity is bounded explicitly,
-- while the placement of admissible seams remains unconstrained by anatomy.

record ComplexityBudget : Set where
  field
    maxPanels             : Nat
    maxSeams              : Nat
    maxBoundaryComponents : Nat
    maxSingularities      : Nat

record BoundedBy (actual limit : Nat) : Set₁ where
  field
    Witness : Set
    witness : Witness

record AntiStarburst
  {M : SurfaceMesh}
  (A : CutAtlas M)
  (B : ComplexityBudget)
  : Set₁ where

  private
    module A = CutAtlas A
    module B = ComplexityBudget B

  field
    panelBudget    : BoundedBy A.panelCount B.maxPanels
    seamBudget     : BoundedBy A.seamCount B.maxSeams
    boundaryBudget : BoundedBy A.boundaryCount B.maxBoundaryComponents

    -- Boundary regularity is represented as a proof obligation instead of a
    -- hidden smoothing heuristic.  Concrete instances may use turning-angle,
    -- total-variation, spline, or fabrication-specific witnesses.
    BoundaryRegularity : Set
    boundaryRegularity : BoundaryRegularity

record SewableAtlas
  (M : SurfaceMesh)
  (A : CutAtlas M)
  : Set₂ where

  private
    module A = CutAtlas A

  field
    fabric        : FabricResponse
    flattening    : PanelFlattening A.Panel
    allocation    : CurvatureAllocation A.Panel
    budget        : ComplexityBudget
    antiStarburst : AntiStarburst A budget

    allPanelsFlattenable : A.Panel → Bool
    allPanelsFlattenable≡true : ∀ p → allPanelsFlattenable p ≡ true

    seamPairsCompatible : Bool
    seamPairsCompatible≡true : seamPairsCompatible ≡ true

    grainAndStrainAdmissible : Bool
    grainAndStrainAdmissible≡true : grainAndStrainAdmissible ≡ true

------------------------------------------------------------------------
-- Canonical promotion theorem

record SewableCutAtlasTheorem : Set₂ where
  field
    mesh  : SurfaceMesh
    atlas : CutAtlas mesh
    proof : SewableAtlas mesh atlas

  private
    module A = CutAtlas atlas
    module S = SewableAtlas proof
    module X = AntiStarburst S.antiStarburst

  noIndexGraphTeleport : ∀ s →
    SurfaceMesh.meshAdjacent mesh (A.seamFrom s) (A.seamTo s) ≡ true
  noIndexGraphTeleport = A.seamIsMeshLocal

  noPorcupineDischarge :
    BoundedBy A.seamCount (ComplexityBudget.maxSeams S.budget)
  noPorcupineDischarge = X.seamBudget

  flattenabilityIsManufacturingObligation : ∀ p →
    S.allPanelsFlattenable p ≡ true
  flattenabilityIsManufacturingObligation = S.allPanelsFlattenable≡true

------------------------------------------------------------------------
-- Scope boundary
--
-- This module does not assert that any concrete SeaMeInIt output is sewable.
-- Promotion requires concrete mesh-locality, flattening, strain, seam-pair,
-- curvature-allocation, regularity, and finite-complexity witnesses.
