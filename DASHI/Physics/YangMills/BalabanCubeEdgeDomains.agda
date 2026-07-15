module DASHI.Physics.YangMills.BalabanCubeEdgeDomains where

------------------------------------------------------------------------
-- CMP 109, p. 257: base localization domains and their finite tree-code
-- carrier.
--
-- A domain is represented extensionally by a duplicate-free finite list of
-- closed M-cubes, with wall-connectedness measured in the already checked
-- source-faithful face-cube graph.  This file intentionally stops before
-- asserting a geometric edge-containment relation: proving that relation
-- requires the next explicit closed-cube/grid-edge incidence development.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≢_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; [])
open import Data.Nat.Base using (NonZero)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import DASHI.Physics.YangMills.GraphCombinatorics using
  ( _∈_; _⊆_; NoDuplicates; Connected )
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using
  ( faceCubeGraph )
open import DASHI.Physics.YangMills.BalabanCubeEdgeIncidence using
  ( CubeGridVertex4; MCube4; incidentCubeCandidates; incidentCubes
  ; incidentCubesForVerticesComplete )
open import DASHI.Physics.YangMills.BalabanCubeEdgeTreeCodes using
  ( CubeGridEdgeCode; CubeEdgeTreeCode; CubeEdgeTreeValidity
  ; from; to; vertices; edges; endpointsPresent )

record LocalizationDomain (N : Nat) {{_ : NonZero N}} : Set where
  field
    cubes : List (MCube4 N)
    cubesNoDuplicates : NoDuplicates cubes
    cubesNonempty : cubes ≢ []
    wallConnected : Connected (faceCubeGraph {N}) cubes

open LocalizationDomain public

-- This is the source-facing pairing before geometric admissibility is
-- supplied.  Validity proves that a traversal stays on the code's exact
-- finite edge graph; the later `AdmissibleCubeEdgeTree` will additionally
-- certify closed-cube containment and that every domain cube is met.
record DomainTreePresentation {N : Nat} {{_ : NonZero N}}
  (X : LocalizationDomain N) : Set where
  field
    code : CubeEdgeTreeCode N
    valid : CubeEdgeTreeValidity code

open DomainTreePresentation public

------------------------------------------------------------------------
-- Discrete closed-cube incidence.
--
-- `VertexInClosedCube v C` is the cubical-complex relation: C is one of
-- the (at most sixteen) lower-corner cubes incident to v.  For a unit grid
-- edge, membership of both endpoints in C expresses that the whole closed
-- cell edge belongs to C.  The remaining source-geometry audit is to prove
-- this discrete presentation equivalent to the continuous "contained in
-- the union of closed M-cubes" wording in CMP 109; no such equivalence is
-- assumed silently here.

VertexInClosedCube : ∀ {N} {{_ : NonZero N}} →
  CubeGridVertex4 N → MCube4 N → Set
VertexInClosedCube vertex cube = cube ∈ incidentCubeCandidates vertex

GridEdgeInClosedCube : ∀ {N} {{_ : NonZero N}} →
  MCube4 N → CubeGridEdgeCode N → Set
GridEdgeInClosedCube cube edge =
  VertexInClosedCube (from edge) cube ×
  VertexInClosedCube (to edge) cube

GridEdgeContainedInDomain : ∀ {N} {{_ : NonZero N}} →
  LocalizationDomain N → CubeGridEdgeCode N → Set
GridEdgeContainedInDomain X edge =
  Σ (MCube4 _) λ cube →
    cube ∈ cubes X × GridEdgeInClosedCube cube edge

-- A cube can meet a unit grid edge only through an endpoint in the
-- discrete cubical presentation.  This is the exact endpoint witness that
-- later transports cube meeting across a spanning tree with the same
-- vertices.
CubeMeetsGridEdge : ∀ {N} {{_ : NonZero N}} →
  MCube4 N → CubeGridEdgeCode N → Set
CubeMeetsGridEdge cube edge =
  VertexInClosedCube (from edge) cube ⊎
  VertexInClosedCube (to edge) cube

cubeMeetsGridEdgeImpliesEndpoint : ∀ {N} {{_ : NonZero N}}
  {cube : MCube4 N} {edge : CubeGridEdgeCode N} →
  CubeMeetsGridEdge cube edge →
  VertexInClosedCube (from edge) cube ⊎
  VertexInClosedCube (to edge) cube
cubeMeetsGridEdgeImpliesEndpoint meeting = meeting

CubeMeetsTree : ∀ {N} {{_ : NonZero N}} →
  MCube4 N → CubeEdgeTreeCode N → Set
CubeMeetsTree cube T =
  Σ (CubeGridEdgeCode _) λ edge →
    edge ∈ edges T × CubeMeetsGridEdge cube edge

cubeMeetsTreeImpliesVertexWitness : ∀ {N} {{_ : NonZero N}}
  {cube : MCube4 N} {T : CubeEdgeTreeCode N} →
  CubeEdgeTreeValidity T → CubeMeetsTree cube T →
  Σ (CubeGridVertex4 N) λ vertex →
    vertex ∈ vertices T × VertexInClosedCube vertex cube
cubeMeetsTreeImpliesVertexWitness validity
  (edge , edge∈ , inj₁ from∈cube) =
  from edge , proj₁ (endpointsPresent validity edge∈) , from∈cube
cubeMeetsTreeImpliesVertexWitness validity
  (edge , edge∈ , inj₂ to∈cube) =
  to edge , proj₂ (endpointsPresent validity edge∈) , to∈cube

cubeMeetsTreeImpliesIncidentCube : ∀ {N} {{_ : NonZero N}}
  {cube : MCube4 N} {T : CubeEdgeTreeCode N} →
  CubeEdgeTreeValidity T → CubeMeetsTree cube T →
  cube ∈ incidentCubes (vertices T)
cubeMeetsTreeImpliesIncidentCube validity meeting =
  let witness = cubeMeetsTreeImpliesVertexWitness validity meeting
  in incidentCubesForVerticesComplete
       (proj₁ (proj₂ witness))
       (proj₂ (proj₂ witness))

record AdmissibleCubeEdgeTree {N : Nat} {{_ : NonZero N}}
  (X : LocalizationDomain N) (T : CubeEdgeTreeCode N) : Set where
  field
    valid : CubeEdgeTreeValidity T
    contained : ∀ {edge} → edge ∈ edges T →
      GridEdgeContainedInDomain X edge
    meetsEveryCube : ∀ {cube} → cube ∈ cubes X → CubeMeetsTree cube T

open AdmissibleCubeEdgeTree public

admissibleTreeMeetsCubeAtVertex : ∀ {N} {{_ : NonZero N}}
  {X : LocalizationDomain N} {T : CubeEdgeTreeCode N} →
  AdmissibleCubeEdgeTree X T →
  ∀ {cube} → cube ∈ cubes X →
  Σ (CubeGridVertex4 N) λ vertex →
    vertex ∈ vertices T × VertexInClosedCube vertex cube
admissibleTreeMeetsCubeAtVertex admissible cube∈ =
  cubeMeetsTreeImpliesVertexWitness
    (AdmissibleCubeEdgeTree.valid admissible)
    (AdmissibleCubeEdgeTree.meetsEveryCube admissible cube∈)

admissibleDomainContainedInIncidentCubes : ∀ {N} {{_ : NonZero N}}
  {X : LocalizationDomain N} {T : CubeEdgeTreeCode N} →
  AdmissibleCubeEdgeTree X T →
  cubes X ⊆ incidentCubes (vertices T)
admissibleDomainContainedInIncidentCubes admissible cube∈ =
  cubeMeetsTreeImpliesIncidentCube
    (AdmissibleCubeEdgeTree.valid admissible)
    (AdmissibleCubeEdgeTree.meetsEveryCube admissible cube∈)
