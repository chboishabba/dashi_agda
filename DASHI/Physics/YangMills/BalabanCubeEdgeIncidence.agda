module DASHI.Physics.YangMills.BalabanCubeEdgeIncidence where

------------------------------------------------------------------------
-- CMP 109 (1987), p. 257, base localization-domain geometry.
--
-- After the source rescaling, M-cubes are unit closed cubes.  A grid
-- vertex is incident to two choices of lower cube coordinate on each of
-- four axes, hence to at most 2^4 = 16 closed cubes.  This module proves
-- that finite arithmetic fact on the same periodic four-coordinate carrier
-- used by the source-faithful P06 face-cube graph.
--
-- The list below is deliberately raw: small periodic tori can identify
-- several incident closed cubes.  Its exact length is 16, which is the
-- uniform upper bound needed for the later incidence-fibre argument.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Nat.Base using (_≤_; NonZero)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Nat.Properties using (*-comm; *-mono-≤; ≤-refl; ≤-trans)

open import DASHI.Physics.YangMills.GraphCombinatorics using
  ( mapList; Graph; NoDuplicates; _∈_; here; there; canonicalize; canonicalizeSound
  ; canonicalizeComplete; canonicalizeNoDup; noDupSubsetLength≤ )
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry
  using ( Cube4; cube4; previousCoordinate; faceCubeGraph
        ; x₀; x₁; x₂; x₃ )

-- We use separate names to make the geometric roles clear.  Both are the
-- periodic coordinate carrier (Fin N)^4; an M-cube is represented by its
-- lower grid corner.
CubeGridVertex4 : Nat → Set
CubeGridVertex4 = Cube4

MCube4 : Nat → Set
MCube4 = Cube4

data VertexCubeCorner : Set where
  c0000 c0001 c0010 c0011 : VertexCubeCorner
  c0100 c0101 c0110 c0111 : VertexCubeCorner
  c1000 c1001 c1010 c1011 : VertexCubeCorner
  c1100 c1101 c1110 c1111 : VertexCubeCorner

allVertexCubeCorners : List VertexCubeCorner
allVertexCubeCorners =
  c0000 ∷ c0001 ∷ c0010 ∷ c0011 ∷
  c0100 ∷ c0101 ∷ c0110 ∷ c0111 ∷
  c1000 ∷ c1001 ∷ c1010 ∷ c1011 ∷
  c1100 ∷ c1101 ∷ c1110 ∷ c1111 ∷ []

allVertexCubeCornersLength : length allVertexCubeCorners ≡ 16
allVertexCubeCornersLength = refl

cornerCube : ∀ {N} {{_ : NonZero N}} → CubeGridVertex4 N → VertexCubeCorner → MCube4 N
cornerCube (cube4 a₀ a₁ a₂ a₃) c0000 = cube4 a₀ a₁ a₂ a₃
cornerCube (cube4 a₀ a₁ a₂ a₃) c0001 = cube4 a₀ a₁ a₂ (previousCoordinate a₃)
cornerCube (cube4 a₀ a₁ a₂ a₃) c0010 = cube4 a₀ a₁ (previousCoordinate a₂) a₃
cornerCube (cube4 a₀ a₁ a₂ a₃) c0011 = cube4 a₀ a₁ (previousCoordinate a₂) (previousCoordinate a₃)
cornerCube (cube4 a₀ a₁ a₂ a₃) c0100 = cube4 a₀ (previousCoordinate a₁) a₂ a₃
cornerCube (cube4 a₀ a₁ a₂ a₃) c0101 = cube4 a₀ (previousCoordinate a₁) a₂ (previousCoordinate a₃)
cornerCube (cube4 a₀ a₁ a₂ a₃) c0110 = cube4 a₀ (previousCoordinate a₁) (previousCoordinate a₂) a₃
cornerCube (cube4 a₀ a₁ a₂ a₃) c0111 = cube4 a₀ (previousCoordinate a₁) (previousCoordinate a₂) (previousCoordinate a₃)
cornerCube (cube4 a₀ a₁ a₂ a₃) c1000 = cube4 (previousCoordinate a₀) a₁ a₂ a₃
cornerCube (cube4 a₀ a₁ a₂ a₃) c1001 = cube4 (previousCoordinate a₀) a₁ a₂ (previousCoordinate a₃)
cornerCube (cube4 a₀ a₁ a₂ a₃) c1010 = cube4 (previousCoordinate a₀) a₁ (previousCoordinate a₂) a₃
cornerCube (cube4 a₀ a₁ a₂ a₃) c1011 = cube4 (previousCoordinate a₀) a₁ (previousCoordinate a₂) (previousCoordinate a₃)
cornerCube (cube4 a₀ a₁ a₂ a₃) c1100 = cube4 (previousCoordinate a₀) (previousCoordinate a₁) a₂ a₃
cornerCube (cube4 a₀ a₁ a₂ a₃) c1101 = cube4 (previousCoordinate a₀) (previousCoordinate a₁) a₂ (previousCoordinate a₃)
cornerCube (cube4 a₀ a₁ a₂ a₃) c1110 = cube4 (previousCoordinate a₀) (previousCoordinate a₁) (previousCoordinate a₂) a₃
cornerCube (cube4 a₀ a₁ a₂ a₃) c1111 = cube4 (previousCoordinate a₀) (previousCoordinate a₁) (previousCoordinate a₂) (previousCoordinate a₃)

incidentCubeCandidates : ∀ {N} {{_ : NonZero N}} → CubeGridVertex4 N → List (MCube4 N)
incidentCubeCandidates vertex = mapList (cornerCube vertex) allVertexCubeCorners

listMapLength : ∀ {A B : Set} (f : A → B) (xs : List A) →
  length (mapList f xs) ≡ length xs
listMapLength f [] = refl
listMapLength f (x ∷ xs) = cong suc (listMapLength f xs)

incidentCubeCandidatesLength : ∀ {N} {{_ : NonZero N}} (vertex : CubeGridVertex4 N) →
  length (incidentCubeCandidates vertex) ≡ 16
incidentCubeCandidatesLength vertex =
  trans (listMapLength (cornerCube vertex) allVertexCubeCorners)
    allVertexCubeCornersLength

-- A raw finite incidence neighbourhood for a finite collection of grid
-- vertices.  Deduplication can only reduce this list; retaining duplicates
-- keeps the cardinality proof elementary and uniform in N.
incidentCubeCandidatesForVertices : ∀ {N} {{_ : NonZero N}} →
  List (CubeGridVertex4 N) → List (MCube4 N)
incidentCubeCandidatesForVertices [] = []
incidentCubeCandidatesForVertices (vertex ∷ vertices) =
  incidentCubeCandidates vertex ++ incidentCubeCandidatesForVertices vertices

in-++-left : ∀ {A : Set} {x : A} {xs ys : List A} →
  x ∈ xs → x ∈ (xs ++ ys)
in-++-left here = here
in-++-left (there x∈) = there (in-++-left x∈)

in-++-right : ∀ {A : Set} {x : A} (xs : List A) {ys : List A} →
  x ∈ ys → x ∈ (xs ++ ys)
in-++-right [] x∈ = x∈
in-++-right (x ∷ xs) x∈ = there (in-++-right xs x∈)

incidentCubeCandidatesForVerticesComplete : ∀ {N} {{_ : NonZero N}}
  {vertices : List (CubeGridVertex4 N)}
  {vertex : CubeGridVertex4 N} {cube : MCube4 N} →
  vertex ∈ vertices → cube ∈ incidentCubeCandidates vertex →
  cube ∈ incidentCubeCandidatesForVertices vertices
incidentCubeCandidatesForVerticesComplete {vertices = []} () cube∈vertex
incidentCubeCandidatesForVerticesComplete {vertices = vertex ∷ vertices}
  here cube∈vertex =
  in-++-left cube∈vertex
incidentCubeCandidatesForVerticesComplete {vertices = vertex ∷ vertices}
  (there vertex∈vertices) cube∈vertex =
  in-++-right (incidentCubeCandidates vertex)
    (incidentCubeCandidatesForVerticesComplete vertex∈vertices cube∈vertex)

-- The fibre mask must be indexed by a genuine finite set of cubes, not by
-- the raw 16-per-vertex presentation.  Canonicalisation removes both
-- repeated vertex incidences and small-torus identifications while retaining
-- exactly the same members.
incidentCubes : ∀ {N} {{_ : NonZero N}} →
  List (CubeGridVertex4 N) → List (MCube4 N)
incidentCubes {N} vertices =
  canonicalize {G = faceCubeGraph {N}}
    (incidentCubeCandidatesForVertices vertices)

incidentCubesSound : ∀ {N} {{_ : NonZero N}} {vertices : List (CubeGridVertex4 N)}
  {cube : MCube4 N} →
  cube ∈ incidentCubes vertices →
  cube ∈ incidentCubeCandidatesForVertices vertices
incidentCubesSound {N} =
  canonicalizeSound {G = faceCubeGraph {N}}

incidentCubesComplete : ∀ {N} {{_ : NonZero N}} {vertices : List (CubeGridVertex4 N)}
  {cube : MCube4 N} →
  cube ∈ incidentCubeCandidatesForVertices vertices →
  cube ∈ incidentCubes vertices
incidentCubesComplete {N} =
  canonicalizeComplete {G = faceCubeGraph {N}}

incidentCubesForVerticesComplete : ∀ {N} {{_ : NonZero N}}
  {vertices : List (CubeGridVertex4 N)}
  {vertex : CubeGridVertex4 N} {cube : MCube4 N} →
  vertex ∈ vertices → cube ∈ incidentCubeCandidates vertex →
  cube ∈ incidentCubes vertices
incidentCubesForVerticesComplete {vertices = vertices} {cube = cube}
  vertex∈vertices cube∈vertex =
  incidentCubesComplete {vertices = vertices} {cube = cube}
    (incidentCubeCandidatesForVerticesComplete vertex∈vertices cube∈vertex)

incidentCubesNoDuplicates : ∀ {N} {{_ : NonZero N}}
  (vertices : List (CubeGridVertex4 N)) →
  NoDuplicates (incidentCubes vertices)
incidentCubesNoDuplicates {N} vertices =
  canonicalizeNoDup {G = faceCubeGraph {N}}
    (incidentCubeCandidatesForVertices vertices)

length-++ : ∀ {A : Set} (xs ys : List A) →
  length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

incidentCubeCandidatesForVerticesLength : ∀ {N} {{_ : NonZero N}}
  (vertices : List (CubeGridVertex4 N)) →
  length (incidentCubeCandidatesForVertices vertices) ≡ length vertices * 16
incidentCubeCandidatesForVerticesLength [] = refl
incidentCubeCandidatesForVerticesLength (vertex ∷ vertices) =
  trans
    (length-++ (incidentCubeCandidates vertex)
      (incidentCubeCandidatesForVertices vertices))
    (trans
      (cong (λ q → q + length (incidentCubeCandidatesForVertices vertices))
        (incidentCubeCandidatesLength vertex))
      (cong (λ q → 16 + q)
        (incidentCubeCandidatesForVerticesLength vertices)))

incidentCubeCandidatesForVerticesLength≤16Times : ∀ {N} {{_ : NonZero N}}
  (vertices : List (CubeGridVertex4 N)) →
  length (incidentCubeCandidatesForVertices vertices) ≤ 16 * length vertices
incidentCubeCandidatesForVerticesLength≤16Times vertices =
  subst (λ q → q ≤ 16 * length vertices)
    (sym
      (trans
        (incidentCubeCandidatesForVerticesLength vertices)
        (*-comm (length vertices) 16)))
    ≤-refl
  where
  -- The equality above is stated as |V| * 16 because multiplication unfolds
  -- directly on the list length.  The source-facing form is 16 * |V|.
  -- Rewriting by commutativity is kept local to avoid a second list proof.
  subst : ∀ {A : Set} {x y : A} → (P : A → Set) → x ≡ y → P x → P y
  subst P refl px = px

incidentCubesLength≤Raw : ∀ {N} {{_ : NonZero N}}
  (vertices : List (CubeGridVertex4 N)) →
  length (incidentCubes vertices)
    ≤ length (incidentCubeCandidatesForVertices vertices)
incidentCubesLength≤Raw {N} vertices =
  noDupSubsetLength≤
    (incidentCubesNoDuplicates {N} vertices)
    (incidentCubesSound {N} {vertices = vertices})

incidentCubesLength≤16Times : ∀ {N} {{_ : NonZero N}}
  (vertices : List (CubeGridVertex4 N)) →
  length (incidentCubes vertices) ≤ 16 * length vertices
incidentCubesLength≤16Times vertices =
  ≤-trans
    (incidentCubesLength≤Raw vertices)
    (incidentCubeCandidatesForVerticesLength≤16Times vertices)

------------------------------------------------------------------------
-- Tree-facing form of the incidence estimate.
--
-- CMP 109's cube-edge minimizer has |V(T)| = |E(T)| + 1.  The actual
-- tree-code construction and its proof of that equality belong in the
-- next module; this lemma is the concrete incidence transport it needs.
-- It is intentionally stated from the weaker inequality, so it also
-- applies to any finite tree presentation whose vertex list has already
-- been deduplicated.

incidentCubeCandidatesForTreeVerticesLength≤ : ∀ {N} {{_ : NonZero N}}
  (vertices : List (CubeGridVertex4 N))
  (edgeCount : Nat) →
  length vertices ≤ edgeCount + 1 →
  length (incidentCubeCandidatesForVertices vertices)
    ≤ 16 * (edgeCount + 1)
incidentCubeCandidatesForTreeVerticesLength≤ vertices edgeCount vertices≤ =
  ≤-trans
    (incidentCubeCandidatesForVerticesLength≤16Times vertices)
    (*-mono-≤ (≤-refl {16}) vertices≤)

incidentCubesForTreeVerticesLength≤ : ∀ {N} {{_ : NonZero N}}
  (vertices : List (CubeGridVertex4 N))
  (edgeCount : Nat) →
  length vertices ≤ edgeCount + 1 →
  length (incidentCubes vertices)
    ≤ 16 * (edgeCount + 1)
incidentCubesForTreeVerticesLength≤ vertices edgeCount vertices≤ =
  ≤-trans
    (incidentCubesLength≤16Times vertices)
    (*-mono-≤ (≤-refl {16}) vertices≤)
