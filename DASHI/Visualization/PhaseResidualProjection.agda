module DASHI.Visualization.PhaseResidualProjection where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Semantic authority and renderer authority are deliberately separate.
-- An SVG can expose a theorem, a residual, or a useful conjectural shape;
-- it cannot promote an illustrative projection into a proof.

data Authority : Set where
  exact : Authority
  derived : Authority
  illustrative : Authority
  observed : Authority
  candidate : Authority

data ViewKind : Set where
  phase-plane : ViewKind
  residual-shadow : ViewKind
  helix : ViewKind
  axis-fan : ViewKind
  waveform : ViewKind
  mosaic : ViewKind
  spiral : ViewKind
  search-tree : ViewKind

data EvidenceFeature : Set where
  cyclic-phase : EvidenceFeature
  temporal-lift : EvidenceFeature
  high-dimensional : EvidenceFeature
  scalar-residual : EvidenceFeature
  coordinate-matrix : EvidenceFeature
  branching-search : EvidenceFeature
  recursive-growth : EvidenceFeature

viewBattery : EvidenceFeature → List ViewKind
viewBattery cyclic-phase = phase-plane ∷ residual-shadow ∷ waveform ∷ []
viewBattery temporal-lift = helix ∷ waveform ∷ []
viewBattery high-dimensional = axis-fan ∷ mosaic ∷ spiral ∷ []
viewBattery scalar-residual = waveform ∷ residual-shadow ∷ []
viewBattery coordinate-matrix = mosaic ∷ axis-fan ∷ []
viewBattery branching-search = search-tree ∷ mosaic ∷ []
viewBattery recursive-growth = spiral ∷ search-tree ∷ waveform ∷ []

------------------------------------------------------------------------
-- Minimal algebraic kernel for exact residual cancellation.

record PointedNegation (A : Set) : Set where
  constructor pointedNegation
  field
    zero : A
    add : A → A → A
    negate : A → A
    rightInverse : (x : A) → add x (negate x) ≡ zero

open PointedNegation public

residual :
  ∀ {A : Set} →
  PointedNegation A →
  A →
  A →
  A
residual structure anchor phase =
  add structure anchor (negate structure phase)

residualAtClosure :
  ∀ {A : Set} →
  (structure : PointedNegation A) →
  (anchor phase : A) →
  phase ≡ anchor →
  residual structure anchor phase ≡ zero structure
residualAtClosure structure anchor phase refl =
  rightInverse structure anchor

record ZeroPreservingProjection
  {A : Set}
  (structure : PointedNegation A)
  (Screen : Set) : Set where
  constructor zeroPreservingProjection
  field
    screenZero : Screen
    project : A → Screen
    projectZero : project (zero structure) ≡ screenZero

open ZeroPreservingProjection public

projectedResidualAtClosure :
  ∀ {A Screen : Set} →
  (structure : PointedNegation A) →
  (projection : ZeroPreservingProjection structure Screen) →
  (anchor phase : A) →
  phase ≡ anchor →
  project projection (residual structure anchor phase)
    ≡ screenZero projection
projectedResidualAtClosure structure projection anchor phase closes
  rewrite residualAtClosure structure anchor phase closes =
  projectZero projection

------------------------------------------------------------------------
-- The introspective loop is represented as typed stages.  In particular,
-- image analysis yields observations and candidate models; the return edge to
-- theory is an explicit proof-discharge step rather than an automatic upgrade.

data PipelineStage : Set where
  agda-source : PipelineStage
  visual-ir : PipelineStage
  svg-artifact : PipelineStage
  image-observation : PipelineStage
  reconstructed-candidate : PipelineStage

data PipelineStep : PipelineStage → PipelineStage → Set where
  extract-source : PipelineStep agda-source visual-ir
  render-view : PipelineStep visual-ir svg-artifact
  analyse-image : PipelineStep svg-artifact image-observation
  reconstruct-model : PipelineStep image-observation reconstructed-candidate
  discharge-candidate : PipelineStep reconstructed-candidate agda-source

stepAuthority :
  ∀ {from to : PipelineStage} →
  PipelineStep from to →
  Authority
stepAuthority extract-source = derived
stepAuthority render-view = illustrative
stepAuthority analyse-image = observed
stepAuthority reconstruct-model = candidate
stepAuthority discharge-candidate = derived

------------------------------------------------------------------------
-- Source-readable scene descriptors.  The materialiser parses only these
-- declarations and derives all sample coordinates, projection matrices, paths,
-- and SVG animation data downstream.

record SceneDescriptor : Set where
  constructor sceneDescriptor
  field
    title : String
    dimension : Nat
    samples : Nat
    views : List ViewKind
    semanticAuthority : Authority
    renderingAuthority : Authority

open SceneDescriptor public

eulerComplex2D : SceneDescriptor
eulerComplex2D = sceneDescriptor "Euler phase cancellation in the complex plane" 2 97 (phase-plane ∷ residual-shadow ∷ waveform ∷ []) exact illustrative

eulerHelix3D : SceneDescriptor
eulerHelix3D = sceneDescriptor "Complex phase lifted along time" 3 145 (phase-plane ∷ helix ∷ waveform ∷ []) derived illustrative

eulerAmbient4D : SceneDescriptor
eulerAmbient4D = sceneDescriptor "Complex phase plane embedded in four real coordinates" 4 97 (phase-plane ∷ axis-fan ∷ residual-shadow ∷ mosaic ∷ []) derived illustrative

eulerAmbient5D : SceneDescriptor
eulerAmbient5D = sceneDescriptor "Complex phase plane embedded in five real coordinates" 5 97 (phase-plane ∷ axis-fan ∷ spiral ∷ residual-shadow ∷ []) derived illustrative

eulerAmbient12D : SceneDescriptor
eulerAmbient12D = sceneDescriptor "Complex phase plane embedded in twelve real coordinates" 12 145 (axis-fan ∷ mosaic ∷ waveform ∷ spiral ∷ []) derived illustrative

eulerAmbient32D : SceneDescriptor
eulerAmbient32D = sceneDescriptor "Complex phase plane embedded in thirty-two real coordinates" 32 193 (axis-fan ∷ mosaic ∷ waveform ∷ spiral ∷ []) derived illustrative

record ClaimBoundary : Set where
  constructor claimBoundary
  field
    exactClaim : String
    projectionClaim : String
    observationClaim : String

open ClaimBoundary public

eulerClaimBoundary : ClaimBoundary
eulerClaimBoundary =
  claimBoundary
    "If the phase returns to its anchor, the residual is exactly zero."
    "The two-dimensional screen map changes appearance but preserves zero."
    "Patterns recovered from pixels remain observations until reconstructed and proved."
