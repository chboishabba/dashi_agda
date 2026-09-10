module DASHI.Combinatorics.GraphColouringHomomorphismCoreExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- MINIMAL GRAPH-COLOURING CORE
--
-- A proper colouring is not a second primitive notion: it is a graph
-- homomorphism into a palette graph.  This keeps recolouring, restriction,
-- tensor-product lift, and later pants/gluing specialisations on one transport
-- law instead of duplicating colouring-specific machinery.
------------------------------------------------------------------------

record RelGraph : Set₁ where
  constructor relGraph
  field
    Vertex : Set
    Adj : Vertex → Vertex → Set

open RelGraph public

record GraphHom (G H : RelGraph) : Set₁ where
  constructor graphHom
  field
    onVertex : Vertex G → Vertex H
    preservesAdj :
      {u v : Vertex G} →
      Adj G u v →
      Adj H (onVertex u) (onVertex v)

open GraphHom public

identityHom : (G : RelGraph) → GraphHom G G
identityHom G = graphHom (λ v → v) (λ edge → edge)

composeHom :
  {G H K : RelGraph} →
  GraphHom G H →
  GraphHom H K →
  GraphHom G K
composeHom f g =
  graphHom
    (λ v → onVertex g (onVertex f v))
    (λ edge → preservesAdj g (preservesAdj f edge))

------------------------------------------------------------------------
-- Palette graphs and colourings.
--
-- `Different` is supplied by the instance.  For an ordinary complete palette
-- graph it is inequality; keeping it abstract avoids importing decidable
-- equality or a second graph library into the core.
------------------------------------------------------------------------

paletteGraph :
  (Colour : Set) →
  (Different : Colour → Colour → Set) →
  RelGraph
paletteGraph Colour Different = relGraph Colour Different

Colouring : RelGraph → RelGraph → Set₁
Colouring G Palette = GraphHom G Palette

ProperColouring :
  (G : RelGraph) →
  (Colour : Set) →
  (Different : Colour → Colour → Set) →
  Set₁
ProperColouring G Colour Different =
  Colouring G (paletteGraph Colour Different)

------------------------------------------------------------------------
-- Recolouring = an endomorphism of the valid-colouring space.
--
-- The codomain type already enforces preservation of properness.  Locality,
-- Kempe support, minimality, and algorithmic choice are extra predicates on an
-- instance, not duplicated in the generic carrier.
------------------------------------------------------------------------

Recolour : RelGraph → RelGraph → Set₁
Recolour G Palette = Colouring G Palette → Colouring G Palette

identityRecolour : {G Palette : RelGraph} → Recolour G Palette
identityRecolour c = c

------------------------------------------------------------------------
-- Colourings pull back contravariantly along graph homomorphisms.
------------------------------------------------------------------------

pullbackColouring :
  {G H Palette : RelGraph} →
  GraphHom G H →
  Colouring H Palette →
  Colouring G Palette
pullbackColouring f colouring = composeHom f colouring

------------------------------------------------------------------------
-- Tensor product and its two canonical projections.
--
-- This is the source-paid easy half of Hedetniemi's setting: any colouring of
-- either factor pulls back to the tensor product.  No equality of chromatic
-- numbers is asserted here.
------------------------------------------------------------------------

tensorGraph : RelGraph → RelGraph → RelGraph
tensorGraph G H =
  relGraph
    (Vertex G × Vertex H)
    (λ x y →
      Adj G (proj₁ x) (proj₁ y)
      × Adj H (proj₂ x) (proj₂ y))

tensorProjLeft : (G H : RelGraph) → GraphHom (tensorGraph G H) G
tensorProjLeft G H =
  graphHom proj₁ (λ edge → proj₁ edge)

tensorProjRight : (G H : RelGraph) → GraphHom (tensorGraph G H) H
tensorProjRight G H =
  graphHom proj₂ (λ edge → proj₂ edge)

leftTensorColouring :
  {G H Palette : RelGraph} →
  Colouring G Palette →
  Colouring (tensorGraph G H) Palette
leftTensorColouring {G} {H} colouring =
  pullbackColouring (tensorProjLeft G H) colouring

rightTensorColouring :
  {G H Palette : RelGraph} →
  Colouring H Palette →
  Colouring (tensorGraph G H) Palette
rightTensorColouring {G} {H} colouring =
  pullbackColouring (tensorProjRight G H) colouring

------------------------------------------------------------------------
-- Exact boundary: this core deliberately stops before chromatic minimisation,
-- Kempe connectivity, planarity, reducibility, or any identification of the
-- 369 ternary carrier with a graph adjacency structure.
------------------------------------------------------------------------

record GraphColouringHomomorphismCoreBoundary : Set where
  constructor graphColouringHomomorphismCoreBoundary
  field
    colouringIsHomomorphismToPaletteGraph : Bool
    recolouringIsEndomorphismOfColouringSpace : Bool
    colouringsPullBackAlongGraphHomomorphisms : Bool
    tensorFactorColouringsLiftByProjection : Bool
    hedetniemiEqualityDerived : Bool
    fourColourTheoremDerived : Bool
    pantsAdjacencyInvented : Bool

canonicalGraphColouringHomomorphismCoreBoundary :
  GraphColouringHomomorphismCoreBoundary
canonicalGraphColouringHomomorphismCoreBoundary =
  graphColouringHomomorphismCoreBoundary
    true
    true
    true
    true
    false
    false
    false
