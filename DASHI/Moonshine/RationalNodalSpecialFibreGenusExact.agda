module DASHI.Moonshine.RationalNodalSpecialFibreGenusExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / GEOMETRIC CONTEXT
--
-- Stephanie Treneer,
-- "Weierstrass points on X_0^+(p) and supersingular j-invariants",
-- Research in the Mathematical Sciences 4 (2017), article 25.
-- DOI: 10.1186/s40687-017-0115-z.
--
-- Treneer recalls the Deligne--Rapoport/Ogg reduction picture: modulo p,
-- X_0(p) consists of two copies of X_0(1) meeting at the supersingular points.
-- The Atkin--Lehner involution exchanges the components, fixes the supersingular
-- points with j in F_p, and exchanges Frobenius-conjugate quadratic pairs.
-- The quotient X_0^+(p) therefore has one rational component; each quadratic
-- supersingular pair becomes one self-intersection node.
--
-- DASHI CONTRIBUTION
--
-- Isolate the finite dual-graph calculation needed by that geometric picture.
-- For a connected nodal curve with one genus-zero component and d self-nodes,
-- the dual graph has
--
--   V = 1, E = d,
--
-- and the graph Euler relation E + 1 = V + b1 forces b1=d.  Combining this
-- with the standard nodal-curve genus formula
--
--   arithmetic genus = sum(component genera) + b1(dual graph)
--
-- gives arithmetic genus = d.
--
-- This file does NOT assert that an arbitrary modular curve has this special
-- fibre.  That domain-specific geometric realization is a separate witness.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import Data.Nat.Properties as Nat

record NodalDualGraphGenusData : Set where
  field
    nodeCount : Nat
    vertexCount : Nat
    edgeCount : Nat
    cycleRank : Nat
    componentGenusSum : Nat
    arithmeticGenus : Nat

    oneComponent : vertexCount ≡ 1
    oneEdgePerNode : edgeCount ≡ nodeCount

    -- Connected graph Euler relation: E + 1 = V + b1.
    graphEuler : edgeCount + 1 ≡ vertexCount + cycleRank

    rationalComponents : componentGenusSum ≡ 0

    nodalGenusFormula :
      arithmeticGenus ≡ componentGenusSum + cycleRank

open NodalDualGraphGenusData public

cycleRankEqualsNodeCount :
  (D : NodalDualGraphGenusData) →
  cycleRank D ≡ nodeCount D
cycleRankEqualsNodeCount D =
  sym
    (Nat.+-cancelˡ-≡ 1 (nodeCount D) (cycleRank D) normalized)
  where
  normalized : 1 + nodeCount D ≡ 1 + cycleRank D
  normalized =
    trans
      (Nat.+-comm 1 (nodeCount D))
      (trans
        (sym (oneEdgePerNode D))
        (trans
          (graphEuler D)
          (cong (_+ cycleRank D) (oneComponent D))))

arithmeticGenusEqualsNodeCount :
  (D : NodalDualGraphGenusData) →
  arithmeticGenus D ≡ nodeCount D
arithmeticGenusEqualsNodeCount D =
  trans
    (nodalGenusFormula D)
    (trans
      (cong (_+ cycleRank D) (rationalComponents D))
      (cycleRankEqualsNodeCount D))

record RationalNodalSpecialFibreGenusBoundary : Set where
  field
    oneComponentDualGraphReductionConstructed : Bool
    graphCycleRankDerivedFromEuler : Bool
    rationalNodalGenusEqualsNodeCount : Bool
    modularCurveSpecialFibreConstructedHere : Bool
    flatGenusPreservationConstructedHere : Bool

canonicalRationalNodalSpecialFibreGenusBoundary :
  RationalNodalSpecialFibreGenusBoundary
canonicalRationalNodalSpecialFibreGenusBoundary = record
  { oneComponentDualGraphReductionConstructed = true
  ; graphCycleRankDerivedFromEuler = true
  ; rationalNodalGenusEqualsNodeCount = true
  ; modularCurveSpecialFibreConstructedHere = false
  ; flatGenusPreservationConstructedHere = false
  }
