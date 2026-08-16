module DASHI.Foundations.BinaryPolyhedralMcKayDimensionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- John McKay,
-- "Graphs, Singularities, and Finite Groups",
-- Proceedings of Symposia in Pure Mathematics 37 (1980), 183--186.
-- No DOI asserted here.
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics 129,
-- Springer.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- DASHI CONTRIBUTION
--
-- Record the finite dimension/eigenvector skeleton of the SU(2) binary
-- polyhedral McKay graphs.  For the affine E6/E7/E8 graphs the vector of irrep
-- dimensions d satisfies
--
--   adjacency * d = 2 * d,
--
-- where 2 is the natural SU(2) doublet dimension.  The squared dimensions sum
-- to the binary tetrahedral/octahedral/icosahedral group orders 24/48/120.
--
-- This module does not construct the binary polyhedral groups, their actual
-- representations, or the full McKay correspondence internally.  It is an
-- exact finite compatibility surface for the p=2 spinorial reduction lane and
-- an exceptional-symmetry neighbour of the SSP programme, not an Ogg selector.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin

sumNat : List Nat → Nat
sumNat [] = 0
sumNat (x ∷ xs) = x + sumNat xs

------------------------------------------------------------------------
-- Binary tetrahedral: affine E6, seven irrep nodes.
------------------------------------------------------------------------

data E6Node : Set where
  e6Central3
    e6ArmA2 e6ArmB2 e6ArmC2
    e6LeafA1 e6LeafB1 e6LeafC1 : E6Node

e6Dimension : E6Node → Nat
e6Dimension e6Central3 = 3
e6Dimension e6ArmA2 = 2
e6Dimension e6ArmB2 = 2
e6Dimension e6ArmC2 = 2
e6Dimension e6LeafA1 = 1
e6Dimension e6LeafB1 = 1
e6Dimension e6LeafC1 = 1

e6Neighbours : E6Node → List E6Node
e6Neighbours e6Central3 = e6ArmA2 ∷ e6ArmB2 ∷ e6ArmC2 ∷ []
e6Neighbours e6ArmA2 = e6Central3 ∷ e6LeafA1 ∷ []
e6Neighbours e6ArmB2 = e6Central3 ∷ e6LeafB1 ∷ []
e6Neighbours e6ArmC2 = e6Central3 ∷ e6LeafC1 ∷ []
e6Neighbours e6LeafA1 = e6ArmA2 ∷ []
e6Neighbours e6LeafB1 = e6ArmB2 ∷ []
e6Neighbours e6LeafC1 = e6ArmC2 ∷ []

sumNodeDimensions :
  {Node : Set} →
  (dimension : Node → Nat) →
  List Node → Nat
sumNodeDimensions dimension [] = 0
sumNodeDimensions dimension (node ∷ nodes) =
  dimension node + sumNodeDimensions dimension nodes

e6McKayDimensionEquation :
  (node : E6Node) →
  2 * e6Dimension node
  ≡ sumNodeDimensions e6Dimension (e6Neighbours node)
e6McKayDimensionEquation e6Central3 = refl
e6McKayDimensionEquation e6ArmA2 = refl
e6McKayDimensionEquation e6ArmB2 = refl
e6McKayDimensionEquation e6ArmC2 = refl
e6McKayDimensionEquation e6LeafA1 = refl
e6McKayDimensionEquation e6LeafB1 = refl
e6McKayDimensionEquation e6LeafC1 = refl

e6DimensionSquareSum : Nat
e6DimensionSquareSum =
  3 * 3 + 2 * 2 + 2 * 2 + 2 * 2 + 1 + 1 + 1

e6BinaryTetrahedralOrder : e6DimensionSquareSum ≡ 24
e6BinaryTetrahedralOrder = refl

------------------------------------------------------------------------
-- Binary octahedral: affine E7, eight irrep nodes.
--
--       branch2
--          |
-- 1 - 2 - 3 - 4 - 3 - 2 - 1
------------------------------------------------------------------------

data E7Node : Set where
  e7Left1 e7Left2 e7Left3 e7Central4
    e7Right3 e7Right2 e7Right1 e7Branch2 : E7Node

e7Dimension : E7Node → Nat
e7Dimension e7Left1 = 1
e7Dimension e7Left2 = 2
e7Dimension e7Left3 = 3
e7Dimension e7Central4 = 4
e7Dimension e7Right3 = 3
e7Dimension e7Right2 = 2
e7Dimension e7Right1 = 1
e7Dimension e7Branch2 = 2

e7Neighbours : E7Node → List E7Node
e7Neighbours e7Left1 = e7Left2 ∷ []
e7Neighbours e7Left2 = e7Left1 ∷ e7Left3 ∷ []
e7Neighbours e7Left3 = e7Left2 ∷ e7Central4 ∷ []
e7Neighbours e7Central4 = e7Left3 ∷ e7Right3 ∷ e7Branch2 ∷ []
e7Neighbours e7Right3 = e7Central4 ∷ e7Right2 ∷ []
e7Neighbours e7Right2 = e7Right3 ∷ e7Right1 ∷ []
e7Neighbours e7Right1 = e7Right2 ∷ []
e7Neighbours e7Branch2 = e7Central4 ∷ []

e7McKayDimensionEquation :
  (node : E7Node) →
  2 * e7Dimension node
  ≡ sumNodeDimensions e7Dimension (e7Neighbours node)
e7McKayDimensionEquation e7Left1 = refl
e7McKayDimensionEquation e7Left2 = refl
e7McKayDimensionEquation e7Left3 = refl
e7McKayDimensionEquation e7Central4 = refl
e7McKayDimensionEquation e7Right3 = refl
e7McKayDimensionEquation e7Right2 = refl
e7McKayDimensionEquation e7Right1 = refl
e7McKayDimensionEquation e7Branch2 = refl

e7DimensionSquareSum : Nat
e7DimensionSquareSum =
  1 + 2 * 2 + 3 * 3 + 4 * 4 + 3 * 3 + 2 * 2 + 1 + 2 * 2

e7BinaryOctahedralOrder : e7DimensionSquareSum ≡ 48
e7BinaryOctahedralOrder = refl

------------------------------------------------------------------------
-- Binary icosahedral: affine E8, nine irrep nodes.
--
--                 branch3
--                    |
-- 1 - 2 - 3 - 4 - 5 - 6 - 4 - 2
------------------------------------------------------------------------

data E8Node : Set where
  e8Left1 e8Left2 e8Left3 e8Left4 e8Left5 e8Central6
    e8Right4 e8Right2 e8Branch3 : E8Node

e8Dimension : E8Node → Nat
e8Dimension e8Left1 = 1
e8Dimension e8Left2 = 2
e8Dimension e8Left3 = 3
e8Dimension e8Left4 = 4
e8Dimension e8Left5 = 5
e8Dimension e8Central6 = 6
e8Dimension e8Right4 = 4
e8Dimension e8Right2 = 2
e8Dimension e8Branch3 = 3

e8Neighbours : E8Node → List E8Node
e8Neighbours e8Left1 = e8Left2 ∷ []
e8Neighbours e8Left2 = e8Left1 ∷ e8Left3 ∷ []
e8Neighbours e8Left3 = e8Left2 ∷ e8Left4 ∷ []
e8Neighbours e8Left4 = e8Left3 ∷ e8Left5 ∷ []
e8Neighbours e8Left5 = e8Left4 ∷ e8Central6 ∷ []
e8Neighbours e8Central6 = e8Left5 ∷ e8Right4 ∷ e8Branch3 ∷ []
e8Neighbours e8Right4 = e8Central6 ∷ e8Right2 ∷ []
e8Neighbours e8Right2 = e8Right4 ∷ []
e8Neighbours e8Branch3 = e8Central6 ∷ []

e8McKayDimensionEquation :
  (node : E8Node) →
  2 * e8Dimension node
  ≡ sumNodeDimensions e8Dimension (e8Neighbours node)
e8McKayDimensionEquation e8Left1 = refl
e8McKayDimensionEquation e8Left2 = refl
e8McKayDimensionEquation e8Left3 = refl
e8McKayDimensionEquation e8Left4 = refl
e8McKayDimensionEquation e8Left5 = refl
e8McKayDimensionEquation e8Central6 = refl
e8McKayDimensionEquation e8Right4 = refl
e8McKayDimensionEquation e8Right2 = refl
e8McKayDimensionEquation e8Branch3 = refl

e8DimensionSquareSum : Nat
e8DimensionSquareSum =
  1 + 2 * 2 + 3 * 3 + 4 * 4 + 5 * 5 + 6 * 6
  + 4 * 4 + 2 * 2 + 3 * 3

e8BinaryIcosahedralOrder : e8DimensionSquareSum ≡ 120
e8BinaryIcosahedralOrder = refl

------------------------------------------------------------------------
-- Link to the explicitly typed p=2 SU(2) lane.
------------------------------------------------------------------------

naturalSU2DoubletDimensionIsTwo : Spin.su2Dimension 1 ≡ 2
naturalSU2DoubletDimensionIsTwo = Spin.spinHalfDimensionIsTwo

e6NodeCount e7NodeCount e8NodeCount : Nat
e6NodeCount = 7
e7NodeCount = 8
e8NodeCount = 9

record BinaryPolyhedralMcKayBoundary : Set where
  field
    affineE6DimensionSkeletonConstructed : Bool
    affineE6DimensionSkeletonConstructedIsTrue :
      affineE6DimensionSkeletonConstructed ≡ true

    affineE7DimensionSkeletonConstructed : Bool
    affineE7DimensionSkeletonConstructedIsTrue :
      affineE7DimensionSkeletonConstructed ≡ true

    affineE8DimensionSkeletonConstructed : Bool
    affineE8DimensionSkeletonConstructedIsTrue :
      affineE8DimensionSkeletonConstructed ≡ true

    naturalDoubletActsAsDimensionEigenvalue : Bool
    naturalDoubletActsAsDimensionEigenvalueIsTrue :
      naturalDoubletActsAsDimensionEigenvalue ≡ true

    fullBinaryPolyhedralRepresentationsConstructed : Bool
    fullBinaryPolyhedralRepresentationsConstructedIsFalse :
      fullBinaryPolyhedralRepresentationsConstructed ≡ false

    McKaySkeletonClaimedToSelectOggPrimes : Bool
    McKaySkeletonClaimedToSelectOggPrimesIsFalse :
      McKaySkeletonClaimedToSelectOggPrimes ≡ false

canonicalBinaryPolyhedralMcKayBoundary : BinaryPolyhedralMcKayBoundary
canonicalBinaryPolyhedralMcKayBoundary =
  record
    { affineE6DimensionSkeletonConstructed = true
    ; affineE6DimensionSkeletonConstructedIsTrue = refl
    ; affineE7DimensionSkeletonConstructed = true
    ; affineE7DimensionSkeletonConstructedIsTrue = refl
    ; affineE8DimensionSkeletonConstructed = true
    ; affineE8DimensionSkeletonConstructedIsTrue = refl
    ; naturalDoubletActsAsDimensionEigenvalue = true
    ; naturalDoubletActsAsDimensionEigenvalueIsTrue = refl
    ; fullBinaryPolyhedralRepresentationsConstructed = false
    ; fullBinaryPolyhedralRepresentationsConstructedIsFalse = refl
    ; McKaySkeletonClaimedToSelectOggPrimes = false
    ; McKaySkeletonClaimedToSelectOggPrimesIsFalse = refl
    }
