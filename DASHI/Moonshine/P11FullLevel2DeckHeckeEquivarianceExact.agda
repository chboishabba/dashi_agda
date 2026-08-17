module DASHI.Moonshine.P11FullLevel2DeckHeckeEquivarianceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Annals of Mathematics Studies 108,
-- Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005.
-- DOI: 10.1007/978-0-387-27226-9.
--
-- SOURCE ROLE
--
-- Full level-2 structures carry the right change-of-frame action of
-- GL_2(F_2) ~= S_3.  Prime-to-level Hecke correspondences are compatible with
-- the auxiliary level structure, so odd-prime Hecke should be equivariant with
-- this deck action.
--
-- DASHI CONTRIBUTION
--
-- Starting from the explicit regular six-frame S3 torsor constructed in
-- P11FullLevel2RigidificationExact, construct commuting RIGHT frame changes,
-- descend them to the 2+3 rigidified quotient, and prove the existing positive
-- R3 and R5 adjacency multiplicities are invariant under the descended deck
-- generators.  This symmetry was not used when R3/R5 were discovered.
--
-- IMPORTANT BOUNDARY
--
-- This proves a necessary moduli-compatible symmetry of the existing finite
-- correspondences.  It does NOT identify their individual permutation summands
-- with canonical isogenies or double cosets.  R2 is deliberately excluded from
-- the source-facing prime-to-level claim because 2 divides the auxiliary level.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.PositiveFiniteNeighbourSystemExact as Positive
import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11FiveStatePositiveHeckeAlgebraExact as Algebra
import DASHI.Moonshine.P11FullLevel2RigidificationExact as Level2

------------------------------------------------------------------------
-- Right multiplication on the regular six-frame S3 torsor.
------------------------------------------------------------------------

rightR : Level2.Level2Frame → Level2.Level2Frame
rightR Level2.f0 = Level2.f1
rightR Level2.f1 = Level2.f2
rightR Level2.f2 = Level2.f0
rightR Level2.f3 = Level2.f5
rightR Level2.f5 = Level2.f4
rightR Level2.f4 = Level2.f3

rightS : Level2.Level2Frame → Level2.Level2Frame
rightS Level2.f0 = Level2.f3
rightS Level2.f3 = Level2.f0
rightS Level2.f1 = Level2.f4
rightS Level2.f4 = Level2.f1
rightS Level2.f2 = Level2.f5
rightS Level2.f5 = Level2.f2

rightR3IsIdentity : (x : Level2.Level2Frame) → rightR (rightR (rightR x)) ≡ x
rightR3IsIdentity Level2.f0 = refl
rightR3IsIdentity Level2.f1 = refl
rightR3IsIdentity Level2.f2 = refl
rightR3IsIdentity Level2.f3 = refl
rightR3IsIdentity Level2.f4 = refl
rightR3IsIdentity Level2.f5 = refl

rightS2IsIdentity : (x : Level2.Level2Frame) → rightS (rightS x) ≡ x
rightS2IsIdentity Level2.f0 = refl
rightS2IsIdentity Level2.f1 = refl
rightS2IsIdentity Level2.f2 = refl
rightS2IsIdentity Level2.f3 = refl
rightS2IsIdentity Level2.f4 = refl
rightS2IsIdentity Level2.f5 = refl

rightSRSIsRInverse :
  (x : Level2.Level2Frame) → rightS (rightR (rightS x)) ≡ rightR (rightR x)
rightSRSIsRInverse Level2.f0 = refl
rightSRSIsRInverse Level2.f1 = refl
rightSRSIsRInverse Level2.f2 = refl
rightSRSIsRInverse Level2.f3 = refl
rightSRSIsRInverse Level2.f4 = refl
rightSRSIsRInverse Level2.f5 = refl

------------------------------------------------------------------------
-- Left stabilizer actions commute with right frame changes.
------------------------------------------------------------------------

leftRCommutesRightR :
  (x : Level2.Level2Frame) → Level2.leftR (rightR x) ≡ rightR (Level2.leftR x)
leftRCommutesRightR Level2.f0 = refl
leftRCommutesRightR Level2.f1 = refl
leftRCommutesRightR Level2.f2 = refl
leftRCommutesRightR Level2.f3 = refl
leftRCommutesRightR Level2.f4 = refl
leftRCommutesRightR Level2.f5 = refl

leftRCommutesRightS :
  (x : Level2.Level2Frame) → Level2.leftR (rightS x) ≡ rightS (Level2.leftR x)
leftRCommutesRightS Level2.f0 = refl
leftRCommutesRightS Level2.f1 = refl
leftRCommutesRightS Level2.f2 = refl
leftRCommutesRightS Level2.f3 = refl
leftRCommutesRightS Level2.f4 = refl
leftRCommutesRightS Level2.f5 = refl

leftSCommutesRightR :
  (x : Level2.Level2Frame) → Level2.leftS (rightR x) ≡ rightR (Level2.leftS x)
leftSCommutesRightR Level2.f0 = refl
leftSCommutesRightR Level2.f1 = refl
leftSCommutesRightR Level2.f2 = refl
leftSCommutesRightR Level2.f3 = refl
leftSCommutesRightR Level2.f4 = refl
leftSCommutesRightR Level2.f5 = refl

leftSCommutesRightS :
  (x : Level2.Level2Frame) → Level2.leftS (rightS x) ≡ rightS (Level2.leftS x)
leftSCommutesRightS Level2.f0 = refl
leftSCommutesRightS Level2.f1 = refl
leftSCommutesRightS Level2.f2 = refl
leftSCommutesRightS Level2.f3 = refl
leftSCommutesRightS Level2.f4 = refl
leftSCommutesRightS Level2.f5 = refl

------------------------------------------------------------------------
-- Descended deck action on the existing five-state carrier.
------------------------------------------------------------------------

deckR : Fine.P11Fine5 → Fine.P11Fine5
deckR Fine.a0 = Fine.a0
deckR Fine.a1 = Fine.a1
deckR Fine.b0 = Fine.b1
deckR Fine.b1 = Fine.b2
deckR Fine.b2 = Fine.b0

deckS : Fine.P11Fine5 → Fine.P11Fine5
deckS Fine.a0 = Fine.a1
deckS Fine.a1 = Fine.a0
deckS Fine.b0 = Fine.b0
deckS Fine.b1 = Fine.b2
deckS Fine.b2 = Fine.b1

deckR3IsIdentity : (x : Fine.P11Fine5) → deckR (deckR (deckR x)) ≡ x
deckR3IsIdentity Fine.a0 = refl
deckR3IsIdentity Fine.a1 = refl
deckR3IsIdentity Fine.b0 = refl
deckR3IsIdentity Fine.b1 = refl
deckR3IsIdentity Fine.b2 = refl

deckS2IsIdentity : (x : Fine.P11Fine5) → deckS (deckS x) ≡ x
deckS2IsIdentity Fine.a0 = refl
deckS2IsIdentity Fine.a1 = refl
deckS2IsIdentity Fine.b0 = refl
deckS2IsIdentity Fine.b1 = refl
deckS2IsIdentity Fine.b2 = refl

deckSRSIsRInverse :
  (x : Fine.P11Fine5) → deckS (deckR (deckS x)) ≡ deckR (deckR x)
deckSRSIsRInverse Fine.a0 = refl
deckSRSIsRInverse Fine.a1 = refl
deckSRSIsRInverse Fine.b0 = refl
deckSRSIsRInverse Fine.b1 = refl
deckSRSIsRInverse Fine.b2 = refl

------------------------------------------------------------------------
-- Verify that the descended action is exactly induced by right frame change.
------------------------------------------------------------------------

j0RightRDescends :
  (x : Level2.Level2Frame) →
  Level2.j0OrbitOfFrame (rightR x) ≡ Level2.j0OrbitOfFrame x
j0RightRDescends Level2.f0 = refl
j0RightRDescends Level2.f1 = refl
j0RightRDescends Level2.f2 = refl
j0RightRDescends Level2.f3 = refl
j0RightRDescends Level2.f4 = refl
j0RightRDescends Level2.f5 = refl

j0RightSDescends :
  (x : Level2.Level2Frame) →
  ( Level2.j0OrbitOfFrame x ≡ Level2.j0Orbit0
  → Level2.j0OrbitOfFrame (rightS x) ≡ Level2.j0Orbit1 )
  ×
  ( Level2.j0OrbitOfFrame x ≡ Level2.j0Orbit1
  → Level2.j0OrbitOfFrame (rightS x) ≡ Level2.j0Orbit0 )
j0RightSDescends Level2.f0 = (λ _ → refl) , λ ()
j0RightSDescends Level2.f1 = (λ _ → refl) , λ ()
j0RightSDescends Level2.f2 = (λ _ → refl) , λ ()
j0RightSDescends Level2.f3 = (λ ()) , λ _ → refl
j0RightSDescends Level2.f4 = (λ ()) , λ _ → refl
j0RightSDescends Level2.f5 = (λ ()) , λ _ → refl

------------------------------------------------------------------------
-- Adjacency multiplicity derived from actual positive neighbour systems.
------------------------------------------------------------------------

edgeMultiplicity :
  Positive.PositiveFiniteNeighbourSystem Fine.P11Fine5 →
  Fine.P11Fine5 → Fine.P11Fine5 → Nat
edgeMultiplicity system source target =
  Positive.positiveOperator system (Algebra.indicator target) source

------------------------------------------------------------------------
-- Odd-prime aggregate Hecke equivariance under the level-2 deck generators.
-- The proofs are finite normalization on all source/target pairs.
------------------------------------------------------------------------

r3DeckREquivariant :
  (source target : Fine.P11Fine5) →
  edgeMultiplicity Fine.R3Positive (deckR source) (deckR target)
  ≡ edgeMultiplicity Fine.R3Positive source target
r3DeckREquivariant Fine.a0 Fine.a0 = refl
r3DeckREquivariant Fine.a0 Fine.a1 = refl
r3DeckREquivariant Fine.a0 Fine.b0 = refl
r3DeckREquivariant Fine.a0 Fine.b1 = refl
r3DeckREquivariant Fine.a0 Fine.b2 = refl
r3DeckREquivariant Fine.a1 Fine.a0 = refl
r3DeckREquivariant Fine.a1 Fine.a1 = refl
r3DeckREquivariant Fine.a1 Fine.b0 = refl
r3DeckREquivariant Fine.a1 Fine.b1 = refl
r3DeckREquivariant Fine.a1 Fine.b2 = refl
r3DeckREquivariant Fine.b0 Fine.a0 = refl
r3DeckREquivariant Fine.b0 Fine.a1 = refl
r3DeckREquivariant Fine.b0 Fine.b0 = refl
r3DeckREquivariant Fine.b0 Fine.b1 = refl
r3DeckREquivariant Fine.b0 Fine.b2 = refl
r3DeckREquivariant Fine.b1 Fine.a0 = refl
r3DeckREquivariant Fine.b1 Fine.a1 = refl
r3DeckREquivariant Fine.b1 Fine.b0 = refl
r3DeckREquivariant Fine.b1 Fine.b1 = refl
r3DeckREquivariant Fine.b1 Fine.b2 = refl
r3DeckREquivariant Fine.b2 Fine.a0 = refl
r3DeckREquivariant Fine.b2 Fine.a1 = refl
r3DeckREquivariant Fine.b2 Fine.b0 = refl
r3DeckREquivariant Fine.b2 Fine.b1 = refl
r3DeckREquivariant Fine.b2 Fine.b2 = refl

r3DeckSEquivariant :
  (source target : Fine.P11Fine5) →
  edgeMultiplicity Fine.R3Positive (deckS source) (deckS target)
  ≡ edgeMultiplicity Fine.R3Positive source target
r3DeckSEquivariant Fine.a0 Fine.a0 = refl
r3DeckSEquivariant Fine.a0 Fine.a1 = refl
r3DeckSEquivariant Fine.a0 Fine.b0 = refl
r3DeckSEquivariant Fine.a0 Fine.b1 = refl
r3DeckSEquivariant Fine.a0 Fine.b2 = refl
r3DeckSEquivariant Fine.a1 Fine.a0 = refl
r3DeckSEquivariant Fine.a1 Fine.a1 = refl
r3DeckSEquivariant Fine.a1 Fine.b0 = refl
r3DeckSEquivariant Fine.a1 Fine.b1 = refl
r3DeckSEquivariant Fine.a1 Fine.b2 = refl
r3DeckSEquivariant Fine.b0 Fine.a0 = refl
r3DeckSEquivariant Fine.b0 Fine.a1 = refl
r3DeckSEquivariant Fine.b0 Fine.b0 = refl
r3DeckSEquivariant Fine.b0 Fine.b1 = refl
r3DeckSEquivariant Fine.b0 Fine.b2 = refl
r3DeckSEquivariant Fine.b1 Fine.a0 = refl
r3DeckSEquivariant Fine.b1 Fine.a1 = refl
r3DeckSEquivariant Fine.b1 Fine.b0 = refl
r3DeckSEquivariant Fine.b1 Fine.b1 = refl
r3DeckSEquivariant Fine.b1 Fine.b2 = refl
r3DeckSEquivariant Fine.b2 Fine.a0 = refl
r3DeckSEquivariant Fine.b2 Fine.a1 = refl
r3DeckSEquivariant Fine.b2 Fine.b0 = refl
r3DeckSEquivariant Fine.b2 Fine.b1 = refl
r3DeckSEquivariant Fine.b2 Fine.b2 = refl

r5DeckREquivariant :
  (source target : Fine.P11Fine5) →
  edgeMultiplicity Fine.R5Positive (deckR source) (deckR target)
  ≡ edgeMultiplicity Fine.R5Positive source target
r5DeckREquivariant Fine.a0 Fine.a0 = refl
r5DeckREquivariant Fine.a0 Fine.a1 = refl
r5DeckREquivariant Fine.a0 Fine.b0 = refl
r5DeckREquivariant Fine.a0 Fine.b1 = refl
r5DeckREquivariant Fine.a0 Fine.b2 = refl
r5DeckREquivariant Fine.a1 Fine.a0 = refl
r5DeckREquivariant Fine.a1 Fine.a1 = refl
r5DeckREquivariant Fine.a1 Fine.b0 = refl
r5DeckREquivariant Fine.a1 Fine.b1 = refl
r5DeckREquivariant Fine.a1 Fine.b2 = refl
r5DeckREquivariant Fine.b0 Fine.a0 = refl
r5DeckREquivariant Fine.b0 Fine.a1 = refl
r5DeckREquivariant Fine.b0 Fine.b0 = refl
r5DeckREquivariant Fine.b0 Fine.b1 = refl
r5DeckREquivariant Fine.b0 Fine.b2 = refl
r5DeckREquivariant Fine.b1 Fine.a0 = refl
r5DeckREquivariant Fine.b1 Fine.a1 = refl
r5DeckREquivariant Fine.b1 Fine.b0 = refl
r5DeckREquivariant Fine.b1 Fine.b1 = refl
r5DeckREquivariant Fine.b1 Fine.b2 = refl
r5DeckREquivariant Fine.b2 Fine.a0 = refl
r5DeckREquivariant Fine.b2 Fine.a1 = refl
r5DeckREquivariant Fine.b2 Fine.b0 = refl
r5DeckREquivariant Fine.b2 Fine.b1 = refl
r5DeckREquivariant Fine.b2 Fine.b2 = refl

r5DeckSEquivariant :
  (source target : Fine.P11Fine5) →
  edgeMultiplicity Fine.R5Positive (deckS source) (deckS target)
  ≡ edgeMultiplicity Fine.R5Positive source target
r5DeckSEquivariant Fine.a0 Fine.a0 = refl
r5DeckSEquivariant Fine.a0 Fine.a1 = refl
r5DeckSEquivariant Fine.a0 Fine.b0 = refl
r5DeckSEquivariant Fine.a0 Fine.b1 = refl
r5DeckSEquivariant Fine.a0 Fine.b2 = refl
r5DeckSEquivariant Fine.a1 Fine.a0 = refl
r5DeckSEquivariant Fine.a1 Fine.a1 = refl
r5DeckSEquivariant Fine.a1 Fine.b0 = refl
r5DeckSEquivariant Fine.a1 Fine.b1 = refl
r5DeckSEquivariant Fine.a1 Fine.b2 = refl
r5DeckSEquivariant Fine.b0 Fine.a0 = refl
r5DeckSEquivariant Fine.b0 Fine.a1 = refl
r5DeckSEquivariant Fine.b0 Fine.b0 = refl
r5DeckSEquivariant Fine.b0 Fine.b1 = refl
r5DeckSEquivariant Fine.b0 Fine.b2 = refl
r5DeckSEquivariant Fine.b1 Fine.a0 = refl
r5DeckSEquivariant Fine.b1 Fine.a1 = refl
r5DeckSEquivariant Fine.b1 Fine.b0 = refl
r5DeckSEquivariant Fine.b1 Fine.b1 = refl
r5DeckSEquivariant Fine.b1 Fine.b2 = refl
r5DeckSEquivariant Fine.b2 Fine.a0 = refl
r5DeckSEquivariant Fine.b2 Fine.a1 = refl
r5DeckSEquivariant Fine.b2 Fine.b0 = refl
r5DeckSEquivariant Fine.b2 Fine.b1 = refl
r5DeckSEquivariant Fine.b2 Fine.b2 = refl

record P11FullLevel2DeckHeckeBoundary : Set where
  field
    rightDeckS3ConstructedFromFrameTorsor : Bool
    rightDeckS3ConstructedFromFrameTorsorIsTrue :
      rightDeckS3ConstructedFromFrameTorsor ≡ true

    rightDeckCommutesWithReducedAutomorphisms : Bool
    rightDeckCommutesWithReducedAutomorphismsIsTrue :
      rightDeckCommutesWithReducedAutomorphisms ≡ true

    oddR3R5AggregateDeckEquivarianceConstructed : Bool
    oddR3R5AggregateDeckEquivarianceConstructedIsTrue :
      oddR3R5AggregateDeckEquivarianceConstructed ≡ true

    individualPermutationSummandsCanonicalIsogenies : Bool
    individualPermutationSummandsCanonicalIsogeniesIsFalse :
      individualPermutationSummandsCanonicalIsogenies ≡ false

    ell2PrimeToLevelCompatibilityClaimed : Bool
    ell2PrimeToLevelCompatibilityClaimedIsFalse :
      ell2PrimeToLevelCompatibilityClaimed ≡ false

canonicalP11FullLevel2DeckHeckeBoundary : P11FullLevel2DeckHeckeBoundary
canonicalP11FullLevel2DeckHeckeBoundary =
  record
    { rightDeckS3ConstructedFromFrameTorsor = true
    ; rightDeckS3ConstructedFromFrameTorsorIsTrue = refl
    ; rightDeckCommutesWithReducedAutomorphisms = true
    ; rightDeckCommutesWithReducedAutomorphismsIsTrue = refl
    ; oddR3R5AggregateDeckEquivarianceConstructed = true
    ; oddR3R5AggregateDeckEquivarianceConstructedIsTrue = refl
    ; individualPermutationSummandsCanonicalIsogenies = false
    ; individualPermutationSummandsCanonicalIsogeniesIsFalse = refl
    ; ell2PrimeToLevelCompatibilityClaimed = false
    ; ell2PrimeToLevelCompatibilityClaimedIsFalse = refl
    }
