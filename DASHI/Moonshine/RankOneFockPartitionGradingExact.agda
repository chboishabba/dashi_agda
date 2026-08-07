module DASHI.Moonshine.RankOneFockPartitionGradingExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Victor G. Kac,
-- "Vertex Algebras for Beginners", second edition,
-- University Lecture Series 10, American Mathematical Society, 1998.
-- No DOI is asserted for the cited AMS book edition.
--
-- Igor Frenkel, James Lepowsky and Arne Meurman,
-- "A natural representation of the Fischer-Griess Monster with the modular
-- function J as character",
-- Proceedings of the National Academy of Sciences 81 (1984), 3256--3260.
-- DOI: 10.1073/pnas.81.10.3256.
--
-- DASHI CONTRIBUTION
--
-- Construct the first six homogeneous grades of the rank-one bosonic Fock
-- carrier.  Basis vectors are indexed explicitly by integer partitions of the
-- energy, giving exact graded dimensions
--
--   1, 1, 2, 3, 5, 7
--
-- in grades 0 through 5.  This is the finite combinatorial core of the
-- character product product_{n>=1}(1-q^n)^(-1).
--
-- Heisenberg commutation relations, infinite Fock completion, conformal
-- vector, VOA Jacobi identity and Dedekind-eta modularity remain separate
-- theorem owners.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Explicit partition-labelled oscillator monomials.
------------------------------------------------------------------------

data RankOneFockBasis : Nat → Set where
  vacuum : RankOneFockBasis 0

  aMinus1 : RankOneFockBasis 1

  aMinus2 : RankOneFockBasis 2
  aMinus1Squared : RankOneFockBasis 2

  aMinus3 : RankOneFockBasis 3
  aMinus2aMinus1 : RankOneFockBasis 3
  aMinus1Cubed : RankOneFockBasis 3

  aMinus4 : RankOneFockBasis 4
  aMinus3aMinus1 : RankOneFockBasis 4
  aMinus2Squared : RankOneFockBasis 4
  aMinus2aMinus1Squared : RankOneFockBasis 4
  aMinus1Fourth : RankOneFockBasis 4

  aMinus5 : RankOneFockBasis 5
  aMinus4aMinus1 : RankOneFockBasis 5
  aMinus3aMinus2 : RankOneFockBasis 5
  aMinus3aMinus1Squared : RankOneFockBasis 5
  aMinus2SquaredaMinus1 : RankOneFockBasis 5
  aMinus2aMinus1Cubed : RankOneFockBasis 5
  aMinus1Fifth : RankOneFockBasis 5

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ values) = suc (listLength values)

gradeZeroBasis : List (RankOneFockBasis 0)
gradeZeroBasis = vacuum ∷ []

gradeOneBasis : List (RankOneFockBasis 1)
gradeOneBasis = aMinus1 ∷ []

gradeTwoBasis : List (RankOneFockBasis 2)
gradeTwoBasis = aMinus2 ∷ aMinus1Squared ∷ []

gradeThreeBasis : List (RankOneFockBasis 3)
gradeThreeBasis =
  aMinus3 ∷ aMinus2aMinus1 ∷ aMinus1Cubed ∷ []

gradeFourBasis : List (RankOneFockBasis 4)
gradeFourBasis =
  aMinus4
  ∷ aMinus3aMinus1
  ∷ aMinus2Squared
  ∷ aMinus2aMinus1Squared
  ∷ aMinus1Fourth
  ∷ []

gradeFiveBasis : List (RankOneFockBasis 5)
gradeFiveBasis =
  aMinus5
  ∷ aMinus4aMinus1
  ∷ aMinus3aMinus2
  ∷ aMinus3aMinus1Squared
  ∷ aMinus2SquaredaMinus1
  ∷ aMinus2aMinus1Cubed
  ∷ aMinus1Fifth
  ∷ []

gradeZeroDimension : listLength gradeZeroBasis ≡ 1
gradeZeroDimension = refl

gradeOneDimension : listLength gradeOneBasis ≡ 1
gradeOneDimension = refl

gradeTwoDimension : listLength gradeTwoBasis ≡ 2
gradeTwoDimension = refl

gradeThreeDimension : listLength gradeThreeBasis ≡ 3
gradeThreeDimension = refl

gradeFourDimension : listLength gradeFourBasis ≡ 5
gradeFourDimension = refl

gradeFiveDimension : listLength gradeFiveBasis ≡ 7
gradeFiveDimension = refl

fockCharacterPrefix : List Nat
fockCharacterPrefix = 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 7 ∷ []

record FockPrefixCertificate : Set where
  field
    dimension0 : listLength gradeZeroBasis ≡ 1
    dimension1 : listLength gradeOneBasis ≡ 1
    dimension2 : listLength gradeTwoBasis ≡ 2
    dimension3 : listLength gradeThreeBasis ≡ 3
    dimension4 : listLength gradeFourBasis ≡ 5
    dimension5 : listLength gradeFiveBasis ≡ 7

canonicalFockPrefixCertificate : FockPrefixCertificate
canonicalFockPrefixCertificate = record
  { dimension0 = gradeZeroDimension
  ; dimension1 = gradeOneDimension
  ; dimension2 = gradeTwoDimension
  ; dimension3 = gradeThreeDimension
  ; dimension4 = gradeFourDimension
  ; dimension5 = gradeFiveDimension
  }

record RankOneHeisenbergVOABoundary : Set₁ where
  field
    Oscillator : Set
    commutatorRelation : Set
    vacuumAnnihilation : Set
    infiniteFockDirectSum : Set
    normalOrderedVertexFields : Set
    conformalVector : Set
    centralChargeOne : Set
    jacobiIdentity : Set
    characterEqualsPartitionProduct : Set
    etaTransformationLaw : Set

data FockCompletionLayer : Set where
  finitePartitionPrefix infiniteHeisenbergVOA : FockCompletionLayer

finitePrefixIsNotInfiniteVOA :
  finitePartitionPrefix ≡ infiniteHeisenbergVOA → ⊥
finitePrefixIsNotInfiniteVOA ()
