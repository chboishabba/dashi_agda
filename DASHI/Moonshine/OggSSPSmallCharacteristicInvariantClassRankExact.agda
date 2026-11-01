module DASHI.Moonshine.OggSSPSmallCharacteristicInvariantClassRankExact where

------------------------------------------------------------------------
-- SMALL-CHARACTERISTIC INVARIANT-CLASS-FUNCTION RANK SKELETON
--
-- p=2
-- ----
-- The characteristic-2 supersingular automorphism group is binary tetrahedral.
-- Its seven conjugacy classes are the natural basis labels for class functions.
-- Loop reversal / inversion acts on those seven labels; the quotient has five
-- orbits.  Therefore inversion-invariant class functions have a canonical
-- FIVE-SECTOR basis skeleton.  Tensoring with the two oriented quadratic-order
-- sheets gives a TEN-SECTOR basis skeleton.
--
-- p=3
-- ----
-- The Deligne--Rapoport local three-stratum C2-set has two C2-orbits:
-- node and branch-pair.  Invariant functions on the finite C2-set therefore
-- have a TWO-SECTOR basis skeleton.
--
-- This removes the arbitrariness from "one unit per sector": one is the basis
-- multiplicity of a finite free invariant-function skeleton.
--
-- FIREWALL
-- -------
-- A basis-rank theorem is still NOT a p-adic valuation theorem.  Nothing here
-- proves that Duncan--Swisher's exceptional Monster gaps equal these ranks.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Product using (_×_; _,_)

import DASHI.Foundations.BinaryPolyhedralMcKayDimensionExact as McKay
import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as P2Inertia
import DASHI.Moonshine.OggSSPP2OrientedInertiaTenStateRecognitionExact as P2Orientation
import DASHI.Moonshine.OggSSPP3DeligneRapoportLocalStrataRecognitionExact as P3
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Generic finite basis-rank skeleton.
------------------------------------------------------------------------

listRank :
  {A : Set} ->
  List A ->
  Nat
listRank [] = 0
listRank (_ ∷ rest) = 1 + listRank rest

------------------------------------------------------------------------
-- 2. p=2: seven raw class-function labels -> five reversal-invariant labels.
------------------------------------------------------------------------

p2RawConjugacyClassBasis :
  List P2Inertia.BinaryTetrahedralConjugacyClass
p2RawConjugacyClassBasis =
  P2Inertia.identityClass
  ∷ P2Inertia.centralMinusOneClass
  ∷ P2Inertia.orderFourClass
  ∷ P2Inertia.orderThreePositiveClass
  ∷ P2Inertia.orderThreeNegativeClass
  ∷ P2Inertia.orderSixPositiveClass
  ∷ P2Inertia.orderSixNegativeClass
  ∷ []

p2RawClassFunctionRank :
  listRank p2RawConjugacyClassBasis ≡ 7
p2RawClassFunctionRank = refl

p2McKayNodeCountAgreesWithRawClassRank :
  McKay.e6NodeCount ≡ listRank p2RawConjugacyClassBasis
p2McKayNodeCountAgreesWithRawClassRank = refl

p2InvariantClassBasis :
  List P2Inertia.BinaryTetrahedralInversionOrbit
p2InvariantClassBasis =
  P2Inertia.identityInertiaOrbit
  ∷ P2Inertia.centralMinusOneInertiaOrbit
  ∷ P2Inertia.orderFourInertiaOrbit
  ∷ P2Inertia.orderThreePairInertiaOrbit
  ∷ P2Inertia.orderSixPairInertiaOrbit
  ∷ []

p2InvariantClassFunctionRank :
  listRank p2InvariantClassBasis ≡ 5
p2InvariantClassFunctionRank = refl

------------------------------------------------------------------------
-- 3. p=2 orientation doublet x invariant class basis = rank 10.
------------------------------------------------------------------------

P2OrientedInvariantBasis : Set
P2OrientedInvariantBasis =
  P2Orientation.ClassicalQuadraticOrientation
  × P2Inertia.BinaryTetrahedralInversionOrbit

p2OrientedInvariantBasis :
  List P2OrientedInvariantBasis
p2OrientedInvariantBasis =
  (P2Orientation.firstGaloisOrientation ,
    P2Inertia.identityInertiaOrbit)
  ∷ (P2Orientation.firstGaloisOrientation ,
    P2Inertia.centralMinusOneInertiaOrbit)
  ∷ (P2Orientation.firstGaloisOrientation ,
    P2Inertia.orderFourInertiaOrbit)
  ∷ (P2Orientation.firstGaloisOrientation ,
    P2Inertia.orderThreePairInertiaOrbit)
  ∷ (P2Orientation.firstGaloisOrientation ,
    P2Inertia.orderSixPairInertiaOrbit)
  ∷ (P2Orientation.conjugateGaloisOrientation ,
    P2Inertia.identityInertiaOrbit)
  ∷ (P2Orientation.conjugateGaloisOrientation ,
    P2Inertia.centralMinusOneInertiaOrbit)
  ∷ (P2Orientation.conjugateGaloisOrientation ,
    P2Inertia.orderFourInertiaOrbit)
  ∷ (P2Orientation.conjugateGaloisOrientation ,
    P2Inertia.orderThreePairInertiaOrbit)
  ∷ (P2Orientation.conjugateGaloisOrientation ,
    P2Inertia.orderSixPairInertiaOrbit)
  ∷ []

p2OrientedInvariantClassFunctionRank :
  listRank p2OrientedInvariantBasis ≡ 10
p2OrientedInvariantClassFunctionRank = refl

twoTimesFiveIsTen :
  2 * 5 ≡ 10
twoTimesFiveIsTen = refl

------------------------------------------------------------------------
-- 4. p=3 invariant-function basis on the local incidence C2-set.
------------------------------------------------------------------------

p3InvariantStratumBasis :
  List P3.P3LocalOrbit
p3InvariantStratumBasis =
  P3.nodeOrbit
  ∷ P3.branchOrbit
  ∷ []

p3InvariantStratumFunctionRank :
  listRank p3InvariantStratumBasis ≡ 2
p3InvariantStratumFunctionRank = refl

------------------------------------------------------------------------
-- 5. Unit multiplicity is now "one basis generator", not arbitrary weighting.
------------------------------------------------------------------------

basisMultiplicity :
  {A : Set} ->
  A ->
  Nat
basisMultiplicity basis = 1

sumBasisMultiplicities :
  {A : Set} ->
  List A ->
  Nat
sumBasisMultiplicities [] = 0
sumBasisMultiplicities (_ ∷ rest) =
  1 + sumBasisMultiplicities rest

basisMultiplicitySumEqualsRank :
  {A : Set} ->
  (basis : List A) ->
  sumBasisMultiplicities basis ≡ listRank basis
basisMultiplicitySumEqualsRank [] = refl
basisMultiplicitySumEqualsRank (_ ∷ rest)
  rewrite basisMultiplicitySumEqualsRank rest = refl

p2BasisMultiplicitySumIsTen :
  sumBasisMultiplicities p2OrientedInvariantBasis ≡ 10
p2BasisMultiplicitySumIsTen = refl

p3BasisMultiplicitySumIsTwo :
  sumBasisMultiplicities p3InvariantStratumBasis ≡ 2
p3BasisMultiplicitySumIsTwo = refl

------------------------------------------------------------------------
-- 6. Wrong-type guards.
------------------------------------------------------------------------

data InvariantClassRankIsPadicValuationContribution : Set where
data McKaySevenNodesProveMonsterResidual : Set where
data FiveInvariantClassesAreD4FiveIrreps : Set where
data RankEqualityCreatesMoonshineSameObject : Set where

invariantClassRankDoesNotCreatePadicValuationContribution :
  InvariantClassRankIsPadicValuationContribution -> ⊥
invariantClassRankDoesNotCreatePadicValuationContribution ()

mckaySevenNodesDoNotProveMonsterResidual :
  McKaySevenNodesProveMonsterResidual -> ⊥
mckaySevenNodesDoNotProveMonsterResidual ()

fiveInvariantClassesAreNotDeclaredD4FiveIrreps :
  FiveInvariantClassesAreD4FiveIrreps -> ⊥
fiveInvariantClassesAreNotDeclaredD4FiveIrreps ()

rankEqualityDoesNotCreateMoonshineSameObject :
  RankEqualityCreatesMoonshineSameObject -> ⊥
rankEqualityDoesNotCreateMoonshineSameObject ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record InvariantClassRankBoundary : Set where
  constructor invariant-class-rank-boundary
  field
    p2RawSevenClassBasisConstructed : Bool
    p2AffineE6SevenNodeCountCrossChecksRawRank : Bool
    p2ReversalInvariantBasisRankFive : Bool
    p2OrientationTimesInvariantBasisRankTen : Bool
    p3InvariantLocalStratumRankTwo : Bool
    unitWeightsInterpretedAsBasisMultiplicity : Bool
    rankPromotedToPadicValuation : Bool
    rankPromotedToMonsterMechanism : Bool

canonicalInvariantClassRankBoundary :
  InvariantClassRankBoundary
canonicalInvariantClassRankBoundary =
  invariant-class-rank-boundary
    true true true true true true false false
