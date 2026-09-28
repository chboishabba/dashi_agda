module DASHI.Foundations.BalancedTernaryHypercubeAntipodalOrbitCountExact where

------------------------------------------------------------------------
-- BALANCED-TERNARY HYPERCUBE ANTIPODAL ORBIT COUNT
--
-- DASHI CONTRIBUTION
--
-- This module factors the common finite count mechanism behind the existing
-- n=1 and n=2 antipodal carriers.
--
-- For a ternary n-cube under global sign inversion there is one all-zero
-- fixed state and every nonzero state belongs to a two-element antipodal
-- pair.  Rather than use Nat division, define the pair count recursively:
--
--   P 0       = 0
--   P (n + 1) = 1 + 3 * P n
--
-- and orbit count O n = 1 + P n.
--
-- We prove the division-free identities
--
--   3^n = 1 + 2 P n
--   2 O n = 3^n + 1.
--
-- This is a CARDINALITY theorem.  It does not construct a generic quotient
-- action groupoid, identify an arithmetic supersingular object, or transfer
-- external authority to the Base369 interpretation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

import DASHI.Biology.TernaryHypercubeHyperfabricExact as Hyper

------------------------------------------------------------------------
-- 1. Canonical recursive pair/orbit counts.
------------------------------------------------------------------------

antipodalPairCount : Nat -> Nat
antipodalPairCount zero = 0
antipodalPairCount (suc n) = 1 + 3 * antipodalPairCount n

antipodalOrbitCount : Nat -> Nat
antipodalOrbitCount n = 1 + antipodalPairCount n

ternaryStateCount : Nat -> Nat
ternaryStateCount = Hyper.ternaryLatticeCount

------------------------------------------------------------------------
-- 2. Fixed point plus antipodal-pair decomposition.
------------------------------------------------------------------------

ternaryStateSplitExact :
  (n : Nat) ->
  ternaryStateCount n
  ≡
  1 + 2 * antipodalPairCount n
ternaryStateSplitExact zero = refl
ternaryStateSplitExact (suc n)
  rewrite ternaryStateSplitExact n =
  solve 1
    (lambda p ->
      (con 3 :* (con 1 :+ (con 2 :* p)))
      :=
      con 1 :+ (con 2 :* (con 1 :+ (con 3 :* p))))
    refl
    (antipodalPairCount n)

doubleOrbitCountExact :
  (n : Nat) ->
  2 * antipodalOrbitCount n
  ≡
  ternaryStateCount n + 1
doubleOrbitCountExact n =
  trans
    (solve 1
      (lambda p ->
        con 2 :* (con 1 :+ p)
        :=
        (con 1 :+ (con 2 :* p)) :+ con 1)
      refl
      (antipodalPairCount n))
    (cong
      (lambda count -> count + 1)
      (sym (ternaryStateSplitExact n)))

------------------------------------------------------------------------
-- 3. First three exact specialisations.
------------------------------------------------------------------------

pairCountOneIsOne :
  antipodalPairCount 1 ≡ 1
pairCountOneIsOne = refl

pairCountTwoIsFour :
  antipodalPairCount 2 ≡ 4
pairCountTwoIsFour = refl

pairCountThreeIsThirteen :
  antipodalPairCount 3 ≡ 13
pairCountThreeIsThirteen = refl

orbitCountOneIsTwo :
  antipodalOrbitCount 1 ≡ 2
orbitCountOneIsTwo = refl

orbitCountTwoIsFive :
  antipodalOrbitCount 2 ≡ 5
orbitCountTwoIsFive = refl

orbitCountThreeIsFourteen :
  antipodalOrbitCount 3 ≡ 14
orbitCountThreeIsFourteen = refl

ternaryOneSplit :
  ternaryStateCount 1 ≡ 1 + 2 * 1
ternaryOneSplit = refl

ternaryTwoSplit :
  ternaryStateCount 2 ≡ 1 + 2 * 4
ternaryTwoSplit = refl

ternaryThreeSplit :
  ternaryStateCount 3 ≡ 1 + 2 * 13
ternaryThreeSplit = refl

------------------------------------------------------------------------
-- 4. Exceptional residual target count pattern.
------------------------------------------------------------------------

p3TargetCountFromOneTritOrbit :
  antipodalOrbitCount 1 ≡ 2
p3TargetCountFromOneTritOrbit = orbitCountOneIsTwo

p2FiveOrbitBaseFromTwoTritOrbit :
  antipodalOrbitCount 2 ≡ 5
p2FiveOrbitBaseFromTwoTritOrbit = orbitCountTwoIsFive

p2RetainedBinarySheetCount :
  2 * antipodalOrbitCount 2 ≡ 10
p2RetainedBinarySheetCount = refl

------------------------------------------------------------------------
-- 5. Firewall.
------------------------------------------------------------------------

data OrbitCountConstructsGenericActionGroupoid : Set where
data OrbitCountIdentifiesArithmeticResidualSource : Set where
data FibonacciAdjacencyProvesArithmeticRecognition : Set where

orbitCountDoesNotConstructGenericActionGroupoid :
  OrbitCountConstructsGenericActionGroupoid -> ⊥
orbitCountDoesNotConstructGenericActionGroupoid ()

orbitCountDoesNotIdentifyArithmeticResidualSource :
  OrbitCountIdentifiesArithmeticResidualSource -> ⊥
orbitCountDoesNotIdentifyArithmeticResidualSource ()

fibonacciAdjacencyDoesNotProveArithmeticRecognition :
  FibonacciAdjacencyProvesArithmeticRecognition -> ⊥
fibonacciAdjacencyDoesNotProveArithmeticRecognition ()

record BalancedTernaryHypercubeAntipodalOrbitCountBoundary : Set where
  constructor balanced-ternary-hypercube-antipodal-orbit-count-boundary
  field
    reusesCanonicalTernaryHypercubeCount : Bool
    fixedPlusPairedCountTheoremProved : Bool
    divisionFreeOrbitFormulaProved : Bool
    n1OrbitCountTwoProved : Bool
    n2OrbitCountFiveProved : Bool
    n3OrbitCountFourteenProved : Bool
    p2RetainedTwoTimesFiveCountProved : Bool
    genericActionGroupoidConstructedHere : Bool
    arithmeticResidualSourceIdentifiedHere : Bool
    fibonacciAdjacencyPromotedToArithmeticRecognition : Bool

canonicalBalancedTernaryHypercubeAntipodalOrbitCountBoundary :
  BalancedTernaryHypercubeAntipodalOrbitCountBoundary
canonicalBalancedTernaryHypercubeAntipodalOrbitCountBoundary =
  balanced-ternary-hypercube-antipodal-orbit-count-boundary
    true true true true true true true
    false false false
