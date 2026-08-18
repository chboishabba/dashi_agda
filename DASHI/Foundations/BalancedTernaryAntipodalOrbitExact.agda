module DASHI.Foundations.BalancedTernaryAntipodalOrbitExact where

------------------------------------------------------------------------
-- SOURCE / METHOD CALIBRATION
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Graduate Texts in Mathematics 42,
-- Springer, 1977. DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Put an explicit C2 antipodal action on the repository's canonical typed
-- SSP trit {-1,0,+1}.  The negative pole is the strict antipode of the
-- positive pole; zero is the unique fixed centre.  The resulting orbit
-- quotients are action-indexed geometry, not Boolean truth, logical negation,
-- or decision semantics.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)

import DASHI.Foundations.Base369AddressSymmetryAndBranchGeometryExact as Branch
import DASHI.Foundations.SSPTritCarrier as SSP

strictAntipode : SSP.SSPTrit → SSP.SSPTrit
strictAntipode SSP.sspNegOne = SSP.sspPosOne
strictAntipode SSP.sspZero = SSP.sspZero
strictAntipode SSP.sspPosOne = SSP.sspNegOne

strictAntipodeInvolutive :
  (x : SSP.SSPTrit) → strictAntipode (strictAntipode x) ≡ x
strictAntipodeInvolutive SSP.sspNegOne = refl
strictAntipodeInvolutive SSP.sspZero = refl
strictAntipodeInvolutive SSP.sspPosOne = refl

zeroIsAntipodeFixedCentre : strictAntipode SSP.sspZero ≡ SSP.sspZero
zeroIsAntipodeFixedCentre = refl

positiveAntipodeIsNegative : strictAntipode SSP.sspPosOne ≡ SSP.sspNegOne
positiveAntipodeIsNegative = refl

negativeAntipodeIsPositive : strictAntipode SSP.sspNegOne ≡ SSP.sspPosOne
negativeAntipodeIsPositive = refl

zeroIsNotNegativePole : SSP.sspZero ≡ SSP.sspNegOne → ⊥
zeroIsNotNegativePole ()

zeroIsNotPositivePole : SSP.sspZero ≡ SSP.sspPosOne → ⊥
zeroIsNotPositivePole ()

------------------------------------------------------------------------
-- Strict antipodal action on a three-coordinate ternary block.
------------------------------------------------------------------------

TritTriple : Set
TritTriple = Branch.Triple SSP.SSPTrit

strictAntipodeTriple : TritTriple → TritTriple
strictAntipodeTriple (Branch.triple a b c) =
  Branch.triple (strictAntipode a) (strictAntipode b) (strictAntipode c)

strictAntipodeTripleInvolutive :
  (x : TritTriple) → strictAntipodeTriple (strictAntipodeTriple x) ≡ x
strictAntipodeTripleInvolutive (Branch.triple SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne) = refl
strictAntipodeTripleInvolutive (Branch.triple SSP.sspNegOne SSP.sspNegOne SSP.sspZero) = refl
strictAntipodeTripleInvolutive (Branch.triple SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne) = refl
strictAntipodeTripleInvolutive (Branch.triple SSP.sspNegOne SSP.sspZero SSP.sspNegOne) = refl
strictAntipodeTripleInvolutive (Branch.triple SSP.sspNegOne SSP.sspZero SSP.sspZero) = refl
strictAntipodeTripleInvolutive (Branch.triple SSP.sspNegOne SSP.sspZero SSP.sspPosOne) = refl
strictAntipodeTripleInvolutive (Branch.triple SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne) = refl
strictAntipodeTripleInvolutive (Branch.triple SSP.sspNegOne SSP.sspPosOne SSP.sspZero) = refl
strictAntipodeTripleInvolutive (Branch.triple SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne) = refl
strictAntipodeTripleInvolutive (Branch.triple SSP.sspZero SSP.sspNegOne SSP.sspNegOne) = refl
strictAntipodeTripleInvolutive (Branch.triple SSP.sspZero SSP.sspNegOne SSP.sspZero) = refl
strictAntipodeTripleInvolutive (Branch.triple SSP.sspZero SSP.sspNegOne SSP.sspPosOne) = refl
strictAntipodeTripleInvolutive (Branch.triple SSP.sspZero SSP.sspZero SSP.sspNegOne) = refl
strictAntipodeTripleInvolutive (Branch.triple SSP.sspZero SSP.sspZero SSP.sspZero) = refl
strictAntipodeTripleInvolutive (Branch.triple SSP.sspZero SSP.sspZero SSP.sspPosOne) = refl
strictAntipodeTripleInvolutive (Branch.triple SSP.sspZero SSP.sspPosOne SSP.sspNegOne) = refl
strictAntipodeTripleInvolutive (Branch.triple SSP.sspZero SSP.sspPosOne SSP.sspZero) = refl
strictAntipodeTripleInvolutive (Branch.triple SSP.sspZero SSP.sspPosOne SSP.sspPosOne) = refl
strictAntipodeTripleInvolutive (Branch.triple SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne) = refl
strictAntipodeTripleInvolutive (Branch.triple SSP.sspPosOne SSP.sspNegOne SSP.sspZero) = refl
strictAntipodeTripleInvolutive (Branch.triple SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne) = refl
strictAntipodeTripleInvolutive (Branch.triple SSP.sspPosOne SSP.sspZero SSP.sspNegOne) = refl
strictAntipodeTripleInvolutive (Branch.triple SSP.sspPosOne SSP.sspZero SSP.sspZero) = refl
strictAntipodeTripleInvolutive (Branch.triple SSP.sspPosOne SSP.sspZero SSP.sspPosOne) = refl
strictAntipodeTripleInvolutive (Branch.triple SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne) = refl
strictAntipodeTripleInvolutive (Branch.triple SSP.sspPosOne SSP.sspPosOne SSP.sspZero) = refl
strictAntipodeTripleInvolutive (Branch.triple SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne) = refl

------------------------------------------------------------------------
-- Exact orientation-forgotten quotient of one 27-state ternary cube.
-- Representatives are chosen by making the first nonzero coordinate positive.
-- Constructor cardinality is 1 + 3^2 + 3 + 1 = 14.
------------------------------------------------------------------------

data AntipodalClass27 : Set where
  centre27 : AntipodalClass27
  firstPositive27 : SSP.SSPTrit → SSP.SSPTrit → AntipodalClass27
  secondPositive27 : SSP.SSPTrit → AntipodalClass27
  thirdPositive27 : AntipodalClass27

classifyAntipodal27 : TritTriple → AntipodalClass27
classifyAntipodal27 (Branch.triple SSP.sspPosOne b c) = firstPositive27 b c
classifyAntipodal27 (Branch.triple SSP.sspNegOne b c) =
  firstPositive27 (strictAntipode b) (strictAntipode c)
classifyAntipodal27 (Branch.triple SSP.sspZero SSP.sspPosOne c) = secondPositive27 c
classifyAntipodal27 (Branch.triple SSP.sspZero SSP.sspNegOne c) =
  secondPositive27 (strictAntipode c)
classifyAntipodal27 (Branch.triple SSP.sspZero SSP.sspZero SSP.sspPosOne) = thirdPositive27
classifyAntipodal27 (Branch.triple SSP.sspZero SSP.sspZero SSP.sspNegOne) = thirdPositive27
classifyAntipodal27 (Branch.triple SSP.sspZero SSP.sspZero SSP.sspZero) = centre27

classifyAntipodal27Invariant :
  (x : TritTriple) →
  classifyAntipodal27 (strictAntipodeTriple x) ≡ classifyAntipodal27 x
classifyAntipodal27Invariant (Branch.triple SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne) = refl
classifyAntipodal27Invariant (Branch.triple SSP.sspPosOne SSP.sspNegOne SSP.sspZero) = refl
classifyAntipodal27Invariant (Branch.triple SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne) = refl
classifyAntipodal27Invariant (Branch.triple SSP.sspPosOne SSP.sspZero SSP.sspNegOne) = refl
classifyAntipodal27Invariant (Branch.triple SSP.sspPosOne SSP.sspZero SSP.sspZero) = refl
classifyAntipodal27Invariant (Branch.triple SSP.sspPosOne SSP.sspZero SSP.sspPosOne) = refl
classifyAntipodal27Invariant (Branch.triple SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne) = refl
classifyAntipodal27Invariant (Branch.triple SSP.sspPosOne SSP.sspPosOne SSP.sspZero) = refl
classifyAntipodal27Invariant (Branch.triple SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne) = refl
classifyAntipodal27Invariant (Branch.triple SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne) = refl
classifyAntipodal27Invariant (Branch.triple SSP.sspNegOne SSP.sspNegOne SSP.sspZero) = refl
classifyAntipodal27Invariant (Branch.triple SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne) = refl
classifyAntipodal27Invariant (Branch.triple SSP.sspNegOne SSP.sspZero SSP.sspNegOne) = refl
classifyAntipodal27Invariant (Branch.triple SSP.sspNegOne SSP.sspZero SSP.sspZero) = refl
classifyAntipodal27Invariant (Branch.triple SSP.sspNegOne SSP.sspZero SSP.sspPosOne) = refl
classifyAntipodal27Invariant (Branch.triple SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne) = refl
classifyAntipodal27Invariant (Branch.triple SSP.sspNegOne SSP.sspPosOne SSP.sspZero) = refl
classifyAntipodal27Invariant (Branch.triple SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne) = refl
classifyAntipodal27Invariant (Branch.triple SSP.sspZero SSP.sspPosOne SSP.sspNegOne) = refl
classifyAntipodal27Invariant (Branch.triple SSP.sspZero SSP.sspPosOne SSP.sspZero) = refl
classifyAntipodal27Invariant (Branch.triple SSP.sspZero SSP.sspPosOne SSP.sspPosOne) = refl
classifyAntipodal27Invariant (Branch.triple SSP.sspZero SSP.sspNegOne SSP.sspNegOne) = refl
classifyAntipodal27Invariant (Branch.triple SSP.sspZero SSP.sspNegOne SSP.sspZero) = refl
classifyAntipodal27Invariant (Branch.triple SSP.sspZero SSP.sspNegOne SSP.sspPosOne) = refl
classifyAntipodal27Invariant (Branch.triple SSP.sspZero SSP.sspZero SSP.sspPosOne) = refl
classifyAntipodal27Invariant (Branch.triple SSP.sspZero SSP.sspZero SSP.sspNegOne) = refl
classifyAntipodal27Invariant (Branch.triple SSP.sspZero SSP.sspZero SSP.sspZero) = refl

antipodalClass27Count : Nat
antipodalClass27Count = 1 + 9 + 3 + 1

antipodalClass27CountIsFourteen : antipodalClass27Count ≡ 14
antipodalClass27CountIsFourteen = refl

ternaryCubeCountDecomposesAsCentrePlusThirteenPairs :
  27 ≡ 1 + 13 * 2
ternaryCubeCountDecomposesAsCentrePlusThirteenPairs = refl

------------------------------------------------------------------------
-- Exact 9 -> 5 antipodal quotient on two ternary coordinates.
------------------------------------------------------------------------

data AntipodalClass9 : Set where
  centre9 firstAxis9 secondAxis9 sameSignDiagonal9 oppositeSignDiagonal9 :
    AntipodalClass9

classifyAntipodal9 : SSP.SSPTrit → SSP.SSPTrit → AntipodalClass9
classifyAntipodal9 SSP.sspZero SSP.sspZero = centre9
classifyAntipodal9 SSP.sspPosOne SSP.sspZero = firstAxis9
classifyAntipodal9 SSP.sspNegOne SSP.sspZero = firstAxis9
classifyAntipodal9 SSP.sspZero SSP.sspPosOne = secondAxis9
classifyAntipodal9 SSP.sspZero SSP.sspNegOne = secondAxis9
classifyAntipodal9 SSP.sspPosOne SSP.sspPosOne = sameSignDiagonal9
classifyAntipodal9 SSP.sspNegOne SSP.sspNegOne = sameSignDiagonal9
classifyAntipodal9 SSP.sspPosOne SSP.sspNegOne = oppositeSignDiagonal9
classifyAntipodal9 SSP.sspNegOne SSP.sspPosOne = oppositeSignDiagonal9

antipodal9Invariant :
  (a b : SSP.SSPTrit) →
  classifyAntipodal9 (strictAntipode a) (strictAntipode b)
  ≡ classifyAntipodal9 a b
antipodal9Invariant SSP.sspNegOne SSP.sspNegOne = refl
antipodal9Invariant SSP.sspNegOne SSP.sspZero = refl
antipodal9Invariant SSP.sspNegOne SSP.sspPosOne = refl
antipodal9Invariant SSP.sspZero SSP.sspNegOne = refl
antipodal9Invariant SSP.sspZero SSP.sspZero = refl
antipodal9Invariant SSP.sspZero SSP.sspPosOne = refl
antipodal9Invariant SSP.sspPosOne SSP.sspNegOne = refl
antipodal9Invariant SSP.sspPosOne SSP.sspZero = refl
antipodal9Invariant SSP.sspPosOne SSP.sspPosOne = refl

antipodalClass9Count : Nat
antipodalClass9Count = 5

antipodalClass9CountIsFive : antipodalClass9Count ≡ 5
antipodalClass9CountIsFive = refl

nineDecomposesAsCentrePlusFourPairs : 9 ≡ 1 + 4 * 2
nineDecomposesAsCentrePlusFourPairs = refl

------------------------------------------------------------------------
-- Boundary: the orbit geometry does not identify its C2 with another
-- two-element semantic carrier.
------------------------------------------------------------------------

record BalancedTernaryAntipodalBoundary : Set where
  field
    zeroIsOppositePole : Bool
    antipodalC2IsBooleanTruth : Bool
    antipodalC2IsDecisionAcceptReject : Bool
    contextualCounterpositionAutomaticallyStrictAntipode : Bool

open import Agda.Builtin.Bool using (Bool; false)

canonicalBalancedTernaryAntipodalBoundary : BalancedTernaryAntipodalBoundary
canonicalBalancedTernaryAntipodalBoundary = record
  { zeroIsOppositePole = false
  ; antipodalC2IsBooleanTruth = false
  ; antipodalC2IsDecisionAcceptReject = false
  ; contextualCounterpositionAutomaticallyStrictAntipode = false
  }
