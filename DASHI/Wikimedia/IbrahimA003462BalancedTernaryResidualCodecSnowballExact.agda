module DASHI.Wikimedia.IbrahimA003462BalancedTernaryResidualCodecSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Codec.TriadicMaskSignFactorization as Codec
import DASHI.Wikimedia.IbrahimTernaryGeometricPartialSumRegularisationOEISSnowballExact as Geo

------------------------------------------------------------------------
-- A003462 HAS A SECOND TYPED ROLE RELEVANT TO DASHI:
--
--   a(n) = (3^n - 1)/2
--
-- is both
--   (a) the finite partial sum 1+3+...+3^(n-1), and
--   (b) the largest magnitude representable by n balanced ternary trits.
--
-- DASHI's residual codec already uses canonical trits {-1,0,+1} plane-wise.
-- This owner joins the finite bound to that carrier while keeping integer
-- reconstruction/uniqueness separate because the codec tranche has not yet
-- proved full balanced-ternary integer reconstruction.
------------------------------------------------------------------------

balancedTernaryMaxMagnitude : Nat → Nat
balancedTernaryMaxMagnitude = Geo.partialSum3

oneTritMax : balancedTernaryMaxMagnitude 1 ≡ 1
oneTritMax = refl

twoTritMax : balancedTernaryMaxMagnitude 2 ≡ 4
twoTritMax = refl

threeTritMax : balancedTernaryMaxMagnitude 3 ≡ 13
threeTritMax = refl

sixTritMax : balancedTernaryMaxMagnitude 6 ≡ 364
sixTritMax = refl

nineTritMax : balancedTernaryMaxMagnitude 9 ≡ 9841
nineTritMax = refl

codecThreeTritStateCount : Codec.maskSignStateCount ≡ 27
codecThreeTritStateCount = Codec.maskSignStateCount-is-27

record A003462ResidualCodecCoordinates : Set where
  constructor a003462-residual-codec-coordinates
  field
    partialSumOEIS : String
    powersOfThreeOEIS : String
    balancedTernaryQid : String
    ternaryNumeralSystemQid : String
    a003462FiniteBoundRolePaid : Bool
    codecUsesCanonicalSignedTritCarrier : Bool
    integerReconstructionUniquenessPaidHere : Bool
    oeisCreatesCodecOptimalityClaim : Bool
open A003462ResidualCodecCoordinates public

canonicalA003462ResidualCodecCoordinates : A003462ResidualCodecCoordinates
canonicalA003462ResidualCodecCoordinates = a003462-residual-codec-coordinates
  "A003462" "A000244" "Q2346165" "Q1056486"
  true true false false

data SameA003462RoleIdentifiesPartialSumAndResidualSemantics : Set where
data BalancedTernaryBoundCreatesCodecOptimality : Set where
data ThreeTritTwentySevenStatesCreatesIntegerReconstruction : Set where

sameSequenceDoesNotCollapseRoles :
  SameA003462RoleIdentifiesPartialSumAndResidualSemantics → ⊥
sameSequenceDoesNotCollapseRoles ()

boundDoesNotCreateOptimality : BalancedTernaryBoundCreatesCodecOptimality → ⊥
boundDoesNotCreateOptimality ()

stateCountDoesNotCreateIntegerReconstruction :
  ThreeTritTwentySevenStatesCreatesIntegerReconstruction → ⊥
stateCountDoesNotCreateIntegerReconstruction ()

record A003462ResidualCodecFrontier : Set where
  constructor a003462-residual-codec-frontier
  field
    oneTwoThreeSixNineTritBoundsPaid : Bool
    a003462TypedRolePaid : Bool
    threeTritCodecStateCount27Paid : Bool
    fullBalancedTernaryIntegerReconstructionPaid : Bool
    representationUniquenessPaid : Bool
    nextResidual : String
open A003462ResidualCodecFrontier public

currentA003462ResidualCodecFrontier : A003462ResidualCodecFrontier
currentA003462ResidualCodecFrontier = a003462-residual-codec-frontier
  true true true false false
  "reuse the canonical Trit codec to formalise finite balanced-ternary reconstruction R=sum S_k 3^k and prove the exact reachable interval [-A003462(n), +A003462(n)] plus uniqueness for a declared finite convention. Keep that finite signed-digit theorem separate from the divergent-series continuation value -1/2."
