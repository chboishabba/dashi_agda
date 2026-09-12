module DASHI.Wikimedia.IbrahimJacquardBooleanMaskOEISSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Computation.JacquardOperationalSemanticsExact as Jacquard
import DASHI.Computation.JacquardHelicalWeaveBridgeExact as Helical
import DASHI.Wikimedia.Ibrahim36927PantsColourTextileSweetgrassSnowballExact as Cross
import DASHI.Wikimedia.WikipediaAllPairsPrunedMergeSnowballExact as AllPairs

------------------------------------------------------------------------
-- JACQUARD BOOLEAN LIFT MASK -> POWERS OF TWO OEIS SNOWBALL
--
-- Exact repo carrier:
--   LiftMask n = Fin n -> Bool
--
-- Mathematically, functions from an n-element finite set to Bool form a
-- 2^n-element function space.  The current Jacquard owner does not itself
-- expose a finite-cardinality enumeration/bijection theorem, so that same-
-- object cardinality payment remains OPEN here rather than being inferred from
-- the type shape.  OEIS A000079 is therefore retained as an external numeric
-- coordinate candidate for the eventual cardinality theorem.
------------------------------------------------------------------------

record OEISCoordinate : Set where
  constructor oeis-coordinate
  field
    oeisId : String
    sequenceReference : String
    candidateRelation : String
    sameObjectCardinalityPaid : Bool
    createsJacquardSemantics : Bool
open OEISCoordinate public

booleanMaskPowersOEIS : OEISCoordinate
booleanMaskPowersOEIS = oeis-coordinate
  "A000079"
  "powers of two 2^n"
  "candidate external sequence coordinate for the cardinality of LiftMask n = Fin n -> Bool"
  false false

record JacquardMaskCardinalityFrontier : Set where
  constructor jacquard-mask-cardinality-frontier
  field
    liftMaskIsFiniteIndexToBool : Bool
    threeWarpHelicalProgramExists : Bool
    threeWarpMaskExpectedCardinality : String
    explicitMaskEnumerationConstructed : Bool
    finiteBijectionToBinaryWordsConstructed : Bool
    cardinality2PowNLocallyProved : Bool
    a000079SameObjectPaid : Bool
    nextResidual : String
open JacquardMaskCardinalityFrontier public

currentJacquardMaskCardinalityFrontier : JacquardMaskCardinalityFrontier
currentJacquardMaskCardinalityFrontier = jacquard-mask-cardinality-frontier
  true true "2^3 = 8 for LiftMask 3"
  false false false false
  "construct/reuse a finite enumeration or bijection LiftMask n <-> n-bit words, then pay cardinality 2^n and only then promote A000079 from candidate numeric coordinate to exact same-object sequence identity"

record BinaryTernaryRoleBoundary : Set where
  constructor binary-ternary-role-boundary
  field
    jacquardMaskPowerBase : String
    base369RefinementPowerBase : String
    threeWarpCountCreatesTernaryMaskSpace : Bool
    sharedExponentCreatesSameSequence : Bool
    a000079EqualsA000244 : Bool
    bothRemainAllPairsComparable : Bool
open BinaryTernaryRoleBoundary public

canonicalBinaryTernaryRoleBoundary : BinaryTernaryRoleBoundary
canonicalBinaryTernaryRoleBoundary = binary-ternary-role-boundary
  "2" "3" false false false true

data TypeShapeCreatesCardinalityProof : Set where
data A000079CreatesJacquardProgramme : Set where
data ThreeWarpsCreateTwentySevenMasks : Set where
data BinaryPowerEqualsTernaryPower : Set where

typeShapeDoesNotPayCardinality : TypeShapeCreatesCardinalityProof → ⊥
typeShapeDoesNotPayCardinality ()

oeisDoesNotCreateProgramme : A000079CreatesJacquardProgramme → ⊥
oeisDoesNotCreateProgramme ()

threeWarpsDoNotCreate27Masks : ThreeWarpsCreateTwentySevenMasks → ⊥
threeWarpsDoNotCreate27Masks ()

binaryPowerIsNotTernaryPower : BinaryPowerEqualsTernaryPower → ⊥
binaryPowerIsNotTernaryPower ()

helicalBoundary : Helical.JacquardHelicalBridgeBoundary
helicalBoundary = Helical.canonicalJacquardHelicalBridgeBoundary

crossDomainBoundary : Cross.Ibrahim369ColourTextileBoundary
crossDomainBoundary = Cross.canonicalIbrahim369ColourTextileBoundary

allPairsBoundary : AllPairs.WikipediaAllPairsBoundary
allPairsBoundary = AllPairs.canonicalWikipediaAllPairsBoundary
