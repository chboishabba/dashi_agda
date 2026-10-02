module DASHI.Moonshine.OggSSP2BM24DuadPair24AuthorityExact where

------------------------------------------------------------------------
-- M24 DEGREE-276 ACTION = DUAD / TWO-SUBSET ACTION AUTHORITY
--
-- External source authorities:
--
-- 1. GAP Character Table Library worked example for M24:
--    constructs comb = Combinations([1..24],2), acts with M24 by OnSets,
--    obtains degree 276 and a transitive action.
--
-- 2. ATLAS subgroup program M24G1-max2W1:
--    identifies the index-276 maximal subgroup M22:2 explicitly as the
--    "duad stabiliser".
--
-- Therefore the ATLAS degree-276 permutation carrier is not merely another
-- object of cardinality 276: it is the natural action on unordered two-subsets
-- of the 24-point M24 set.
--
-- This pays the finite carrier seam
--
--   ATLAS M24 p276  <->  Pair24 / duads.
--
-- It does NOT pay the independent source weld
--
--   Carnahan--Urano 2B Tate Hhat0_2(V^natural_2)  <->  M24 duad module.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Moonshine.OggSSP2BM24P276Completion10FrontierExact as Frontier

------------------------------------------------------------------------
-- 1. Exact duad cardinal arithmetic.
------------------------------------------------------------------------

m24PointCount : Nat
m24PointCount = 24

orderedDistinctPairCount : Nat
orderedDistinctPairCount = 24 * 23

duadCount : Nat
duadCount = 276

orderedDistinctPairsAreTwiceDuads :
  orderedDistinctPairCount ≡ 2 * duadCount
orderedDistinctPairsAreTwiceDuads = refl

duadCountIs276 : duadCount ≡ 276
duadCountIs276 = refl

atlasP276DegreeMatchesDuads :
  Frontier.degree Frontier.canonicalAtlasM24P276Receipt ≡ duadCount
atlasP276DegreeMatchesDuads = refl

------------------------------------------------------------------------
-- 2. External source receipt.
------------------------------------------------------------------------

record M24DuadActionAuthority : Set where
  constructor m24-duad-action-authority
  field
    ctblLibExampleURL : String
    atlasPermutationURL : String
    atlasDuadStabilizerURL : String

    sourcePointCount : Nat
    sourceTwoSubsetCount : Nat
    atlasPermutationDegree : Nat
    pointStabilizerName : String
    subgroupDescription : String

    ctblLibConstructsTwoSetAction : Bool
    ctblLibActionTransitive : Bool
    atlasPointStabilizerIsM22d2 : Bool
    atlasCallsSubgroupDuadStabiliser : Bool

    carrierSameObjectPaid : Bool
    carnahanUranoTateSameObjectPaid : Bool

open M24DuadActionAuthority public

canonicalM24DuadActionAuthority : M24DuadActionAuthority
canonicalM24DuadActionAuthority =
  m24-duad-action-authority
    "https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/doc2/chap8_mj.html"
    "https://brauer.maths.qmul.ac.uk/Atlas/v3/permrep/M24G1-p276B0"
    "https://brauer.maths.qmul.ac.uk/Atlas/v3/subgroup/M24G1-max2W1"
    24
    276
    276
    "M22:2"
    "duad stabiliser"
    true
    true
    true
    true
    true
    false

carrierSameObjectPaidIsTrue :
  carrierSameObjectPaid canonicalM24DuadActionAuthority ≡ true
carrierSameObjectPaidIsTrue = refl

tateSameObjectPaidIsFalse :
  carnahanUranoTateSameObjectPaid canonicalM24DuadActionAuthority ≡ false
tateSameObjectPaidIsFalse = refl

------------------------------------------------------------------------
-- 3. Promotion firewall.
------------------------------------------------------------------------

data M24DuadAuthorityCreatesTwoBTateIdentification : Set where

m24DuadAuthorityDoesNotCreateTwoBTateIdentification :
  M24DuadAuthorityCreatesTwoBTateIdentification → ⊥
m24DuadAuthorityDoesNotCreateTwoBTateIdentification ()

record GateCSplit : Set where
  constructor gate-c-split
  field
    c1AtlasP276EqualsDuadCarrier : Bool
    c2TwoBTateEqualsM24DuadModule : Bool
    downstreamM22RestrictionScreenAvailable : Bool
    downstreamCompletion10ObserverAvailable : Bool

canonicalGateCSplit : GateCSplit
canonicalGateCSplit =
  gate-c-split
    true
    false
    true
    true
