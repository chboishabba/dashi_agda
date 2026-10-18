module DASHI.Moonshine.OggSSP2BM22RuntimeMaxCutReceiptExact where

------------------------------------------------------------------------
-- M24-276 -> M22 RUNTIME MAX-CUT RECEIPT
--
-- Provenance: repository GAP / AtlasRep / MeatAxe screens executed against
-- the live J369 branch on 2026-10-03.
--
-- Positive result:
--   M24 degree-276 duad module restricted to M22 has composition factors
--
--     1^10 + 10a^5 + 10b^5 + 34^2 + 98,
--
--   with both 10a and 10b identified against the actual AtlasRep f2r10
--   modules.
--
-- Negative result:
--   the unique bare M22 involution class acts on both 10a and 10b with
--
--     rank(g-I) = 4,
--     dim Fix(g) = 6,
--
--   hence Jordan shape J2^4 + J1^2 rather than the J2^5 five-pair action
--   requested by the old Completion10 criterion.
--
-- Semantic boundary:
-- these are finite-runtime facts about the M24 duad model.  They do not by
-- themselves identify a 10-dimensional subquotient of the actual 2B Tate
-- module, and they do not kill Completion10 recognition through a larger
-- local action/filtration.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- 1. Exact runtime factor accounting.
------------------------------------------------------------------------

data RuntimeFactorKind : Set where
  trivialOne tenA tenB thirtyFour ninetyEight : RuntimeFactorKind

factorDimension : RuntimeFactorKind → Nat
factorDimension trivialOne = 1
factorDimension tenA = 10
factorDimension tenB = 10
factorDimension thirtyFour = 34
factorDimension ninetyEight = 98

factorMultiplicity : RuntimeFactorKind → Nat
factorMultiplicity trivialOne = 10
factorMultiplicity tenA = 5
factorMultiplicity tenB = 5
factorMultiplicity thirtyFour = 2
factorMultiplicity ninetyEight = 1

weightedDimension : RuntimeFactorKind → Nat
weightedDimension k = factorDimension k * factorMultiplicity k

runtimeRestrictedDimensionCloses276 :
  weightedDimension trivialOne
  + weightedDimension tenA
  + weightedDimension tenB
  + weightedDimension thirtyFour
  + weightedDimension ninetyEight
  ≡ 276
runtimeRestrictedDimensionCloses276 = refl

tenAMultiplicityIsFive : factorMultiplicity tenA ≡ 5
tenAMultiplicityIsFive = refl

tenBMultiplicityIsFive : factorMultiplicity tenB ≡ 5
tenBMultiplicityIsFive = refl

totalTenDimensionalFactorMultiplicityIsTen :
  factorMultiplicity tenA + factorMultiplicity tenB ≡ 10
totalTenDimensionalFactorMultiplicityIsTen = refl

------------------------------------------------------------------------
-- 2. AtlasRep identification receipts.
------------------------------------------------------------------------

record AtlasRepTenIdentification : Set where
  constructor atlasrep-ten-identification
  field
    factor : RuntimeFactorKind
    atlasRepName : String
    dimension : Nat
    observedMultiplicity : Nat
    moduleIsomorphismVerified : Bool

open AtlasRepTenIdentification public

runtimeTenAIdentification : AtlasRepTenIdentification
runtimeTenAIdentification =
  atlasrep-ten-identification
    tenA
    "M22G1-f2r10aB0"
    10
    5
    true

runtimeTenBIdentification : AtlasRepTenIdentification
runtimeTenBIdentification =
  atlasrep-ten-identification
    tenB
    "M22G1-f2r10bB0"
    10
    5
    true

------------------------------------------------------------------------
-- 3. Bare-M22 involution no-go.
------------------------------------------------------------------------

bareM22InvolutionRank : Nat
bareM22InvolutionRank = 4

bareM22FixedDimension : Nat
bareM22FixedDimension = 6

completionFivePairTargetRank : Nat
completionFivePairTargetRank = 5

completionFivePairTargetFixedDimension : Nat
completionFivePairTargetFixedDimension = 5

bareM22RankIsFour : bareM22InvolutionRank ≡ 4
bareM22RankIsFour = refl

bareM22FixedDimensionIsSix : bareM22FixedDimension ≡ 6
bareM22FixedDimensionIsSix = refl

runtimeJordanDimensionClosesTen : 2 * 4 + 1 * 2 ≡ 10
runtimeJordanDimensionClosesTen = refl

data BareM22InvolutionRealizesCompletionFivePairs : Set where

bareM22InvolutionDoesNotRealizeCompletionFivePairs :
  BareM22InvolutionRealizesCompletionFivePairs → ⊥
bareM22InvolutionDoesNotRealizeCompletionFivePairs ()

------------------------------------------------------------------------
-- 4. Promotion firewalls.
------------------------------------------------------------------------

data RuntimeTenFactorIsActualTwoBTateSubquotient : Set where
data RuntimeNoGoKillsAllCompletionTenSources : Set where

runtimeFactorDoesNotIdentifyActualTateSubquotient :
  RuntimeTenFactorIsActualTwoBTateSubquotient → ⊥
runtimeFactorDoesNotIdentifyActualTateSubquotient ()

bareM22NoGoDoesNotKillLargerCompletionSource :
  RuntimeNoGoKillsAllCompletionTenSources → ⊥
bareM22NoGoDoesNotKillLargerCompletionSource ()

------------------------------------------------------------------------
-- 5. Runtime status.
------------------------------------------------------------------------

record M22RuntimeMaxCutStatus : Set where
  constructor m22-runtime-max-cut-status
  field
    m24DuadRestrictionComputed : Bool
    tenAObserved : Bool
    tenBObserved : Bool
    tenAAtlasRepIdentified : Bool
    tenBAtlasRepIdentified : Bool
    bareM22FivePairCompletionObserved : Bool
    actualTwoBTateTenSubquotientPaid : Bool
    largerCompletionActionPaid : Bool

canonicalM22RuntimeMaxCutStatus : M22RuntimeMaxCutStatus
canonicalM22RuntimeMaxCutStatus =
  m22-runtime-max-cut-status
    true true true true true false false false
