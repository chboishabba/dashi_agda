module DASHI.Biology.IIT369MatchedAlgebraControlExact where

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Foundations.Base369FiniteRingLaws as Ring369
import DASHI.Foundations.HexTruthS3CarrierBridgeExact as HexS3
import DASHI.Foundations.TernaryPermutationS3LawsExact as S3
import DASHI.Foundations.TernaryEndomorphismPhaseQuotientExact as Phase
import DASHI.Foundations.PhaseQuotientNonaryGroupSeparationExact as Separation
import DASHI.Biology.IIT4FiniteExecutableKernelExact as Kernel

------------------------------------------------------------------------
-- 369 MATCHED-ALGEBRA CONTROLS
--
-- 369 is not represented here merely as cardinalities 3^n.  In particular
-- the six-state lane is first-class:
--
--   HexTruth / hexXor   ~ cyclic Z/6Z-like addition,
--   TriPermutation / S3 ~ noncommutative permutation composition.
--
-- The repository already supplies an exact carrier chart between those six
-- states and proves that it cannot preserve both products.  Likewise, the
-- nine-state Q9 = C3 x C3 and NonaryTruth = C9 carriers are explicitly
-- chart-equivalent but not group-isomorphic.
--
-- Numerical matched-fabric IIT receipts are deliberately separate from these
-- algebraic theorems.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Six-state carrier chart and product separation.
------------------------------------------------------------------------

hexCarrierRoundTrip :
  (hex : Base.HexTruth) →
  HexS3.permutationToHex (HexS3.hexToPermutation hex) ≡ hex
hexCarrierRoundTrip = HexS3.hexRoundTrip

hexCarrierChartCannotPreserveBothProducts :
  ((left right : Base.HexTruth) →
    HexS3.hexToPermutation (Base.hexXor left right)
    ≡ S3._∙_ (HexS3.hexToPermutation left) (HexS3.hexToPermutation right)) →
  ⊥
hexCarrierChartCannotPreserveBothProducts =
  HexS3.hexCarrierChartCannotPreserveBothProducts

hexRingReceipt : Ring369.RingAuthoritySlot
hexRingReceipt = Ring369.hexTruthRingAuthoritySlot

hexHasZeroDivisors :
  Ring369.ZeroDivisorWitness
    Base.HexTruth
    Base.hex-0
    Ring369.hexTruthMul
hexHasZeroDivisors = Ring369.hexZeroDivisorWitness

------------------------------------------------------------------------
-- 2. Nine-state carrier chart and group separation.
------------------------------------------------------------------------

sameCarrierChart :
  (pair : Phase.PhaseQuotient9) →
  Separation.nonaryToPhasePair (Separation.phasePairToNonary pair) ≡ pair
sameCarrierChart = Separation.phaseNonaryRoundTrip

sameCardinalityStillNotGroupIsomorphic :
  Separation.Q9NonaryGroupIsomorphism → ⊥
sameCardinalityStillNotGroupIsomorphic =
  Separation.q9NonaryGroupIsomorphismImpossible

naturalCarrierChartDoesNotPreserveAddition :
  Separation.phasePairToNonary
    (Separation.q9Add
      (Base.tri-low , Base.tri-mid)
      (Base.tri-low , Base.tri-high))
  ≡
  Base.nonaryXor
    (Separation.phasePairToNonary (Base.tri-low , Base.tri-mid))
    (Separation.phasePairToNonary (Base.tri-low , Base.tri-high))
  → ⊥
naturalCarrierChartDoesNotPreserveAddition =
  Separation.naturalChartDoesNotPreserveAddition

------------------------------------------------------------------------
-- 3. Numerical matched-fabric receipt metadata.
------------------------------------------------------------------------

record AlgebraControlReceipt : Set where
  constructor algebraControlReceipt
  field
    sixStatesPerSystem : Nat
    z6IIT42023Profile : String
    s3IIT42023Profile : String
    nineStatesPerSystem : Nat
    z9IIT42023Profile : String
    f3SquaredIIT42023Profile : String
    iit42026DeterministicProfile : String
    sameSixState2023ProfileObserved : Bool
    sameNineState2023ProfileObserved : Bool
    formalSixStateProductSeparationOwned : Bool
    formalNineStateNonisomorphismOwned : Bool
    scanner : String

open AlgebraControlReceipt public

currentAlgebraControlReceipt : AlgebraControlReceipt
currentAlgebraControlReceipt =
  algebraControlReceipt
    36
    "phi_s=log2(36) on all 36 states"
    "phi_s=log2(36) on all 36 states"
    81
    "phi_s=log2(81) on all 81 states"
    "phi_s=log2(81) on all 81 states"
    "phi_s=0 on all deterministic states under IIT_4_0_2026"
    true true true true
    "scripts/iit_369_algebra_scan.py"

------------------------------------------------------------------------
-- 4. Interpretation / authority boundary.
------------------------------------------------------------------------

record IIT369AlgebraControlBoundary : Set where
  constructor iit369AlgebraControlBoundary
  field
    sixStateCarrierChartExists : Bool
    hexXorEqualsS3ProductByDefinition : Bool
    nineStateCarrierChartExists : Bool
    q9AndC9GroupLawsAreIsomorphic : Bool
    matchedFabricHeldFixed : Bool
    matchedSixState2023SystemPhiProfileObserved : Bool
    matchedNineState2023SystemPhiProfileObserved : Bool
    sameSystemPhiProfileIdentifiesSixStateGroupLaw : Bool
    sameSystemPhiProfileIdentifiesNineStateGroupLaw : Bool
    sameCardinalityIdentifiesGroupLaw : Bool
    numericalReceiptIsKernelProof : Bool

open IIT369AlgebraControlBoundary public

canonicalIIT369AlgebraControlBoundary : IIT369AlgebraControlBoundary
canonicalIIT369AlgebraControlBoundary =
  iit369AlgebraControlBoundary
    true false
    true false
    true true true
    false false false false

hexAndS3RemainDifferentProducts :
  hexXorEqualsS3ProductByDefinition
    canonicalIIT369AlgebraControlBoundary ≡ false
hexAndS3RemainDifferentProducts = refl

sixStatePhiProfileDoesNotIdentifyAlgebra :
  sameSystemPhiProfileIdentifiesSixStateGroupLaw
    canonicalIIT369AlgebraControlBoundary ≡ false
sixStatePhiProfileDoesNotIdentifyAlgebra = refl

nineStatePhiProfileDoesNotIdentifyAlgebra :
  sameSystemPhiProfileIdentifiesNineStateGroupLaw
    canonicalIIT369AlgebraControlBoundary ≡ false
nineStatePhiProfileDoesNotIdentifyAlgebra = refl

cardinalityDoesNotIdentifyAlgebra :
  sameCardinalityIdentifiesGroupLaw
    canonicalIIT369AlgebraControlBoundary ≡ false
cardinalityDoesNotIdentifyAlgebra = refl

versionBoundary : Kernel.IIT4ExecutableKernelBoundary
versionBoundary = Kernel.canonicalIIT4ExecutableKernelBoundary
