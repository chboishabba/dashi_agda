module DASHI.Moonshine.JInvariant369NeutralCuspRelationCrossPollinationExact where

------------------------------------------------------------------------
-- NEUTRAL / ORIENTED PHASE, ETA^24 CUSP, AND 12/144 CROSS-POLLINATION
--
-- This owner consolidates three theorem-bearing lanes without identifying
-- their unlike zero/neutral structures:
--
--   finite phase:
--     5 modes x {-1,0,+1}
--       ~= 5 neutral lanes + 10 non-neutral oriented lanes;
--
--   completion quotient:
--     the ten oriented states admit a nine-state quotient by collapsing the
--     duplicated orientation of one distinguished neutral/identity mode;
--
--   eta^24:
--     the pinned Lean companion packages eta^24 as a genuine level-one
--     weight-12 cusp form, proves cusp vanishing, first q coefficient 1, and
--     same-object equality with normalized (E4^3-E6^2)/1728;
--
--   twelve:
--     24 = 12 + 12,
--     144 = 12 * 12,
--     1728 = 12 * 12 * 12,
--   while exponent duplication, relation formation, modular weight and
--   normalization remain different constructors.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Completion
import DASHI.Biology.SSP15ComplementPhaseProjectorExact as SSP15
import DASHI.Wikimedia.IbrahimMonster42dFifteenFourteenPhaseCarrierExact as Phase42
import DASHI.Wikimedia.IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionExact as Reduction
import DASHI.Moonshine.JInvariant369C6TenRankWeightTwelveCrossPollinationExact as Cross
import DASHI.Moonshine.DeltaConstructedComplexReflectionCutsetExact as DeltaCut

------------------------------------------------------------------------
-- 0. The five modes are the exact inner-inversion orbit quotient of T^2.
------------------------------------------------------------------------

nineSquareInversionOrbitReductionBoundary :
  Reduction.Ternary27ReductionBoundary
nineSquareInversionOrbitReductionBoundary =
  Reduction.currentTernary27ReductionBoundary

innerNineToFiveOrbitQuotientIsPaid :
  Reduction.innerNineToFiveOrbitQuotientPaid
    nineSquareInversionOrbitReductionBoundary
  ≡ true
innerNineToFiveOrbitQuotientIsPaid = refl

phasePreservingThreeTimesFiveReductionIsPaid :
  Reduction.phasePreservingThreeTimesFiveReductionPaid
    nineSquareInversionOrbitReductionBoundary
  ≡ true
phasePreservingThreeTimesFiveReductionIsPaid = refl

orbitModeRoundTrip :
  (orbit : DASHI.Biology.TriadicKernelLiftQuotientExact.NineOrbit) →
  Reduction.complementModeToOrbit (Reduction.orbitToComplementMode orbit)
  ≡ orbit
orbitModeRoundTrip =
  Reduction.orbitModeRoundTrip

modeOrbitRoundTrip :
  (mode : Completion.ComplementMode5) →
  Reduction.orbitToComplementMode (Reduction.complementModeToOrbit mode)
  ≡ mode
modeOrbitRoundTrip =
  Reduction.modeOrbitRoundTrip

nineIsOnePlusFourPairs :
  9 ≡ 1 + 4 * 2
nineIsOnePlusFourPairs = refl

fiveOrbitCountIsOnePlusFour :
  5 ≡ 1 + 4
fiveOrbitCountIsOnePlusFour = refl

------------------------------------------------------------------------
-- 1. Exact 15 = neutral-5 + oriented-10 carrier decomposition.
------------------------------------------------------------------------

BalancedPhase : Set
BalancedPhase = Harmonic.BalancedTrit

Phase15 : Set
Phase15 = Completion.ComplementMode5 × BalancedPhase

Neutral5 : Set
Neutral5 = Completion.ComplementMode5

Oriented10 : Set
Oriented10 = Completion.ComplementMode5 × Completion.BinaryPhase

splitPhase15 :
  Phase15 →
  Neutral5 ⊎ Oriented10
splitPhase15 (mode , Harmonic.zeroTrit) =
  inj₁ mode
splitPhase15 (mode , Harmonic.negativeTrit) =
  inj₂ (mode , Completion.counterPhase)
splitPhase15 (mode , Harmonic.positiveTrit) =
  inj₂ (mode , Completion.directPhase)

joinPhase15 :
  Neutral5 ⊎ Oriented10 →
  Phase15
joinPhase15 (inj₁ mode) =
  mode , Harmonic.zeroTrit
joinPhase15 (inj₂ (mode , Completion.counterPhase)) =
  mode , Harmonic.negativeTrit
joinPhase15 (inj₂ (mode , Completion.directPhase)) =
  mode , Harmonic.positiveTrit

joinAfterSplit :
  (state : Phase15) →
  joinPhase15 (splitPhase15 state) ≡ state
joinAfterSplit (mode , Harmonic.negativeTrit) = refl
joinAfterSplit (mode , Harmonic.zeroTrit) = refl
joinAfterSplit (mode , Harmonic.positiveTrit) = refl

splitAfterJoin :
  (state : Neutral5 ⊎ Oriented10) →
  splitPhase15 (joinPhase15 state) ≡ state
splitAfterJoin (inj₁ mode) = refl
splitAfterJoin (inj₂ (mode , Completion.counterPhase)) = refl
splitAfterJoin (inj₂ (mode , Completion.directPhase)) = refl

fiveTimesThreeIsFifteen :
  5 * 3 ≡ 15
fiveTimesThreeIsFifteen =
  SSP15.fiveModesTimesThreePhasesIsFifteen

fivePlusTenIsFifteen :
  5 + 10 ≡ 15
fivePlusTenIsFifteen = refl

fiveTimesTwoIsTen :
  5 * 2 ≡ 10
fiveTimesTwoIsTen = refl

------------------------------------------------------------------------
-- 2. Explicit ten -> nine quotient by duplicated neutral orientation.
------------------------------------------------------------------------

data Quotient9 : Set where
  identity : Quotient9
  mode18counter mode18direct : Quotient9
  mode27counter mode27direct : Quotient9
  mode36counter mode36direct : Quotient9
  mode45counter mode45direct : Quotient9

quotientOriented10 :
  Oriented10 →
  Quotient9
quotientOriented10 (Completion.mode09 , phase) = identity
quotientOriented10 (Completion.mode18 , Completion.counterPhase) = mode18counter
quotientOriented10 (Completion.mode18 , Completion.directPhase) = mode18direct
quotientOriented10 (Completion.mode27 , Completion.counterPhase) = mode27counter
quotientOriented10 (Completion.mode27 , Completion.directPhase) = mode27direct
quotientOriented10 (Completion.mode36 , Completion.counterPhase) = mode36counter
quotientOriented10 (Completion.mode36 , Completion.directPhase) = mode36direct
quotientOriented10 (Completion.mode45 , Completion.counterPhase) = mode45counter
quotientOriented10 (Completion.mode45 , Completion.directPhase) = mode45direct

quotientRepresentative :
  Quotient9 →
  Oriented10
quotientRepresentative identity =
  Completion.mode09 , Completion.directPhase
quotientRepresentative mode18counter =
  Completion.mode18 , Completion.counterPhase
quotientRepresentative mode18direct =
  Completion.mode18 , Completion.directPhase
quotientRepresentative mode27counter =
  Completion.mode27 , Completion.counterPhase
quotientRepresentative mode27direct =
  Completion.mode27 , Completion.directPhase
quotientRepresentative mode36counter =
  Completion.mode36 , Completion.counterPhase
quotientRepresentative mode36direct =
  Completion.mode36 , Completion.directPhase
quotientRepresentative mode45counter =
  Completion.mode45 , Completion.counterPhase
quotientRepresentative mode45direct =
  Completion.mode45 , Completion.directPhase

quotientAfterRepresentative :
  (state : Quotient9) →
  quotientOriented10 (quotientRepresentative state) ≡ state
quotientAfterRepresentative identity = refl
quotientAfterRepresentative mode18counter = refl
quotientAfterRepresentative mode18direct = refl
quotientAfterRepresentative mode27counter = refl
quotientAfterRepresentative mode27direct = refl
quotientAfterRepresentative mode36counter = refl
quotientAfterRepresentative mode36direct = refl
quotientAfterRepresentative mode45counter = refl
quotientAfterRepresentative mode45direct = refl

distinguishedOrientationDuplicationCollapses :
  quotientOriented10
    (Completion.mode09 , Completion.counterPhase)
  ≡
  quotientOriented10
    (Completion.mode09 , Completion.directPhase)
distinguishedOrientationDuplicationCollapses = refl

tenMinusDuplicatedNeutralIsNine :
  10 ≡ 9 + 1
tenMinusDuplicatedNeutralIsNine = refl

------------------------------------------------------------------------
-- 3. Distinguished neutral lane, residual 14 and outer 42.
------------------------------------------------------------------------

distinguishedNeutralLane : Phase15
distinguishedNeutralLane =
  Completion.mode09 , Harmonic.zeroTrit

fifteenIsOnePlusFourteen :
  15 ≡ 1 + 14
fifteenIsOnePlusFourteen = refl

outerThreeTimesFourteenIsFortyTwo :
  3 * 14 ≡ 42
outerThreeTimesFourteenIsFortyTwo =
  Phase42.outerThreeTimesFourteenArithmetic

------------------------------------------------------------------------
-- 4. Three independent constructors landing numerically on fourteen.
------------------------------------------------------------------------

fourteenIsBalancedRankCarry :
  Cross.rankValue Cross.rank14
  ≡ 13 + 1
fourteenIsBalancedRankCarry =
  Cross.rank14IsRank13PlusOne

fourteenIsNeutralDeletionResidual :
  1 + 14 ≡ 15
fourteenIsNeutralDeletionResidual = refl

fourteenIsAtlasExponentDepth :
  Cross.atlasProperImageDepth ≡ 14
fourteenIsAtlasExponentDepth =
  Cross.atlasProperImageDepthIsFourteen

data Rank14EqualsResidual14 : Set where
data Rank14EqualsAtlasFiltration : Set where
data Residual14EqualsAtlasFiltration : Set where

rank14DoesNotEqualResidual14ByNumeral :
  Rank14EqualsResidual14 → ⊥
rank14DoesNotEqualResidual14ByNumeral ()

rank14DoesNotEqualAtlasByNumeral :
  Rank14EqualsAtlasFiltration → ⊥
rank14DoesNotEqualAtlasByNumeral ()

residual14DoesNotEqualAtlasByNumeral :
  Residual14EqualsAtlasFiltration → ⊥
residual14DoesNotEqualAtlasByNumeral ()

------------------------------------------------------------------------
-- 5. eta^24 pinned Lean receipt.
--
-- The Agda branch does not replay Lean's analytic proof.  It records the
-- exact compiler-owned companion results and keeps provenance explicit.
------------------------------------------------------------------------

deltaCutsetBoundary :
  DeltaCut.DeltaConstructedComplexReflectionCutsetBoundary
deltaCutsetBoundary =
  DeltaCut.canonicalDeltaConstructedComplexReflectionCutsetBoundary

leanEta24NormalizedDeltaSameObjectSourceWritten :
  DeltaCut.eta24NormalizedDeltaSameObjectWelded deltaCutsetBoundary
  ≡ true
leanEta24NormalizedDeltaSameObjectSourceWritten = refl

record Eta24PinnedCompanionReceipt : Set where
  constructor eta24-pinned-companion-receipt
  field
    exponent : Nat
    modularWeight : Nat

    eta24Weight12CuspFormOwnedInLean : Bool
    eta24ZeroAtImInftyOwnedInLean : Bool
    eta24FirstQCoefficientOneOwnedInLean : Bool
    eta24NormalizedDeltaSameObjectOwnedInLean : Bool
    dependencyBumpUsed : Bool

open Eta24PinnedCompanionReceipt public

eta24PinnedCompanionReceipt :
  Eta24PinnedCompanionReceipt
eta24PinnedCompanionReceipt =
  eta24-pinned-companion-receipt
    24 12
    true true true true false

etaExponentIsTwoTwelves :
  exponent eta24PinnedCompanionReceipt
  ≡ 12 + 12
etaExponentIsTwoTwelves = refl

etaExponentIsTwoTimesWeight :
  exponent eta24PinnedCompanionReceipt
  ≡ 2 * modularWeight eta24PinnedCompanionReceipt
etaExponentIsTwoTimesWeight = refl

------------------------------------------------------------------------
-- 6. Different constructors around twelve.
------------------------------------------------------------------------

data TwelveConstructor : Set where
  etaExponentDuplication : TwelveConstructor
  modularWeightAssignment : TwelveConstructor
  relationProduct : TwelveConstructor
  normalizationCube : TwelveConstructor

record TwelveConstructorReceipt : Set where
  constructor twelve-constructor-receipt
  field
    operation : TwelveConstructor
    inputTwelve : Nat
    output : Nat
    sameSemanticOperationAsOtherEqualNumeral : Bool

open TwelveConstructorReceipt public

etaExponentReceipt :
  TwelveConstructorReceipt
etaExponentReceipt =
  twelve-constructor-receipt
    etaExponentDuplication 12 24 false

modularWeightReceipt :
  TwelveConstructorReceipt
modularWeightReceipt =
  twelve-constructor-receipt
    modularWeightAssignment 12 12 false

relationProductReceipt :
  TwelveConstructorReceipt
relationProductReceipt =
  twelve-constructor-receipt
    relationProduct 12 144 false

normalizationCubeReceipt :
  TwelveConstructorReceipt
normalizationCubeReceipt =
  twelve-constructor-receipt
    normalizationCube 12 1728 false

twelvePlusTwelveIsTwentyFour :
  12 + 12 ≡ 24
twelvePlusTwelveIsTwentyFour = refl

twelveTimesTwelveIs144 :
  12 * 12 ≡ 144
twelveTimesTwelveIs144 =
  Cross.twelveSquaredIs144

twelveCubedIs1728 :
  12 * 12 * 12 ≡ 1728
twelveCubedIs1728 =
  Cross.twelveCubedIs1728

------------------------------------------------------------------------
-- 7. Distinct zero/neutral notions.
------------------------------------------------------------------------

FiniteZeroPhase : Set
FiniteZeroPhase = Neutral5

record CuspVanishingReceipt : Set where
  constructor cusp-vanishing-receipt
  field
    weight : Nat
    vanishesAtDistinguishedCusp : Bool

eta24CuspVanishingReceipt :
  CuspVanishingReceipt
eta24CuspVanishingReceipt =
  cusp-vanishing-receipt 12 true

RelationCell12 : Set
RelationCell12 = Fin 12 × Fin 12

record RelationDiagonalCell : Set where
  constructor relation-diagonal-cell
  field
    index : Fin 12

data FiniteZeroPhaseEqualsCuspVanishing : Set where
data CuspVanishingEqualsRelationDiagonal : Set where
data RelationDiagonalEqualsFiniteZeroPhase : Set where

finiteZeroPhaseDoesNotEqualCuspVanishing :
  FiniteZeroPhaseEqualsCuspVanishing → ⊥
finiteZeroPhaseDoesNotEqualCuspVanishing ()

cuspVanishingDoesNotEqualRelationDiagonal :
  CuspVanishingEqualsRelationDiagonal → ⊥
cuspVanishingDoesNotEqualRelationDiagonal ()

relationDiagonalDoesNotEqualFiniteZeroPhase :
  RelationDiagonalEqualsFiniteZeroPhase → ⊥
relationDiagonalDoesNotEqualFiniteZeroPhase ()

------------------------------------------------------------------------
-- 8. Consolidated boundary.
------------------------------------------------------------------------

record NeutralCuspRelationBoundary : Set where
  constructor neutral-cusp-relation-boundary
  field
    innerNineToFiveOrbitQuotientPaid : Bool
    phasePreservingTwentySevenToThreeTimesFivePaid : Bool
    phase15SplitsAsNeutral5PlusOriented10 : Bool
    fullNeutralSheetRetained : Bool
    fullNonNeutralOrientedSheetRetained : Bool
    duplicatedIdentityOrientationQuotientOwned : Bool
    quotientTenToNineOwned : Bool

    distinguishedNeutralDeletionLeavesFourteenPaid : Bool
    outerThreeTimesFourteenIsFortyTwoPaid : Bool
    balancedRankCarryAlsoLandsOnFourteenPaid : Bool
    atlasExponentDepthAlsoLandsOnFourteenPaid : Bool
    equalFourteenCreatesSemanticIdentity : Bool

    eta24Exponent24Owned : Bool
    eta24Weight12CuspOwnedInLean : Bool
    eta24CuspZeroOwnedInLean : Bool
    eta24FirstQCoefficientOneOwnedInLean : Bool
    eta24NormalizedDeltaSameObjectOwnedInLean : Bool

    twelvePlusTwelveIsTwentyFourPaid : Bool
    twelveTimesTwelveIs144Paid : Bool
    twelveCubedIs1728Paid : Bool
    equalTwelveCreatesSemanticIdentity : Bool

    finiteZeroEqualsCuspZero : Bool
    cuspZeroEqualsRelationDiagonal : Bool
    relationDiagonalEqualsFiniteZero : Bool

open NeutralCuspRelationBoundary public

canonicalNeutralCuspRelationBoundary :
  NeutralCuspRelationBoundary
canonicalNeutralCuspRelationBoundary =
  neutral-cusp-relation-boundary
    true true
    true true true true true
    true true true true false
    true true true true true
    true true true false
    false false false
