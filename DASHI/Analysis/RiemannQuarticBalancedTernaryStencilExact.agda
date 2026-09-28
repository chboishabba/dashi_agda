module DASHI.Analysis.RiemannQuarticBalancedTernaryStencilExact where

------------------------------------------------------------------------
-- RH QUARTIC KERNEL: 3-ADIC DEPTH + SPARSE BALANCED-TERNARY STENCIL
--
-- DASHI CONTRIBUTION
--
-- This file is arithmetic only.  It does not reprove the analytic RH identity.
-- It packages the primitive integer coefficient kernel
--
--   (80, 243, 1215, 972)
--
-- into:
--
--   * one mod-3 unit coefficient;
--   * three coefficients sharing an exact 3^5 factor;
--   * sparse signed ternary masks;
--   * the existing 196830 = 3^11 + 3^9 carrier identity.
--
-- The analytic theorem remains owned by the Lean RH lane.  Likewise, a sparse
-- signed-digit presentation is not promoted here to a geometric, Monster, or
-- representation-theoretic semantic identity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.MonsterFilteredCarrierExact as MonsterBulk

------------------------------------------------------------------------
-- 1. Canonical powers of three.
------------------------------------------------------------------------

pow3 : Nat → Nat
pow3 zero = 1
pow3 (suc n) = 3 * pow3 n

pow3FourIs81 : pow3 4 ≡ 81
pow3FourIs81 = refl

pow3FiveIs243 : pow3 5 ≡ 243
pow3FiveIs243 = refl

pow3SixIs729 : pow3 6 ≡ 729
pow3SixIs729 = refl

pow3SevenIs2187 : pow3 7 ≡ 2187
pow3SevenIs2187 = refl

pow3NineIs19683 : pow3 9 ≡ 19683
pow3NineIs19683 = refl

pow3ElevenIs177147 : pow3 11 ≡ 177147
pow3ElevenIs177147 = refl

------------------------------------------------------------------------
-- 2. Small coefficients in balanced-ternary additive normal form.
--
-- A subtraction a-b is represented here by the subtraction-free equality
-- a = target + b so the arithmetic remains definitional over Nat.
------------------------------------------------------------------------

fourIsThreePlusOne : 4 ≡ 3 + 1
fourIsThreePlusOne = refl

fiveBalancedTernary :
  pow3 2 ≡ 5 + 3 + 1
fiveBalancedTernary = refl

tenIsSparse101 :
  10 ≡ pow3 2 + 1
tenIsSparse101 = refl

twentyBalancedTernary :
  pow3 3 + 3 ≡ 20 + pow3 2 + 1
twentyBalancedTernary = refl

eightyIsPuncturedThreePowerFour :
  pow3 4 ≡ 80 + 1
eightyIsPuncturedThreePowerFour = refl

------------------------------------------------------------------------
-- 3. Primitive RH coefficient vector.
------------------------------------------------------------------------

poleCoefficient : Nat
poleCoefficient = 80

originCoefficient : Nat
originCoefficient = 243

jCoefficient : Nat
jCoefficient = 1215

targetCoefficient : Nat
targetCoefficient = 972

originIsThreePowerFive :
  originCoefficient ≡ pow3 5
originIsThreePowerFive = refl

jBalancedTernary :
  pow3 7 ≡ jCoefficient + pow3 6 + pow3 5
jBalancedTernary = refl

targetBalancedTernary :
  targetCoefficient ≡ pow3 6 + pow3 5
targetBalancedTernary = refl

poleBalancedTernary :
  pow3 4 ≡ poleCoefficient + 1
poleBalancedTernary = refl

------------------------------------------------------------------------
-- 4. Literal signed stencil at exponents 7,...,0.
------------------------------------------------------------------------

data SignedTrit : Set where
  minus : SignedTrit
  zeroTrit : SignedTrit
  plus : SignedTrit

record Stencil8 : Set where
  constructor stencil8
  field
    e7 e6 e5 e4 e3 e2 e1 e0 : SignedTrit

open Stencil8 public

poleStencil : Stencil8
poleStencil =
  stencil8
    zeroTrit zeroTrit zeroTrit plus
    zeroTrit zeroTrit zeroTrit minus

originStencil : Stencil8
originStencil =
  stencil8
    zeroTrit zeroTrit plus zeroTrit
    zeroTrit zeroTrit zeroTrit zeroTrit

jStencil : Stencil8
jStencil =
  stencil8
    plus minus minus zeroTrit
    zeroTrit zeroTrit zeroTrit zeroTrit

targetStencil : Stencil8
targetStencil =
  stencil8
    zeroTrit plus plus zeroTrit
    zeroTrit zeroTrit zeroTrit zeroTrit

poleWord : String
poleWord = "000+000-"

originWord : String
originWord = "00+00000"

jWord : String
jWord = "+--00000"

targetWord : String
targetWord = "0++00000"

------------------------------------------------------------------------
-- 5. Exact 3-adic depth-five split.
------------------------------------------------------------------------

record DepthFiveFactor : Set where
  constructor depth-five-factor
  field
    coefficient : Nat
    quotient : Nat
    exactFactor :
      coefficient ≡ pow3 5 * quotient

open DepthFiveFactor public

originDepthFive : DepthFiveFactor
originDepthFive =
  depth-five-factor originCoefficient 1 refl

jDepthFive : DepthFiveFactor
jDepthFive =
  depth-five-factor jCoefficient 5 refl

targetDepthFive : DepthFiveFactor
targetDepthFive =
  depth-five-factor targetCoefficient 4 refl

-- The pole coefficient is a 3-adic unit: it is 2 modulo 3.
poleCoefficientModThreeUnitReceipt :
  poleCoefficient ≡ 3 * 26 + 2
poleCoefficientModThreeUnitReceipt = refl

------------------------------------------------------------------------
-- 5a. Exact 3-adic depth certificates without a separate valuation function.
--
-- An exact depth-d certificate stores n = 3^d * u together with a concrete
-- remainder witness u = 3*q + r where r is 1 or 2.  Thus u is a 3-adic unit.
------------------------------------------------------------------------

data NonzeroModThreeRemainder : Set where
  remainderOne : NonzeroModThreeRemainder
  remainderTwo : NonzeroModThreeRemainder

remainderValue : NonzeroModThreeRemainder → Nat
remainderValue remainderOne = 1
remainderValue remainderTwo = 2

record ExactThreeAdicDepthCertificate (value depth : Nat) : Set where
  constructor exact-three-adic-depth-certificate
  field
    unit : Nat
    quotientByThree : Nat
    remainder : NonzeroModThreeRemainder
    factorExact :
      value ≡ pow3 depth * unit
    unitRemainderExact :
      unit ≡ 3 * quotientByThree + remainderValue remainder

open ExactThreeAdicDepthCertificate public

poleExactDepthZero :
  ExactThreeAdicDepthCertificate poleCoefficient 0
poleExactDepthZero =
  exact-three-adic-depth-certificate
    80 26 remainderTwo refl refl

originExactDepthFive :
  ExactThreeAdicDepthCertificate originCoefficient 5
originExactDepthFive =
  exact-three-adic-depth-certificate
    1 0 remainderOne refl refl

jExactDepthFive :
  ExactThreeAdicDepthCertificate jCoefficient 5
jExactDepthFive =
  exact-three-adic-depth-certificate
    5 1 remainderTwo refl refl

targetExactDepthFive :
  ExactThreeAdicDepthCertificate targetCoefficient 5
targetExactDepthFive =
  exact-three-adic-depth-certificate
    4 1 remainderOne refl refl

record RHKernelThreeAdicProfile : Set where
  constructor rh-kernel-three-adic-profile
  field
    poleDepth : Nat
    originDepth : Nat
    jDepth : Nat
    targetDepth : Nat

canonicalThreeAdicProfile : RHKernelThreeAdicProfile
canonicalThreeAdicProfile =
  rh-kernel-three-adic-profile 0 5 5 5

------------------------------------------------------------------------
-- 5b. Primitive-row / Smith-style certificate.
--
-- A direct Bezout witness from the first two coefficients already proves
-- primitiveness:
--
--   27*243 = 82*80 + 1.
--
-- Thus every common divisor of the coefficient row divides 1.  This scalar
-- primitive invariant is deliberately kept separate from the sharper 3-adic
-- depth profile.
------------------------------------------------------------------------

primitiveBezoutCertificate :
  27 * originCoefficient
  ≡ 82 * poleCoefficient + 1
primitiveBezoutCertificate = refl

data PrimitiveRowCertificateDeterminesDepthProfile : Set where

primitiveRowCertificateDoesNotDetermineDepthProfile :
  PrimitiveRowCertificateDeterminesDepthProfile → ⊥
primitiveRowCertificateDoesNotDetermineDepthProfile ()

------------------------------------------------------------------------
-- 6. Shift-polynomial normal form.
--
-- At X=3:
--
--   P : X^4 - 1
--   O : X^5
--   j : X^5 (X^2 - X - 1)
--   s : X^5 (X + 1)
--
-- The Nat equations below are the subtraction-free exact evaluations.
------------------------------------------------------------------------

poleShiftPolynomialAtThree :
  pow3 4 ≡ poleCoefficient + 1
poleShiftPolynomialAtThree = refl

originShiftPolynomialAtThree :
  originCoefficient ≡ pow3 5
originShiftPolynomialAtThree = refl

jShiftPolynomialAtThree :
  pow3 7 ≡ jCoefficient + pow3 6 + pow3 5
jShiftPolynomialAtThree = refl

targetShiftPolynomialAtThree :
  targetCoefficient ≡ pow3 5 * (3 + 1)
targetShiftPolynomialAtThree = refl

------------------------------------------------------------------------
-- 7. Cross-pollination with the existing 196830 carrier.
------------------------------------------------------------------------

twoSpikeBulk :
  Nat
twoSpikeBulk = pow3 11 + pow3 9

twoSpikeBulkIs196830 :
  twoSpikeBulk ≡ 196830
twoSpikeBulkIs196830 = refl

twoSpikeBulkMatchesExistingCarrier :
  twoSpikeBulk ≡ MonsterBulk.structuredBulkDimension
twoSpikeBulkMatchesExistingCarrier = refl

bulkAfterDepthFive :
  Nat
bulkAfterDepthFive = pow3 6 + pow3 4

bulkAfterDepthFiveIs810 :
  bulkAfterDepthFive ≡ 810
bulkAfterDepthFiveIs810 = refl

bulkFactorizationThroughDepthFive :
  twoSpikeBulk ≡ pow3 5 * bulkAfterDepthFive
bulkFactorizationThroughDepthFive = refl

sharedFourShiftBlock :
  bulkAfterDepthFive ≡ pow3 4 * (pow3 2 + 1)
sharedFourShiftBlock = refl

------------------------------------------------------------------------
-- 8. Firewall.
------------------------------------------------------------------------

data SparseTernaryStencilCreatesRHProof : Set where
data SharedThreePowerFourCreatesSemanticIdentity : Set where
data TwoSpikeMonsterBulkCreatesRHCarrierIdentity : Set where
data GoldenRatioPolynomialCreatesGoldenRatioMechanism : Set where

sparseStencilDoesNotReproveRH :
  SparseTernaryStencilCreatesRHProof → ⊥
sparseStencilDoesNotReproveRH ()

sharedFourShiftDoesNotCreateSemanticIdentity :
  SharedThreePowerFourCreatesSemanticIdentity → ⊥
sharedFourShiftDoesNotCreateSemanticIdentity ()

twoSpikeBulkDoesNotCreateRHCarrierIdentity :
  TwoSpikeMonsterBulkCreatesRHCarrierIdentity → ⊥
twoSpikeBulkDoesNotCreateRHCarrierIdentity ()

xSquaredMinusXMinusOneNotPromotedToGoldenRatioMechanism :
  GoldenRatioPolynomialCreatesGoldenRatioMechanism → ⊥
xSquaredMinusXMinusOneNotPromotedToGoldenRatioMechanism ()

record RiemannQuarticBalancedTernaryStencilBoundary : Set where
  constructor riemann-quartic-balanced-ternary-stencil-boundary
  field
    primitiveCoefficientVectorOwned : Bool
    sparseSignedStencilOwned : Bool
    valuationProfileZeroFiveFiveFiveOwned : Bool
    exactUnitFactorCertificatesOwned : Bool
    poleCoefficientCertifiedModThreeUnit : Bool
    commonDepthFiveBlockOwned : Bool
    shiftPolynomialNormalFormOwned : Bool
    twoSpike196830IdentityReused : Bool
    sharedFourShiftBlockOwned : Bool
    primitiveBezoutCertificateOwned : Bool
    primitiveInvariantDeterminesDepthProfile : Bool
    analyticRHIdentityReprovedHere : Bool
    semanticCarrierIdentityClaimed : Bool

canonicalRiemannQuarticBalancedTernaryStencilBoundary :
  RiemannQuarticBalancedTernaryStencilBoundary
canonicalRiemannQuarticBalancedTernaryStencilBoundary =
  riemann-quartic-balanced-ternary-stencil-boundary
    true true true true true true true true true
    true false
    false false
