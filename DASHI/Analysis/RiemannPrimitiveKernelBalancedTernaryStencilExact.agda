module DASHI.Analysis.RiemannPrimitiveKernelBalancedTernaryStencilExact where

------------------------------------------------------------------------
-- RH PRIMITIVE INTEGER KERNEL: SPARSE BALANCED-TERNARY STENCIL
--
-- DASHI CONTRIBUTION
--
-- This module formalizes only the exact integer arithmetic behind the
-- primitive coefficient vector
--
--   (80, 243, 1215, 972).
--
-- It does NOT claim that balanced ternary proves RH, closes the analytic
-- absorption wall, or identifies these coefficients with a geometric carrier.
--
-- The point is to expose the coefficient vector as a sparse signed ternary
-- shift stencil:
--
--   80   = 3^4 - 1
--   243  = 3^5
--   1215 = 3^7 - 3^6 - 3^5
--        = 3^5 * (3^2 - 3 - 1)
--   972  = 3^6 + 3^5
--        = 3^5 * (3 + 1).
--
-- Thus three coordinates share a literal depth-five ternary shift while the
-- pole coefficient is the punctured four-shift 3^4-1.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Nat using (_∸_)

import DASHI.Biology.TernaryHypercubeHyperfabricExact as Hyper
import DASHI.Foundations.Base369Nat as BaseNat using (_%_)

pow3 : Nat -> Nat
pow3 n = Hyper.powNat 3 n

poleCoefficient : Nat
poleCoefficient = pow3 4 ∸ 1

originCoefficient : Nat
originCoefficient = pow3 5

jCoefficient : Nat
jCoefficient = (pow3 7 ∸ pow3 6) ∸ pow3 5

sCoefficient : Nat
sCoefficient = pow3 6 + pow3 5

poleCoefficientIs80 : poleCoefficient ≡ 80
poleCoefficientIs80 = refl

originCoefficientIs243 : originCoefficient ≡ 243
originCoefficientIs243 = refl

jCoefficientIs1215 : jCoefficient ≡ 1215
jCoefficientIs1215 = refl

sCoefficientIs972 : sCoefficient ≡ 972
sCoefficientIs972 = refl

------------------------------------------------------------------------
-- Common depth-five factorization.
------------------------------------------------------------------------

jResidualStencil : Nat
jResidualStencil = (pow3 2 ∸ 3) ∸ 1

sResidualStencil : Nat
sResidualStencil = 3 + 1

jResidualStencilIsFive : jResidualStencil ≡ 5
jResidualStencilIsFive = refl

sResidualStencilIsFour : sResidualStencil ≡ 4
sResidualStencilIsFour = refl

jCoefficientDepthFive :
  jCoefficient ≡ pow3 5 * jResidualStencil
jCoefficientDepthFive = refl

sCoefficientDepthFive :
  sCoefficient ≡ pow3 5 * sResidualStencil
sCoefficientDepthFive = refl

originCoefficientDepthFive :
  originCoefficient ≡ pow3 5 * 1
originCoefficientDepthFive = refl

------------------------------------------------------------------------
-- Sparse-word shape receipts.
--
-- Instead of treating the decimal coefficients as primitive, record the
-- occupied ternary exponents and signs.  These are the balanced-ternary words:
--
--   80   -> 1000T
--   243  -> 100000
--   1215 -> 1TT00000
--   972  -> 1100000
------------------------------------------------------------------------

record SparseSignedTernaryShape : Set where
  constructor sparse-signed-ternary-shape
  field
    positiveSpikes : List Nat
    negativeSpikes : List Nat

open SparseSignedTernaryShape public

poleStencilShape : SparseSignedTernaryShape
poleStencilShape =
  sparse-signed-ternary-shape (4 ∷ []) (0 ∷ [])

originStencilShape : SparseSignedTernaryShape
originStencilShape =
  sparse-signed-ternary-shape (5 ∷ []) []

jStencilShape : SparseSignedTernaryShape
jStencilShape =
  sparse-signed-ternary-shape (7 ∷ []) (6 ∷ 5 ∷ [])

sStencilShape : SparseSignedTernaryShape
sStencilShape =
  sparse-signed-ternary-shape (6 ∷ 5 ∷ []) []

------------------------------------------------------------------------
-- 3-adic filtration shape, stated without importing a separate valuation
-- library: the last three coefficients have an exact displayed 3^5 factor;
-- the pole coefficient is the punctured unit-side term 3^4-1.
------------------------------------------------------------------------

record PrimitiveKernelDepthFiveShape : Set where
  constructor primitive-kernel-depth-five-shape
  field
    poleIsPuncturedFourShift :
      poleCoefficient ≡ pow3 4 ∸ 1
    originSharesFiveShift :
      originCoefficient ≡ pow3 5 * 1
    jSharesFiveShift :
      jCoefficient ≡ pow3 5 * jResidualStencil
    sSharesFiveShift :
      sCoefficient ≡ pow3 5 * sResidualStencil

canonicalPrimitiveKernelDepthFiveShape :
  PrimitiveKernelDepthFiveShape
canonicalPrimitiveKernelDepthFiveShape =
  primitive-kernel-depth-five-shape
    refl
    originCoefficientDepthFive
    jCoefficientDepthFive
    sCoefficientDepthFive

------------------------------------------------------------------------
-- Exact 3-adic depth witnesses.
--
-- A witness is a factorization c = 3^d * u together with a nonzero ternary
-- residue of u.  This is enough to certify the exact displayed 3-adic depth
-- without importing a separate valuation library.
------------------------------------------------------------------------

data NonzeroTernaryResidue : Set where
  residueOne residueTwo : NonzeroTernaryResidue

residueValue : NonzeroTernaryResidue -> Nat
residueValue residueOne = 1
residueValue residueTwo = 2

record ExactThreeAdicDepthWitness (coefficient : Nat) : Set where
  constructor exact-three-adic-depth-witness
  field
    depth : Nat
    unit : Nat
    factorization :
      coefficient ≡ pow3 depth * unit
    unitResidue : NonzeroTernaryResidue
    residueExact :
      unit % 3 ≡ residueValue unitResidue

open ExactThreeAdicDepthWitness public

poleDepthZero :
  ExactThreeAdicDepthWitness poleCoefficient
poleDepthZero =
  exact-three-adic-depth-witness
    0 80 refl residueTwo refl

originDepthFive :
  ExactThreeAdicDepthWitness originCoefficient
originDepthFive =
  exact-three-adic-depth-witness
    5 1 refl residueOne refl

jDepthFive :
  ExactThreeAdicDepthWitness jCoefficient
jDepthFive =
  exact-three-adic-depth-witness
    5 5 refl residueTwo refl

sDepthFive :
  ExactThreeAdicDepthWitness sCoefficient
sDepthFive =
  exact-three-adic-depth-witness
    5 4 refl residueOne refl

record PrimitiveKernelThreeAdicProfile : Set where
  constructor primitive-kernel-three-adic-profile
  field
    poleDepth : Nat
    originDepth : Nat
    jDepth : Nat
    sDepth : Nat

canonicalPrimitiveKernelThreeAdicProfile :
  PrimitiveKernelThreeAdicProfile
canonicalPrimitiveKernelThreeAdicProfile =
  primitive-kernel-three-adic-profile 0 5 5 5

------------------------------------------------------------------------
-- Shift-polynomial reading at X=3.
------------------------------------------------------------------------

xPlusOneAtThree : Nat
xPlusOneAtThree = 3 + 1

xSquaredMinusXMinusOneAtThree : Nat
xSquaredMinusXMinusOneAtThree =
  (pow3 2 ∸ 3) ∸ 1

xPlusOneAtThreeIsFour :
  xPlusOneAtThree ≡ 4
xPlusOneAtThreeIsFour = refl

xSquaredMinusXMinusOneAtThreeIsFive :
  xSquaredMinusXMinusOneAtThree ≡ 5
xSquaredMinusXMinusOneAtThreeIsFive = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SparseStencilProvesRH : Set where
data GoldenPolynomialAtThreeIdentifiesGoldenRatioDynamics : Set where
data PuncturedCoefficientConstructsEightyPointCarrier : Set where

sparseStencilDoesNotProveRH :
  SparseStencilProvesRH -> ⊥
sparseStencilDoesNotProveRH ()

evaluationAtThreeDoesNotIdentifyGoldenRatioDynamics :
  GoldenPolynomialAtThreeIdentifiesGoldenRatioDynamics -> ⊥
evaluationAtThreeDoesNotIdentifyGoldenRatioDynamics ()

puncturedCoefficientDoesNotConstructEightyPointCarrier :
  PuncturedCoefficientConstructsEightyPointCarrier -> ⊥
puncturedCoefficientDoesNotConstructEightyPointCarrier ()

record RiemannPrimitiveKernelBalancedTernaryBoundary : Set where
  constructor riemann-primitive-kernel-balanced-ternary-boundary
  field
    decimalCoefficientVectorRecovered : Bool
    sparseSignedTernaryStencilOwned : Bool
    commonDepthFiveFactorOwned : Bool
    exactThreeAdicProfileZeroFiveFiveFiveOwned : Bool
    puncturedFourShiftOwned : Bool
    goldenPolynomialOnlyEvaluatedAtThree : Bool
    rhClosedHere : Bool
    eightyPointCarrierConstructedHere : Bool

canonicalRiemannPrimitiveKernelBalancedTernaryBoundary :
  RiemannPrimitiveKernelBalancedTernaryBoundary
canonicalRiemannPrimitiveKernelBalancedTernaryBoundary =
  riemann-primitive-kernel-balanced-ternary-boundary
    true true true true true true false false
