module DASHI.Physics.Closure.NSTriadKNLiteralInfinityShellBernsteinPaymentExact where

------------------------------------------------------------------------
-- PERIODIC B1 / LITERAL INFINITY-SHELL -> R465/R234 PAYMENT
--
-- Replace R466's synthetic eightfold support carrier by the actual
-- duplicate-free max-norm shell support.  Once a physical DFL shell producer
-- supplies an InfinityShellSupport and the ordinary finite Bernstein input,
-- shell cardinality is paid by the literal outer cube and then by the chosen
-- derivative coefficient.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Nat.Base as Nat
open Nat using (z≤n; s≤s)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSPeriodicInfinityShellModeCount as ShellCount
import DASHI.Physics.Closure.NSPeriodicInfinityShellSubsetCountExact as SubsetCount
import DASHI.Physics.Closure.NSTriadKNRationalFiniteBernstein as Bernstein
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalInfinityShellBernsteinRound465Exact as R465
import DASHI.Physics.Closure.NSTriadKNDeepFarLowCriticalShoulderRound234Exact as R234
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as NatQ
import DASHI.Physics.Closure.NSTriadKNRationalIntegerEmbeddingModeNormScaleExact as NatOrder

cubeLeToNatLe :
  ∀ {m n} → m Cube.≤ᴺ n → Nat._≤_ m n
cubeLeToNatLe Cube.z≤n = z≤n
cubeLeToNatLe (Cube.s≤s proof) = s≤s (cubeLeToNatLe proof)

supportCardinalityMapLength :
  (coefficient : Z3.FourierMode → ℚ) →
  (modes : List Z3.FourierMode) →
  Bernstein.supportCardinality (Cube.map coefficient modes)
  ≡ NatQ.natAsRational (Cube.length modes)
supportCardinalityMapLength coefficient [] = refl
supportCardinalityMapLength coefficient (mode ∷ modes) =
  cong (1ℚ +_) (supportCardinalityMapLength coefficient modes)

record LiteralInfinityShellBernsteinData (shell : Nat) : Set₁ where
  constructor literal-infinity-shell-bernstein-data
  field
    support : ShellCount.InfinityShellSupport shell
    coefficient : Z3.FourierMode → ℚ

    highEnergy highDerivativeCoefficient productMass : ℚ

    highEnergyNN : 0ℚ ≤ highEnergy
    highDerivativeCoefficientNN : 0ℚ ≤ highDerivativeCoefficient

    outerCubeCardinalityPaidByDerivative :
      NatQ.natAsRational (ShellCount.infinityCubeModeCount shell)
      ≤ highDerivativeCoefficient

    productMassBelowFiniteBernsteinInput :
      productMass
      ≤
      let coefficients = Cube.map coefficient (ShellCount.shellModes support)
      in
      Rational.square
        (Bernstein.coefficientSum coefficients)
        * highEnergy

open LiteralInfinityShellBernsteinData public

coefficients :
  ∀ {shell} →
  LiteralInfinityShellBernsteinData shell →
  List ℚ
coefficients D =
  Cube.map (coefficient D) (ShellCount.shellModes (support D))

literalShellCardinalityPaidByOuterCube :
  ∀ {shell} (D : LiteralInfinityShellBernsteinData shell) →
  Bernstein.supportCardinality (coefficients D)
  ≤ NatQ.natAsRational (ShellCount.infinityCubeModeCount shell)
literalShellCardinalityPaidByOuterCube {shell} D =
  let
    natBound =
      cubeLeToNatLe
        (SubsetCount.literalInfinityShellLengthBound shell (support D))

    rationalBound =
      NatOrder.natAsRationalMonotone natBound
  in
  subst
    (_≤ NatQ.natAsRational (ShellCount.infinityCubeModeCount shell))
    (sym
      (supportCardinalityMapLength
        (coefficient D)
        (ShellCount.shellModes (support D))))
    rationalBound

literalShellCardinalityPaidByDerivative :
  ∀ {shell} (D : LiteralInfinityShellBernsteinData shell) →
  Bernstein.supportCardinality (coefficients D)
  ≤ highDerivativeCoefficient D
literalShellCardinalityPaidByDerivative D =
  ℚP.≤-trans
    (literalShellCardinalityPaidByOuterCube D)
    (outerCubeCardinalityPaidByDerivative D)

toR465FiniteBernsteinData :
  ∀ {shell} →
  LiteralInfinityShellBernsteinData shell →
  R465.DeepFarLowFiniteBernsteinData
toR465FiniteBernsteinData D = record
  { R465.coefficients = coefficients D
  ; R465.highEnergy = highEnergy D
  ; R465.highDerivativeCoefficient = highDerivativeCoefficient D
  ; R465.productMass = productMass D
  ; R465.highEnergyNN = highEnergyNN D
  ; R465.highDerivativeCoefficientNN = highDerivativeCoefficientNN D
  ; R465.supportCardinalityPaidByDerivative =
      literalShellCardinalityPaidByDerivative D
  ; R465.productMassBelowBernsteinInput =
      productMassBelowFiniteBernsteinInput D
  }

toR234DeepFarLowPayment :
  ∀ {shell} →
  LiteralInfinityShellBernsteinData shell →
  R234.DeepFarLowScalarPayment
toR234DeepFarLowPayment D =
  R465.toR234DeepFarLowScalarPayment (toR465FiniteBernsteinData D)

literalInfinityShellBernsteinPaidByEnergyDissipation :
  ∀ {shell} (D : LiteralInfinityShellBernsteinData shell) →
  productMass D
  ≤ Bernstein.coefficientNormSquared (coefficients D)
      * R234.highDissipation (toR234DeepFarLowPayment D)
literalInfinityShellBernsteinPaidByEnergyDissipation D =
  R465.deepFarLowFiniteBernsteinPaidByEnergyDissipation
    (toR465FiniteBernsteinData D)

literalInfinityShellBernsteinCompilerClosed : Bool
literalInfinityShellBernsteinCompilerClosed = true

literalInfinityShellUsesSyntheticEightfoldCarrier : Bool
literalInfinityShellUsesSyntheticEightfoldCarrier = false

literalInfinityShellPhysicalFilteredDFLExtractionClosedHere : Bool
literalInfinityShellPhysicalFilteredDFLExtractionClosedHere = false

literalInfinityShellBernsteinIntroducesPostulate : Bool
literalInfinityShellBernsteinIntroducesPostulate = false

literalInfinityShellBernsteinCompilerClosedIsTrue :
  literalInfinityShellBernsteinCompilerClosed ≡ true
literalInfinityShellBernsteinCompilerClosedIsTrue = refl
