module DASHI.Moonshine.JInvariantBishopLatticeEvenPowerShellMajorantExact where

-- Pay the next concrete gate of the existing punctured-lattice route:
-- from the actual reciprocal norm-square estimate, bound both components
-- of the ACTUAL weight-four and weight-six summands. No square root,
-- independent analytic carrier, or propositional equality of Bishop reals.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
open import Data.Bool.Base using (T)

import Real as R
import RealProperties as RP
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as N
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as U
import DASHI.Foundations.BishopNonnegativeSquareReflectionExact as Reflect
import DASHI.Analysis.BishopPositiveCrossReciprocalUpperExact as Cross
import DASHI.Moonshine.JInvariantBishopLatticeReciprocalShellMajorantExact as S
import DASHI.Moonshine.JInvariantBishopLatticeDenominatorCoercivityExact as Coercive
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as Upper
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as K
import DASHI.Moonshine.JInvariantPuncturedLatticeSquareShellExact as Shell

powerMono : ∀ {a b : R.ℝ} → R.NonNegative a → R._≤_ a b →
  (n : Nat) → R._≤_ (R.pow a n) (R.pow b n)
powerMono aNN le zero = RP.≤-refl
powerMono {a} {b} aNN le (suc n) =
  RP.*-mono-≤ (Seq.nonNegx⇒nonNegxⁿ n aNN) aNN
    (powerMono aNN le n) le

fourSquare : ∀ r → R._≃_ (R.pow r 4) (N.square (R.pow r 2))
fourSquare r =
  let open RP.ℝ-Solver in
  solve 1 (λ x →
    ((((Κ (+ 1 / 1) ⊗ x) ⊗ x) ⊗ x) ⊗ x) ⊜
    (((Κ (+ 1 / 1) ⊗ x) ⊗ x) ⊗ ((Κ (+ 1 / 1) ⊗ x) ⊗ x)))
    RP.≃-refl r

sixSquare : ∀ r → R._≃_ (R.pow r 6) (N.square (R.pow r 3))
sixSquare r =
  let open RP.ℝ-Solver in
  solve 1 (λ x →
    ((((((Κ (+ 1 / 1) ⊗ x) ⊗ x) ⊗ x) ⊗ x) ⊗ x) ⊗ x) ⊜
    ((((Κ (+ 1 / 1) ⊗ x) ⊗ x) ⊗ x) ⊗
     (((Κ (+ 1 / 1) ⊗ x) ⊗ x) ⊗ x)))
    RP.≃-refl r

-- General square-reflection consumer; no new analytic hypothesis.
componentBound :
  (q : C.BishopComplex) (m : R.ℝ) →
  R._≤_ (N.normSqC q) m →
  (k h : Nat) →
  R._≃_ (R.pow m k) (N.square (R.pow m h)) →
  (component : R.ℝ) →
  R._≤_ (N.square component) (N.normSqC (A.powC q k)) →
  R._≤_ (R.∣_∣ component) (R.pow m h)
componentBound q m bound k h evenLaw component below =
  let
    qNN = U.normSquareNonnegative q
    mNN = RP.0≤x⇒nonNegx
      (RP.≤-trans (RP.nonNegx⇒0≤x qNN) bound)
    powerBound = RP.≤-respˡ-≃ (N.normSqPower q k)
      (powerMono qNN bound k)
  in
  Reflect.squareReflectsOnNonnegative
    (RP.nonNeg∣x∣ component)
    (Seq.nonNegx⇒nonNegxⁿ h mNN)
    (RP.≤-respˡ-≃ (N.absoluteSquare component)
      (RP.≤-trans below (RP.≤-respʳ-≃ evenLaw powerBound)))

majorant : Upper.BishopUpperHalfPlanePoint → Nat → R.ℝ
majorant tau inner =
  R._*_ (Coercive.coercivityFactor (Upper.tau tau))
        (Cross.positiveInverse (S.weightedRadiusPositive tau inner))

reciprocal : Upper.BishopUpperHalfPlanePoint → K.NonzeroLatticePoint →
  C.BishopComplex
reciprocal tau index =
  K.latticeReciprocal Upper.upperHalfPlaneDenominatorGeometry tau index

summand : Nat → Upper.BishopUpperHalfPlanePoint → K.NonzeroLatticePoint →
  C.BishopComplex
summand weight tau index =
  K.latticeEisensteinSummand Upper.upperHalfPlaneDenominatorGeometry
    weight index tau

realWeight4 : ∀ tau inner index →
  T (Shell.onSuccessorSquareShell? inner (K.point index)) →
  R._≤_ (R.∣_∣ (C.re (summand 4 tau index))) (R.pow (majorant tau inner) 2)
realWeight4 tau inner index onShell =
  componentBound (reciprocal tau index) (majorant tau inner)
    (S.reciprocalNormSquareShellUpper tau inner index onShell)
    4 2 (fourSquare (majorant tau inner)) _
    (N.componentSquareBelowNormSqReal (summand 4 tau index))

imagWeight4 : ∀ tau inner index →
  T (Shell.onSuccessorSquareShell? inner (K.point index)) →
  R._≤_ (R.∣_∣ (C.im (summand 4 tau index))) (R.pow (majorant tau inner) 2)
imagWeight4 tau inner index onShell =
  componentBound (reciprocal tau index) (majorant tau inner)
    (S.reciprocalNormSquareShellUpper tau inner index onShell)
    4 2 (fourSquare (majorant tau inner)) _
    (N.componentSquareBelowNormSqImag (summand 4 tau index))

realWeight6 : ∀ tau inner index →
  T (Shell.onSuccessorSquareShell? inner (K.point index)) →
  R._≤_ (R.∣_∣ (C.re (summand 6 tau index))) (R.pow (majorant tau inner) 3)
realWeight6 tau inner index onShell =
  componentBound (reciprocal tau index) (majorant tau inner)
    (S.reciprocalNormSquareShellUpper tau inner index onShell)
    6 3 (sixSquare (majorant tau inner)) _
    (N.componentSquareBelowNormSqReal (summand 6 tau index))

imagWeight6 : ∀ tau inner index →
  T (Shell.onSuccessorSquareShell? inner (K.point index)) →
  R._≤_ (R.∣_∣ (C.im (summand 6 tau index))) (R.pow (majorant tau inner) 3)
imagWeight6 tau inner index onShell =
  componentBound (reciprocal tau index) (majorant tau inner)
    (S.reciprocalNormSquareShellUpper tau inner index onShell)
    6 3 (sixSquare (majorant tau inner)) _
    (N.componentSquareBelowNormSqImag (summand 6 tau index))

-- Finite shell folds, tail convergence, normalization and the q/lattice
-- identity remain with the original punctured-lattice compiler.
