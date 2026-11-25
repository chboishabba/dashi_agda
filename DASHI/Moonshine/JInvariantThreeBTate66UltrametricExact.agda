module DASHI.Moonshine.JInvariantThreeBTate66UltrametricExact where

-- SOURCE-WRITTEN, not kernel checked. Literal sourced Tate dimensions,
-- signed eta coefficient and existing finite ultrametric carrier.
-- Do NOT identify Tate modules with graph pair/vertex permutation modules.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (_∸_)
open import Data.Vec using ([]; _∷_)
import Data.Integer as Z
open Z using (ℤ; +_; -_; ∣_∣)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
import DASHI.Arithmetic.VpDepth as V
import DASHI.Geometry.SSP369Ultrametric as U
import DASHI.Moonshine.OggSSP3B6BIntegralTateTraceValuationAuditExact as T
import DASHI.Moonshine.OggSSPP3TateSimpleFactorLengthOneExact as L
import DASHI.Moonshine.Monster3BBalancedRegularFibreExact as M
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y
import DASHI.Moonshine.Monster196884FibreInterferenceExact as F

evenTate oddTate : Nat
evenTate = T.ordinaryCoefficientMagnitude T.q1
oddTate = T.superCoefficientMagnitude T.q1

signedTrace : ℤ
signedTrace = (+ evenTate) Z.- (+ oddTate)

ordinaryTotal : Nat
ordinaryTotal = evenTate + oddTate

signedSource : signedTrace ≡ + M.monster3BConformalTrace
signedSource = refl

unsignedSource : ordinaryTotal ≡ 78
unsignedSource = refl

-- Preserve the signed input pair; valuation observes magnitude only.
signedDepth : Nat → ℤ → Nat
signedDepth p z = V.vp-depth 8 p (∣ z ∣)

signedLift : Nat → ℤ → ℤ → Nat
signedLift p x y =
  signedDepth p (x Z.+ y) ∸
    V.minNat (signedDepth p x) (signedDepth p y)

evenDepth : signedDepth 3 (+ evenTate) ≡ 1
evenDepth = refl

oddDepth : signedDepth 3 (- (+ oddTate)) ≡ 1
oddDepth = refl

residualDepth : signedDepth 3 signedTrace ≡ 3
residualDepth = refl

sumDepth : V.vp-depth 8 3 ordinaryTotal ≡ 1
sumDepth = refl

twoExtraLevels : signedLift 3 (+ evenTate) (- (+ oddTate)) ≡ 2
twoExtraLevels = refl

unsignedNoLift : signedLift 3 (+ evenTate) (+ oddTate) ≡ 0
unsignedNoLift = refl

-- Explicit factors certify exact depths, rather than relying on
-- finite-fuel saturation; these nonzero units are not divisible by 3.
evenFactor : evenTate ≡ 3 * 22
evenFactor = refl
oddFactor : oddTate ≡ 3 * 4
oddFactor = refl
traceFactor : ∣ signedTrace ∣ ≡ 27 * 2
traceFactor = refl
totalFactor : ordinaryTotal ≡ 3 * 26
totalFactor = refl

-- digit3, digit6, digit9 are mapped to 0,1,2 in THIS least-significant
-- digit chart, not asserted to be actual integers 3,6,9.
digitValue : U.Digit369 → Nat
digitValue U.digit3 = 0
digitValue U.digit6 = 1
digitValue U.digit9 = 2

decode : ∀ {d} → U.Address d → Nat
decode [] = 0
decode (x ∷ xs) = digitValue x + 3 * decode xs

evenAddress oddAddress residualAddress totalAddress zeroAddress : U.Address 4
evenAddress = U.digit3 ∷ U.digit6 ∷ U.digit6 ∷ U.digit9 ∷ []
oddAddress = U.digit3 ∷ U.digit6 ∷ U.digit6 ∷ U.digit3 ∷ []
residualAddress = U.digit3 ∷ U.digit3 ∷ U.digit3 ∷ U.digit9 ∷ []
totalAddress = U.digit3 ∷ U.digit9 ∷ U.digit9 ∷ U.digit9 ∷ []
zeroAddress = U.digit3 ∷ U.digit3 ∷ U.digit3 ∷ U.digit3 ∷ []

evenDecode : decode evenAddress ≡ evenTate
evenDecode = refl
oddDecode : decode oddAddress ≡ oddTate
oddDecode = refl
residualDecode : decode residualAddress ≡ ∣ signedTrace ∣
residualDecode = refl
totalDecode : decode totalAddress ≡ ordinaryTotal
totalDecode = refl
commonPrefix : U.agreementDepth evenAddress oddAddress ≡ 3
commonPrefix = refl
residualPrefix : U.agreementDepth residualAddress zeroAddress ≡ 3
residualPrefix = refl
unsignedPrefix : U.agreementDepth totalAddress zeroAddress ≡ 1
unsignedPrefix = refl

-- BIDI reconstruction from both observations. The factor 2 is a
-- 3-adic unit, but not a 2-adic unit. No scalar-only inverse claimed.
reopenEven : (a b : ℤ) →
  (a Z.+ b) Z.+ (a Z.- b) ≡ (+ 2) Z.* a
reopenEven a b =
  let open +-*-Solver in
  solve 2 (λ x y → (x :+ y) :+ (x :+ con (- (+ 1)) :* y)
      := con (+ 2) :* x) refl a b

reopenOdd : (a b : ℤ) →
  (a Z.+ b) Z.- (a Z.- b) ≡ (+ 2) Z.* b
reopenOdd a b =
  let open +-*-Solver in
  solve 2 (λ x y → (x :+ y) :+ con (- (+ 1)) :* (x :+ con (- (+ 1)) :* y)
      := con (+ 2) :* y) refl a b

-- Actual graph source: this is a signed cardinality chart ONLY.
pairCountMatchesEven : Y.length Y.pairs ≡ evenTate
pairCountMatchesEven = refl
nodeCountMatchesOdd : Y.length Y.nodes ≡ oddTate
nodeCountMatchesOdd = refl
coxeterCountMatchesTotal : Y.length Y.coxeterRelators ≡ ordinaryTotal
coxeterCountMatchesTotal = refl
virtualPairMinusNode :
  (+ Y.length Y.pairs) Z.- (+ Y.length Y.nodes) ≡ signedTrace
virtualPairMinusNode = refl

-- The fine bulk vanishes at all lower ternary depths, but is not zero.
fineDepth : V.vp-depth 10 3 F.fineSectorDimension ≡ 9
fineDepth = refl
fullDepth : V.vp-depth 10 3 F.fibreInterferenceTotal ≡ 3
fullDepth = refl
