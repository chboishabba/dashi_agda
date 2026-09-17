module DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact where

------------------------------------------------------------------------
-- S2b2d1b2 / DIVISION-FREE COHERENT-COVARIANCE CENTERING
--
-- R229 forbids a sign argument based only on nonnegative cellwise damping.
-- Instead retain the full signed finite family.  For scalar cell works w_i and
-- rates r_i, exact finite algebra gives
--
--   n (- sum_i r_i w_i) + (sum_i r_i)(sum_i w_i)
--     = - sum_{i<j} (r_i-r_j)(w_i-w_j).
--
-- On the literal fixed-output mixed-helicity fibre take
--
--   w_i = 2 Re <M,A_i>,
--   M   = sum_i A_i,
--   r_i = rho_p + rho_q.
--
-- The left side is exactly the division-free numerator of the coherent
-- covariance obtained by centering the variable viscous rates at their finite
-- mean.  The right side is a signed pair-difference object.  No division,
-- positivity, Cauchy, absolute value, endpoint estimate, or cutoff aggregation
-- is used here.
--
-- This is the first theorem-shaped interface on which the R571/Aug-5 paired
-- second-moment donor can be tested for same-object compatibility.  The actual
-- quantitative pair-difference payment remains open.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (length)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityDampedProductTangentRound231Exact as R231
import DASHI.Physics.Closure.NSTriadKNMixedHelicityCellDampedTangentRound292Exact as R292
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNGramDebtPairExpansionRound383Exact as R383
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work

F : C3.RealField _
F = Rational.rationalRealField

natAsRational : Nat → ℚ
natAsRational zero = 0ℚ
natAsRational (suc n) = 1ℚ + natAsRational n

rateSum : ∀ {A : Set} → (A → ℚ) → List A → ℚ
rateSum rate [] = 0ℚ
rateSum rate (x ∷ xs) = rate x + rateSum rate xs

workSum : ∀ {A : Set} → (A → ℚ) → List A → ℚ
workSum work [] = 0ℚ
workSum work (x ∷ xs) = work x + workSum work xs

weightedWorkSum : ∀ {A : Set} → (A → ℚ) → (A → ℚ) → List A → ℚ
weightedWorkSum rate work [] = 0ℚ
weightedWorkSum rate work (x ∷ xs) =
  rate x * work x + weightedWorkSum rate work xs

pairAgainstHead : ∀ {A : Set} →
  (A → ℚ) → (A → ℚ) → A → List A → ℚ
pairAgainstHead rate work head [] = 0ℚ
pairAgainstHead rate work head (x ∷ xs) =
  (rate head - rate x) * (work head - work x)
  + pairAgainstHead rate work head xs

pairDifferenceWorkSum : ∀ {A : Set} →
  (A → ℚ) → (A → ℚ) → List A → ℚ
pairDifferenceWorkSum rate work [] = 0ℚ
pairDifferenceWorkSum rate work (x ∷ xs) =
  pairAgainstHead rate work x xs + pairDifferenceWorkSum rate work xs

pairAgainstHeadClosedForm :
  ∀ {A : Set}
    (rate work : A → ℚ) (head : A) (xs : List A) →
  pairAgainstHead rate work head xs
  ≡
    natAsRational (length xs) * rate head * work head
    - rate head * workSum work xs
    - rateSum rate xs * work head
    + weightedWorkSum rate work xs
pairAgainstHeadClosedForm rate work head [] = solve []
pairAgainstHeadClosedForm rate work head (x ∷ xs)
  rewrite pairAgainstHeadClosedForm rate work head xs =
  solve
    ( natAsRational (length xs)
    ∷ rate head ∷ work head
    ∷ rate x ∷ work x
    ∷ rateSum rate xs
    ∷ workSum work xs
    ∷ weightedWorkSum rate work xs
    ∷ [])

pairDifferenceClosedForm :
  ∀ {A : Set} (rate work : A → ℚ) (xs : List A) →
  pairDifferenceWorkSum rate work xs
  ≡
    natAsRational (length xs) * weightedWorkSum rate work xs
    - rateSum rate xs * workSum work xs
pairDifferenceClosedForm rate work [] = solve []
pairDifferenceClosedForm rate work (x ∷ xs)
  rewrite pairAgainstHeadClosedForm rate work x xs
        | pairDifferenceClosedForm rate work xs =
  solve
    ( natAsRational (length xs)
    ∷ rate x ∷ work x
    ∷ rateSum rate xs
    ∷ workSum work xs
    ∷ weightedWorkSum rate work xs
    ∷ [])

divisionFreePairDifferenceCentering :
  ∀ {A : Set} (rate work : A → ℚ) (xs : List A) →
  natAsRational (length xs) * (0ℚ - weightedWorkSum rate work xs)
    + rateSum rate xs * workSum work xs
  ≡ 0ℚ - pairDifferenceWorkSum rate work xs
divisionFreePairDifferenceCentering rate work xs
  rewrite pairDifferenceClosedForm rate work xs =
  solve
    ( natAsRational (length xs)
    ∷ rateSum rate xs
    ∷ workSum work xs
    ∷ weightedWorkSum rate work xs
    ∷ [])

cellRate :
  (Z3.FourierMode → ℚ) → Physical.PhysicalTriadIncidence → ℚ
cellRate rho tau = rho (Physical.p tau) + rho (Physical.q tau)

cellValue :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
cellValue = D1a.mixedProductCell

cellWork :
  C3.Complex3 F →
  (Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → ℚ
cellWork mixed value tau = Work.coherentWork mixed (value tau)

workSumAgainstFold :
  (mixed : C3.Complex3 F) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  workSum (cellWork mixed value) items
  ≡ Work.coherentWork mixed (R224.foldVector value items)
workSumAgainstFold mixed value [] =
  sym
    (trans
      (cong (Work.two *_)
        (R383.realCrossZeroRight mixed))
      (solve []))
workSumAgainstFold mixed value (tau ∷ rest) =
  trans
    (cong (cellWork mixed value tau +_)
      (workSumAgainstFold mixed value rest))
    (sym
      (Work.workAddRight mixed (value tau) (R224.foldVector value rest)))

variableDecayCellAsRealScale :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (rho : Z3.FourierMode → ℚ) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (tau : Physical.PhysicalTriadIncidence) →
  D1a.variableDecayCell rho S velocity tau
  ≡ R291.realScale (0ℚ - cellRate rho tau)
      (D1a.mixedProductCell S velocity tau)
variableDecayCellAsRealScale rho S velocity tau =
  trans
    (sym
      (R231.complex3ScaleScalarAdd
        (R94.negativeReal (rho (Physical.p tau)))
        (R94.negativeReal (rho (Physical.q tau)))
        (D1a.mixedProductCell S velocity tau)))
    (R292.negativeRateSumScale
      (rho (Physical.p tau)) (rho (Physical.q tau))
      (D1a.mixedProductCell S velocity tau))

variableDecayWorkSum :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (mixed : C3.Complex3 F) →
  (rho : Z3.FourierMode → ℚ) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  Work.coherentWork mixed
    (R224.foldVector (D1a.variableDecayCell rho S velocity) items)
  ≡ 0ℚ - weightedWorkSum
      (cellRate rho)
      (cellWork mixed (D1a.mixedProductCell S velocity)) items
variableDecayWorkSum mixed rho S velocity [] =
  trans
    (cong (Work.two *_)
      (R383.realCrossZeroRight mixed))
    (solve [])
variableDecayWorkSum mixed rho S velocity (tau ∷ rest) =
  let
    value = D1a.mixedProductCell S velocity
    rate = cellRate rho tau
    headMeaning :
      Work.coherentWork mixed (D1a.variableDecayCell rho S velocity tau)
      ≡ (0ℚ - rate) * Work.coherentWork mixed (value tau)
    headMeaning =
      trans
        (cong (Work.coherentWork mixed)
          (variableDecayCellAsRealScale rho S velocity tau))
        (Work.workScaleRight (0ℚ - rate) mixed (value tau))
    tailMeaning = variableDecayWorkSum mixed rho S velocity rest
  in
  trans
    (Work.workAddRight mixed
      (D1a.variableDecayCell rho S velocity tau)
      (R224.foldVector (D1a.variableDecayCell rho S velocity) rest))
    (trans
      (cong₂ _+_ headMeaning tailMeaning)
      (solve
        ( rate
        ∷ Work.coherentWork mixed (value tau)
        ∷ weightedWorkSum
            (cellRate rho) (cellWork mixed value) rest
        ∷ [])))

fixedOutputCovariancePairDifference :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (rho : Z3.FourierMode → ℚ) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) (output : Z3.FourierMode) →
  let
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = R224.foldVector value items
    rate = cellRate rho
    work = cellWork mixed value
    decay = R224.foldVector (D1a.variableDecayCell rho S velocity) items
  in
  natAsRational (length items) * Work.coherentWork mixed decay
    + rateSum rate items * Work.coherentWork mixed mixed
  ≡ 0ℚ - pairDifferenceWorkSum rate work items
fixedOutputCovariancePairDifference rho S velocity cutoff output =
  let
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = R224.foldVector value items
    rate = cellRate rho
    work = cellWork mixed value
    decay = R224.foldVector (D1a.variableDecayCell rho S velocity) items
    decayMeaning :
      Work.coherentWork mixed decay
      ≡ 0ℚ - weightedWorkSum rate work items
    decayMeaning = variableDecayWorkSum mixed rho S velocity items
    selfMeaning :
      Work.coherentWork mixed mixed ≡ workSum work items
    selfMeaning = sym (workSumAgainstFold mixed value items)
  in
  rewrite decayMeaning | selfMeaning =
    divisionFreePairDifferenceCentering rate work items

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

divisionFreePairDifferenceCenteringClosed : Bool
divisionFreePairDifferenceCenteringClosed = true

fixedOutputCovariancePairDifferenceAttachmentClosed : Bool
fixedOutputCovariancePairDifferenceAttachmentClosed = true

quantitativePairDifferencePaymentClosed : Bool
quantitativePairDifferencePaymentClosed = false

divisionFreePairDifferenceCenteringClosedIsTrue :
  divisionFreePairDifferenceCenteringClosed ≡ true
divisionFreePairDifferenceCenteringClosedIsTrue = refl

fixedOutputCovariancePairDifferenceAttachmentClosedIsTrue :
  fixedOutputCovariancePairDifferenceAttachmentClosed ≡ true
fixedOutputCovariancePairDifferenceAttachmentClosedIsTrue = refl

quantitativePairDifferencePaymentClosedIsFalse :
  quantitativePairDifferencePaymentClosed ≡ false
quantitativePairDifferencePaymentClosedIsFalse = refl
