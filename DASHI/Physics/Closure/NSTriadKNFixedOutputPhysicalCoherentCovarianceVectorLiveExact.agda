module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceVectorLiveExact where

------------------------------------------------------------------------
-- S2b2d1b2 / LIVE COHERENT COVARIANCE AS ONE CENTERED VECTOR WORK
--
-- The scalar d1b2 centering theorem writes the live covariance numerator as
-- the negative complete-graph pair-difference work sum.  The vector centering
-- owner proves, before norms,
--
--   V = sum_{i<j} (r_i-r_j)(A_i-A_j)
--     = n sum_i r_i A_i - (sum_i r_i)(sum_i A_i).
--
-- This file proves that the SAME scalar pair graph is exactly W(M,V), then
-- instantiates V on the literal physical output fibre.  Since the variable
-- decay cell is -r_i A_i, it also proves
--
--   V = - n D - R M,
--
-- where M is the fixed-output mixed-product fold, D is the fixed-output
-- variable-decay fold, and R = sum_i r_i.
--
-- Hence the d1b2 numerator is ONE Hermitian work:
--
--   covarianceNumerator = - W(M,V).
--
-- This removes the pairwise Young family (and its repeated ||M||^2 term) from
-- the primary route.  No norm inequality or cutoff estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinWaleffeAmplitudeTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceVectorCenteringExact as Vector
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact as ScalarLive

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- 1. Coherent work commutes with the vector pair-difference graph.
------------------------------------------------------------------------

workSubtractRight :
  (left rightA rightB : C3.Complex3 F) →
  Work.coherentWork left (C3.complex3Subtract rightA rightB)
  ≡ Work.coherentWork left rightA - Work.coherentWork left rightB
workSubtractRight
    (C3.complex3
      (C3.complex lr li) (C3.complex mr mi) (C3.complex nr ni))
    (C3.complex3
      (C3.complex ar ai) (C3.complex br bi) (C3.complex cr ci))
    (C3.complex3
      (C3.complex dr di) (C3.complex er ei) (C3.complex fr fi)) =
  solve
    (lr ∷ li ∷ mr ∷ mi ∷ nr ∷ ni
    ∷ ar ∷ ai ∷ br ∷ bi ∷ cr ∷ ci
    ∷ dr ∷ di ∷ er ∷ ei ∷ fr ∷ fi ∷ [])

pairVectorTermWork :
  ∀ {A : Set} →
  (mixed : C3.Complex3 F) →
  (rate : A → ℚ) →
  (value : A → C3.Complex3 F) →
  (left right : A) →
  Work.coherentWork mixed
    (Vector.pairVectorTerm rate value left right)
  ≡
  (rate left - rate right)
    * ( Work.coherentWork mixed (value left)
      - Work.coherentWork mixed (value right) )
pairVectorTermWork mixed rate value left right =
  trans
    (Work.workScaleRight
      (rate left - rate right)
      mixed
      (C3.complex3Subtract (value left) (value right)))
    (cong
      ((rate left - rate right) *_)
      (workSubtractRight mixed (value left) (value right)))

pairVectorAgainstHeadWork :
  ∀ {A : Set} →
  (mixed : C3.Complex3 F) →
  (rate : A → ℚ) →
  (value : A → C3.Complex3 F) →
  (head : A) →
  (rest : List A) →
  Work.coherentWork mixed
    (Vector.pairVectorAgainstHead rate value head rest)
  ≡
  Pair.pairAgainstHead
    rate
    (λ item → Work.coherentWork mixed (value item))
    head rest
pairVectorAgainstHeadWork mixed rate value head [] =
  let
    zeroWork :
      Work.coherentWork mixed (C3.complex3Zero F) ≡ 0ℚ
    zeroWork
      with mixed
    ... | C3.complex3
          (C3.complex ar ai) (C3.complex br bi) (C3.complex cr ci) =
      solve (ar ∷ ai ∷ br ∷ bi ∷ cr ∷ ci ∷ [])
  in
  zeroWork
pairVectorAgainstHeadWork mixed rate value head (x ∷ xs) =
  trans
    (Work.workAddRight
      mixed
      (Vector.pairVectorTerm rate value head x)
      (Vector.pairVectorAgainstHead rate value head xs))
    (cong₂ _+_
      (pairVectorTermWork mixed rate value head x)
      (pairVectorAgainstHeadWork mixed rate value head xs))

pairVectorDifferenceWork :
  ∀ {A : Set} →
  (mixed : C3.Complex3 F) →
  (rate : A → ℚ) →
  (value : A → C3.Complex3 F) →
  (items : List A) →
  Work.coherentWork mixed
    (Vector.pairVectorDifferenceSum rate value items)
  ≡
  Pair.pairDifferenceWorkSum
    rate
    (λ item → Work.coherentWork mixed (value item))
    items
pairVectorDifferenceWork mixed rate value [] =
  let
    zeroWork :
      Work.coherentWork mixed (C3.complex3Zero F) ≡ 0ℚ
    zeroWork
      with mixed
    ... | C3.complex3
          (C3.complex ar ai) (C3.complex br bi) (C3.complex cr ci) =
      solve (ar ∷ ai ∷ br ∷ bi ∷ cr ∷ ci ∷ [])
  in
  zeroWork
pairVectorDifferenceWork mixed rate value (x ∷ xs) =
  trans
    (Work.workAddRight
      mixed
      (Vector.pairVectorAgainstHead rate value x xs)
      (Vector.pairVectorDifferenceSum rate value xs))
    (cong₂ _+_
      (pairVectorAgainstHeadWork mixed rate value x xs)
      (pairVectorDifferenceWork mixed rate value xs))

------------------------------------------------------------------------
-- 2. Literal physical fixed-output specialization.
------------------------------------------------------------------------

module LiveVector
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module Live = ScalarLive.Live physicalSystem S

  system = Field30.finiteSystem physicalSystem
  cutoff = Audit.cutoff system
  velocity = Audit.velocity system
  rho = R94.physicalDecayRate physicalSystem

  value : Physical.PhysicalTriadIncidence → C3.Complex3 F
  value = D1a.mixedProductCell S velocity

  rate : Physical.PhysicalTriadIncidence → ℚ
  rate = Pair.cellRate rho

  fibre : Z3.FourierMode → List Physical.PhysicalTriadIncidence
  fibre output = Output.physicalOutputFiber cutoff output

  mixed : Z3.FourierMode → C3.Complex3 F
  mixed = Live.mixed

  decay : Z3.FourierMode → C3.Complex3 F
  decay = Live.decay

  centeredRateVector : Z3.FourierMode → C3.Complex3 F
  centeredRateVector output =
    Vector.pairVectorDifferenceSum rate value (fibre output)

  centeredRateClosedForm : Z3.FourierMode → C3.Complex3 F
  centeredRateClosedForm output =
    Vector.closedFormVector rate value (fibre output)

  centeredRateVectorClosedForm :
    (output : Z3.FourierMode) →
    centeredRateVector output ≡ centeredRateClosedForm output
  centeredRateVectorClosedForm output =
    Vector.completeGraphVectorCovarianceIdentity
      rate value (fibre output)

  covarianceNumeratorIsNegativeCenteredVectorWork :
    (output : Z3.FourierMode) →
    Live.coherentCovarianceNumerator output
    ≡ 0ℚ - Work.coherentWork
      (mixed output) (centeredRateVector output)
  covarianceNumeratorIsNegativeCenteredVectorWork output =
    trans
      (Live.exactCentering output)
      (cong
        (0ℚ -_)
        (sym
          (pairVectorDifferenceWork
            (mixed output) rate value (fibre output))))

  covarianceNumeratorIsNegativeClosedFormWork :
    (output : Z3.FourierMode) →
    Live.coherentCovarianceNumerator output
    ≡ 0ℚ - Work.coherentWork
      (mixed output) (centeredRateClosedForm output)
  covarianceNumeratorIsNegativeClosedFormWork output =
    trans
      (covarianceNumeratorIsNegativeCenteredVectorWork output)
      (cong
        (λ vector → 0ℚ - Work.coherentWork (mixed output) vector)
        (centeredRateVectorClosedForm output))

  ----------------------------------------------------------------------
  -- 3. Identify the two vector sums in the closed form with literal M,D.
  ----------------------------------------------------------------------

  vectorSumIsPhysicalMixed :
    (items : List Physical.PhysicalTriadIncidence) →
    Vector.vectorSum value items ≡ R224.foldVector value items
  vectorSumIsPhysicalMixed [] = refl
  vectorSumIsPhysicalMixed (x ∷ xs) =
    cong (C3.complex3Add (value x)) (vectorSumIsPhysicalMixed xs)

  negativeRealScale :
    (scalar : ℚ) (v : C3.Complex3 F) →
    R291.realScale (0ℚ - scalar) v
    ≡ C3.complex3Negate (R291.realScale scalar v)
  negativeRealScale scalar
      (C3.complex3
        (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi)) =
    Algebra.complex3Ext
      (Algebra.complexExt
        (solve (scalar ∷ xr ∷ xi ∷ []))
        (solve (scalar ∷ xr ∷ xi ∷ [])))
      (Algebra.complexExt
        (solve (scalar ∷ yr ∷ yi ∷ []))
        (solve (scalar ∷ yr ∷ yi ∷ [])))
      (Algebra.complexExt
        (solve (scalar ∷ zr ∷ zi ∷ []))
        (solve (scalar ∷ zr ∷ zi ∷ [])))

  weightedCellIsNegativeDecayCell :
    (tau : Physical.PhysicalTriadIncidence) →
    R291.realScale (rate tau) (value tau)
    ≡ C3.complex3Negate (D1a.variableDecayCell rho S velocity tau)
  weightedCellIsNegativeDecayCell tau =
    trans
      (sym negateInvolutive)
      (trans
        (cong C3.complex3Negate
          (sym (negativeRealScale (rate tau) (value tau))))
        (cong C3.complex3Negate
          (sym
            (Pair.variableDecayCellAsRealScale
              rho S velocity tau))))
    where
    negateInvolutive :
      C3.complex3Negate
        (C3.complex3Negate (R291.realScale (rate tau) (value tau)))
      ≡ R291.realScale (rate tau) (value tau)
    negateInvolutive
      with R291.realScale (rate tau) (value tau)
    ... | C3.complex3
          (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi) =
      Algebra.complex3Ext
        (Algebra.complexExt
          (solve (xr ∷ xi ∷ []))
          (solve (xr ∷ xi ∷ [])))
        (Algebra.complexExt
          (solve (yr ∷ yi ∷ []))
          (solve (yr ∷ yi ∷ [])))
        (Algebra.complexExt
          (solve (zr ∷ zi ∷ []))
          (solve (zr ∷ zi ∷ [])))

  weightedVectorSumIsNegativeDecay :
    (items : List Physical.PhysicalTriadIncidence) →
    Vector.weightedVectorSum rate value items
    ≡ C3.complex3Negate
        (R224.foldVector
          (D1a.variableDecayCell rho S velocity) items)
  weightedVectorSumIsNegativeDecay [] =
    sym R225.complex3NegateZero
  weightedVectorSumIsNegativeDecay (tau ∷ rest) =
    trans
      (cong₂ C3.complex3Add
        (weightedCellIsNegativeDecayCell tau)
        (weightedVectorSumIsNegativeDecay rest))
      (sym
        (R225.complex3NegateAdd
          (D1a.variableDecayCell rho S velocity tau)
          (R224.foldVector
            (D1a.variableDecayCell rho S velocity) rest)))

  closedFormIsNegativeDecayAndMixed :
    (output : Z3.FourierMode) →
    centeredRateClosedForm output
    ≡
    C3.complex3Subtract
      (R291.realScale
        (Pair.natAsRational (length (fibre output)))
        (C3.complex3Negate (decay output)))
      (R291.realScale
        (Pair.rateSum rate (fibre output))
        (mixed output))
  closedFormIsNegativeDecayAndMixed output =
    cong₂ C3.complex3Subtract
      (cong
        (R291.realScale (Pair.natAsRational (length (fibre output))))
        (weightedVectorSumIsNegativeDecay (fibre output)))
      (cong
        (R291.realScale (Pair.rateSum rate (fibre output)))
        (vectorSumIsPhysicalMixed (fibre output)))

  liveCovarianceSingleVectorClosed : Bool
  liveCovarianceSingleVectorClosed = true

  pairwiseYoungFamilyRequiredForPrimaryD1b2Route : Bool
  pairwiseYoungFamilyRequiredForPrimaryD1b2Route = false

  centeredVectorCutoffUniformNormPaymentClosedHere : Bool
  centeredVectorCutoffUniformNormPaymentClosedHere = false

  clayPromotion : Bool
  clayPromotion = false

liveCoherentCovarianceVectorReductionClosed : Bool
liveCoherentCovarianceVectorReductionClosed = true

pairwiseYoungFamilyRequiredForPrimaryD1b2Route : Bool
pairwiseYoungFamilyRequiredForPrimaryD1b2Route = false

centeredVectorCutoffUniformNormPaymentClosedHere : Bool
centeredVectorCutoffUniformNormPaymentClosedHere = false

clayPromotion : Bool
clayPromotion = false

liveCoherentCovarianceVectorReductionClosedIsTrue :
  liveCoherentCovarianceVectorReductionClosed ≡ true
liveCoherentCovarianceVectorReductionClosedIsTrue = refl

pairwiseYoungFamilyRequiredForPrimaryD1b2RouteIsFalse :
  pairwiseYoungFamilyRequiredForPrimaryD1b2Route ≡ false
pairwiseYoungFamilyRequiredForPrimaryD1b2RouteIsFalse = refl
