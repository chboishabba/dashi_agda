module DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact where

------------------------------------------------------------------------
-- S2b2d1b / FIXED-OUTPUT COHERENT-COVARIANCE WORK DECOMPOSITION
--
-- d1a already proves on the literal fixed-output mixed-helicity fibre
--
--   tangent = variableDecay + commutator.
--
-- This owner pushes that exact vector identity through the SAME real-Hermitian
-- scalar consumer used elsewhere in the NS programme.  For the coherent cell
-- sum M it proves
--
--   W(M,commutator) = W(M,tangent) - W(M,variableDecay).
--
-- For any chosen common rate lambda, define the exact coherent residual
--
--   covarianceResidual = variableDecay + lambda M.
--
-- Then purely by linearity
--
--   W(M,commutator)
--     = W(M,tangent)
--       + lambda W(M,M)
--       - W(M,covarianceResidual).
--
-- Thus the fixed-output quantitative theorem is no longer an unspecified
-- vector estimate.  Its genuinely signed local content is the coherent
-- covariance work together with the endpoint/tangent payment.  Round229
-- remains authoritative: no favorable sign for this covariance is inferred
-- from cellwise nonnegative excess damping.
--
-- No inequality, time integration, endpoint bound, shell estimate, cutoff
-- aggregation, or Clay promotion is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a

F : C3.RealField _
F = Rational.rationalRealField

two : ℚ
two = 1ℚ + 1ℚ

coherentWork : C3.Complex3 F → C3.Complex3 F → ℚ
coherentWork left right = two * R179.realHermitianCross left right

fixedOutputMixedProduct :
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Nat → Z3.FourierMode → C3.Complex3 F
fixedOutputMixedProduct S velocity cutoff output =
  R224.foldVector (D1a.mixedProductCell S velocity)
    (Output.physicalOutputFiber cutoff output)

fixedOutputVariableDecay :
  (rho : Z3.FourierMode → C3.Carrier F) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Nat → Z3.FourierMode → C3.Complex3 F
fixedOutputVariableDecay rho S velocity cutoff output =
  R224.foldVector (D1a.variableDecayCell rho S velocity)
    (Output.physicalOutputFiber cutoff output)

fixedOutputDampedTangent :
  (rho : Z3.FourierMode → C3.Carrier F) →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  Nat → Z3.FourierMode → C3.Complex3 F
fixedOutputDampedTangent rho S velocity forcing cutoff output =
  R224.foldVector (D1a.dampedMixedTangentCell rho S velocity forcing)
    (Output.physicalOutputFiber cutoff output)

fixedOutputCommutator :
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  Nat → Z3.FourierMode → C3.Complex3 F
fixedOutputCommutator S velocity forcing cutoff output =
  R224.foldVector (R230.forcingCommutatorCell S velocity forcing)
    (Output.physicalOutputFiber cutoff output)

workAddRight :
  (left rightA rightB : C3.Complex3 F) →
  coherentWork left (C3.complex3Add rightA rightB)
  ≡ coherentWork left rightA + coherentWork left rightB
workAddRight left rightA rightB =
  trans
    (cong (two *_) (R291.realCrossAddRight left rightA rightB))
    (solve
      ( R179.realHermitianCross left rightA
      ∷ R179.realHermitianCross left rightB
      ∷ []))

workScaleRight :
  (scalar : ℚ) (left right : C3.Complex3 F) →
  coherentWork left (R291.realScale scalar right)
  ≡ scalar * coherentWork left right
workScaleRight scalar left right =
  trans
    (cong (two *_)
      (R291.scaledRealCrossRight scalar left right))
    (solve (scalar ∷ R179.realHermitianCross left right ∷ []))

fixedOutputTangentWorkIsDecayPlusCommutatorWork :
  (rho : Z3.FourierMode → C3.Carrier F) →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) (output : Z3.FourierMode) →
  let
    mixed = fixedOutputMixedProduct S velocity cutoff output
    tangent = fixedOutputDampedTangent rho S velocity forcing cutoff output
    decay = fixedOutputVariableDecay rho S velocity cutoff output
    commutator = fixedOutputCommutator S velocity forcing cutoff output
  in
  coherentWork mixed tangent
  ≡ coherentWork mixed decay + coherentWork mixed commutator
fixedOutputTangentWorkIsDecayPlusCommutatorWork
    rho S velocity forcing cutoff output =
  let
    mixed = fixedOutputMixedProduct S velocity cutoff output
    tangent = fixedOutputDampedTangent rho S velocity forcing cutoff output
    decay = fixedOutputVariableDecay rho S velocity cutoff output
    commutator = fixedOutputCommutator S velocity forcing cutoff output
    vectorSplit : tangent ≡ C3.complex3Add decay commutator
    vectorSplit =
      D1a.fixedOutputDampedTangentIsDecayPlusCommutator
        rho S velocity forcing cutoff output
  in
  trans
    (cong (coherentWork mixed) vectorSplit)
    (workAddRight mixed decay commutator)

fixedOutputCommutatorWorkIsTangentMinusDecay :
  (rho : Z3.FourierMode → C3.Carrier F) →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) (output : Z3.FourierMode) →
  let
    mixed = fixedOutputMixedProduct S velocity cutoff output
    tangent = fixedOutputDampedTangent rho S velocity forcing cutoff output
    decay = fixedOutputVariableDecay rho S velocity cutoff output
    commutator = fixedOutputCommutator S velocity forcing cutoff output
  in
  coherentWork mixed commutator
  ≡ coherentWork mixed tangent - coherentWork mixed decay
fixedOutputCommutatorWorkIsTangentMinusDecay
    rho S velocity forcing cutoff output =
  let
    mixed = fixedOutputMixedProduct S velocity cutoff output
    tangent = fixedOutputDampedTangent rho S velocity forcing cutoff output
    decay = fixedOutputVariableDecay rho S velocity cutoff output
    commutator = fixedOutputCommutator S velocity forcing cutoff output
    tangentWork = coherentWork mixed tangent
    decayWork = coherentWork mixed decay
    commutatorWork = coherentWork mixed commutator
    split : tangentWork ≡ decayWork + commutatorWork
    split = fixedOutputTangentWorkIsDecayPlusCommutatorWork
      rho S velocity forcing cutoff output
    shifted = cong (λ value → value - decayWork) split
    normalizeLeft : commutatorWork ≡ (decayWork + commutatorWork) - decayWork
    normalizeLeft = solve (decayWork ∷ commutatorWork ∷ [])
  in
  trans normalizeLeft (sym shifted)

coherentCovarianceResidual :
  ℚ → C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
coherentCovarianceResidual commonRate mixed decay =
  C3.complex3Add decay (R291.realScale commonRate mixed)

coherentResidualWorkSplit :
  (commonRate : ℚ) (mixed decay : C3.Complex3 F) →
  coherentWork mixed (coherentCovarianceResidual commonRate mixed decay)
  ≡ coherentWork mixed decay
    + commonRate * coherentWork mixed mixed
coherentResidualWorkSplit commonRate mixed decay =
  trans
    (workAddRight mixed decay (R291.realScale commonRate mixed))
    (cong (coherentWork mixed decay +_)
      (workScaleRight commonRate mixed mixed))

fixedOutputCommutatorWorkIsEndpointRateMinusCovariance :
  (commonRate : ℚ) →
  (rho : Z3.FourierMode → C3.Carrier F) →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) (output : Z3.FourierMode) →
  let
    mixed = fixedOutputMixedProduct S velocity cutoff output
    tangent = fixedOutputDampedTangent rho S velocity forcing cutoff output
    decay = fixedOutputVariableDecay rho S velocity cutoff output
    commutator = fixedOutputCommutator S velocity forcing cutoff output
    covarianceResidual = coherentCovarianceResidual commonRate mixed decay
  in
  coherentWork mixed commutator
  ≡ coherentWork mixed tangent
      + commonRate * coherentWork mixed mixed
      - coherentWork mixed covarianceResidual
fixedOutputCommutatorWorkIsEndpointRateMinusCovariance
    commonRate rho S velocity forcing cutoff output =
  let
    mixed = fixedOutputMixedProduct S velocity cutoff output
    tangent = fixedOutputDampedTangent rho S velocity forcing cutoff output
    decay = fixedOutputVariableDecay rho S velocity cutoff output
    commutator = fixedOutputCommutator S velocity forcing cutoff output
    residual = coherentCovarianceResidual commonRate mixed decay
    tangentWork = coherentWork mixed tangent
    decayWork = coherentWork mixed decay
    commutatorWork = coherentWork mixed commutator
    selfWork = coherentWork mixed mixed
    residualWork = coherentWork mixed residual
    first : commutatorWork ≡ tangentWork - decayWork
    first = fixedOutputCommutatorWorkIsTangentMinusDecay
      rho S velocity forcing cutoff output
    residualSplit : residualWork ≡ decayWork + commonRate * selfWork
    residualSplit = coherentResidualWorkSplit commonRate mixed decay
    normalize :
      tangentWork + commonRate * selfWork - residualWork
      ≡ tangentWork - decayWork
    normalize rewrite residualSplit =
      solve (tangentWork ∷ decayWork ∷ commonRate ∷ selfWork ∷ [])
  in
  trans first (sym normalize)

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

fixedOutputCommutatorWorkDecompositionClosed : Bool
fixedOutputCommutatorWorkDecompositionClosed = true

commonRateCoherentCovarianceIsolationClosed : Bool
commonRateCoherentCovarianceIsolationClosed = true

endpointTangentIntegrationInstalled : Bool
endpointTangentIntegrationInstalled = false

quantitativeCoherentCovariancePaymentClosed : Bool
quantitativeCoherentCovariancePaymentClosed = false

fixedOutputCommutatorWorkDecompositionClosedIsTrue :
  fixedOutputCommutatorWorkDecompositionClosed ≡ true
fixedOutputCommutatorWorkDecompositionClosedIsTrue = refl

commonRateCoherentCovarianceIsolationClosedIsTrue :
  commonRateCoherentCovarianceIsolationClosed ≡ true
commonRateCoherentCovarianceIsolationClosedIsTrue = refl

endpointTangentIntegrationInstalledIsFalse :
  endpointTangentIntegrationInstalled ≡ false
endpointTangentIntegrationInstalledIsFalse = refl

quantitativeCoherentCovariancePaymentClosedIsFalse :
  quantitativeCoherentCovariancePaymentClosed ≡ false
quantitativeCoherentCovariancePaymentClosedIsFalse = refl
