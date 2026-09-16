module DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact where

------------------------------------------------------------------------
-- S2b2d1a / FIXED-OUTPUT COMMUTATOR AS DAMPED-TANGENT RESIDUAL
--
-- #957 removes the periodic collar selector on an active fixed-output fibre:
-- the hard local object is the ordinary unweighted R230 mixed commutator.
--
-- R231 already proves, cellwise, that the tangent of the mixed-helicity
-- product is exactly
--
--   viscous decay + product-rule forcing.
--
-- R230 proves that after complete fixed-output summation the product-rule
-- forcing is exactly the signed mixed commutator.  Combining those two exact
-- identities gives
--
--   sum tangent = sum variable viscous decay + sum commutator.
--
-- Thus d1 is not an unspecified pointwise commutator estimate.  Its remaining
-- analytic content is the signed/coherent control needed to compare the
-- variable-rate viscous fold and the endpoint/tangent fold.  R229 proves that
-- cellwise nonnegative viscous excesses alone do NOT provide this after
-- coherent summation.
--
-- No norm estimate, half-derivative gain, shell estimate, endpoint bound,
-- covariance payment, cutoff aggregation, or Clay promotion is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityViscousCovarianceNoGoRound229Exact as R229
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNMixedHelicityDampedProductTangentRound231Exact as R231

plusVelocity :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
plusVelocity {E = E} {I = I} S velocity tau =
  Helical.helicalProjectorPlus E I S
    (Physical.p tau) (velocity (Physical.p tau))

minusVelocity :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
minusVelocity {E = E} {I = I} S velocity tau =
  Helical.helicalProjectorMinus E I S
    (Physical.q tau) (velocity (Physical.q tau))

plusForcing :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (S : Helical.HelicalModeScalars F) →
  (forcing : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
plusForcing {E = E} {I = I} S forcing tau =
  Helical.helicalProjectorPlus E I S
    (Physical.p tau) (forcing (Physical.p tau))

minusForcing :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (S : Helical.HelicalModeScalars F) →
  (forcing : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
minusForcing {E = E} {I = I} S forcing tau =
  Helical.helicalProjectorMinus E I S
    (Physical.q tau) (forcing (Physical.q tau))

mixedProductCell :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
mixedProductCell S velocity tau =
  R231.mixedProduct
    (plusVelocity S velocity tau)
    (minusVelocity S velocity tau)

variableDecayCell :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (rho : Z3.FourierMode → C3.Carrier F) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
variableDecayCell rho S velocity tau =
  C3.complex3Scale
    (R231.twoModeNegativeDecay
      (rho (Physical.p tau)) (rho (Physical.q tau)))
    (mixedProductCell S velocity tau)

dampedMixedTangentCell :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (rho : Z3.FourierMode → C3.Carrier F) →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
dampedMixedTangentCell rho S velocity forcing tau =
  R231.mixedProductTangent
    (plusVelocity S velocity tau)
    (minusVelocity S velocity tau)
    (R94.dampedPlusForcing
      (rho (Physical.p tau))
      (plusVelocity S velocity tau)
      (plusForcing S forcing tau))
    (R94.dampedPlusForcing
      (rho (Physical.q tau))
      (minusVelocity S velocity tau)
      (minusForcing S forcing tau))

cellDampedTangentIsDecayPlusProductRule :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (rho : Z3.FourierMode → C3.Carrier F) →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  (tau : Physical.PhysicalTriadIncidence) →
  dampedMixedTangentCell rho S velocity forcing tau
  ≡ C3.complex3Add
      (variableDecayCell rho S velocity tau)
      (R230.productRuleForcingCell S velocity forcing tau)
cellDampedTangentIsDecayPlusProductRule rho S velocity forcing tau =
  R231.mixedProductDampedNetworkEquation
    (rho (Physical.p tau))
    (rho (Physical.q tau))
    (plusVelocity S velocity tau)
    (minusVelocity S velocity tau)
    (plusForcing S forcing tau)
    (minusForcing S forcing tau)

foldPointwiseDampedEquation :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (rho : Z3.FourierMode → C3.Carrier F) →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  R224.foldVector (dampedMixedTangentCell rho S velocity forcing) items
  ≡ C3.complex3Add
      (R224.foldVector (variableDecayCell rho S velocity) items)
      (R224.foldVector (R230.productRuleForcingCell S velocity forcing) items)
foldPointwiseDampedEquation {F = F} rho S velocity forcing [] =
  sym (R230.complex3AddZeroLeft (C3.complex3Zero F))
foldPointwiseDampedEquation rho S velocity forcing (tau ∷ rest) =
  trans
    (cong₂ C3.complex3Add
      (cellDampedTangentIsDecayPlusProductRule rho S velocity forcing tau)
      (foldPointwiseDampedEquation rho S velocity forcing rest))
    (R230.complex3Shuffle
      (variableDecayCell rho S velocity tau)
      (R230.productRuleForcingCell S velocity forcing tau)
      (R224.foldVector (variableDecayCell rho S velocity) rest)
      (R224.foldVector (R230.productRuleForcingCell S velocity forcing) rest))

fixedOutputDampedTangentIsDecayPlusCommutator :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (rho : Z3.FourierMode → C3.Carrier F) →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) (output : Z3.FourierMode) →
  R224.foldVector (dampedMixedTangentCell rho S velocity forcing)
    (Output.physicalOutputFiber cutoff output)
  ≡ C3.complex3Add
      (R224.foldVector (variableDecayCell rho S velocity)
        (Output.physicalOutputFiber cutoff output))
      (R224.foldVector (R230.forcingCommutatorCell S velocity forcing)
        (Output.physicalOutputFiber cutoff output))
fixedOutputDampedTangentIsDecayPlusCommutator
    rho S velocity forcing cutoff output =
  trans
    (foldPointwiseDampedEquation rho S velocity forcing
      (Output.physicalOutputFiber cutoff output))
    (cong₂ C3.complex3Add refl
      (R230.fixedOutputProductRuleForcingIsMixedCommutator
        S velocity forcing cutoff output))

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

fixedOutputDampedTangentDecompositionClosed : Bool
fixedOutputDampedTangentDecompositionClosed = true

fixedOutputCommutatorDynamicResidualIdentified : Bool
fixedOutputCommutatorDynamicResidualIdentified = true

-- Round229 is an explicit finite counterexample: nonnegative cellwise excess
-- damping does not imply favorable coherent damping after summation.
cellwiseDampingLowerBoundPaysCoherentFixedOutput : Bool
cellwiseDampingLowerBoundPaysCoherentFixedOutput =
  R229.round229CellwiseViscousLowerBoundImpliesCoherentDamping

remainingD1LeafIsSignedCoherentCovarianceOrEquivalent : Bool
remainingD1LeafIsSignedCoherentCovarianceOrEquivalent = true

d1QuantitativePaymentClosed : Bool
d1QuantitativePaymentClosed = false

fixedOutputDampedTangentDecompositionClosedIsTrue :
  fixedOutputDampedTangentDecompositionClosed ≡ true
fixedOutputDampedTangentDecompositionClosedIsTrue = refl

fixedOutputCommutatorDynamicResidualIdentifiedIsTrue :
  fixedOutputCommutatorDynamicResidualIdentified ≡ true
fixedOutputCommutatorDynamicResidualIdentifiedIsTrue = refl

cellwiseDampingLowerBoundPaysCoherentFixedOutputIsFalse :
  cellwiseDampingLowerBoundPaysCoherentFixedOutput ≡ false
cellwiseDampingLowerBoundPaysCoherentFixedOutputIsFalse =
  R229.round229CellwiseViscousLowerBoundImpliesCoherentDampingIsFalse

remainingD1LeafIsSignedCoherentCovarianceOrEquivalentIsTrue :
  remainingD1LeafIsSignedCoherentCovarianceOrEquivalent ≡ true
remainingD1LeafIsSignedCoherentCovarianceOrEquivalentIsTrue = refl

d1QuantitativePaymentClosedIsFalse :
  d1QuantitativePaymentClosed ≡ false
d1QuantitativePaymentClosedIsFalse = refl
