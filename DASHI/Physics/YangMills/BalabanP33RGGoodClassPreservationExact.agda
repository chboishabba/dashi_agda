module DASHI.Physics.YangMills.BalabanP33RGGoodClassPreservationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Tadeusz Balaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II".
-- DOI: 10.1007/BF01240221.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban III. Convergence".
-- DOI: 10.1007/s00023-013-0303-3.
--
-- Volker Bach, Thomas Chen, Juerg Froehlich and Israel Michael Sigal,
-- "Smooth Feshbach Map and Operator-Theoretic Renormalization Group Methods".
-- DOI: 10.1016/S0022-1236(03)00057-0.
--
-- DASHI CONTRIBUTION
-- Make the intended scale-uniform induction object literal. A good scale
-- records a coercive floor, Hessian row mass, normalized stencil range,
-- coarse--fine coupling amplitude and remainder size under fixed caps.
-- A producer for one scale contains the next values and proofs that every cap
-- is retained. Preservation is therefore an actual dependent construction.
--
-- The remainder contraction is checked exactly for two steps:
-- delta1 = theta delta0 and delta2 = theta delta1 imply
-- delta2 = theta^2 delta0. Physical producers for the caps and theta<2 are
-- not fabricated.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)

data ScaleLabel : Set where
  scaleZero : ScaleLabel
  nextScale : ScaleLabel → ScaleLabel

record RGGoodParameters : Set where
  constructor rgGoodParameters
  field
    coerciveFloorCap : ℚ
    rowMassCap : ℚ
    stencilRangeCap : Nat
    couplingAmplitudeCap : ℚ
    remainderCap : ℚ

open RGGoodParameters public

record RGScaleState (scale : ScaleLabel) : Set where
  constructor rgScaleState
  field
    coerciveFloor : ℚ
    rowMass : ℚ
    stencilRange : Nat
    couplingAmplitude : ℚ
    remainderSize : ℚ

open RGScaleState public

record GoodScale
    (parameters : RGGoodParameters)
    (scale : ScaleLabel) : Set where
  constructor goodScale
  field
    state : RGScaleState scale
    coerciveFloorRetained :
      coerciveFloorCap parameters ≤ coerciveFloor state
    rowMassControlled : rowMass state ≤ rowMassCap parameters
    stencilRangeControlled : stencilRange state ≡ stencilRangeCap parameters
    couplingAmplitudeControlled :
      couplingAmplitude state ≤ couplingAmplitudeCap parameters
    remainderControlled : remainderSize state ≤ remainderCap parameters

open GoodScale public

record RGGoodStep
    (parameters : RGGoodParameters)
    (scale : ScaleLabel)
    (current : GoodScale parameters scale) : Set where
  constructor rgGoodStep
  field
    nextState : RGScaleState (nextScale scale)
    nextCoerciveFloorRetained :
      coerciveFloorCap parameters ≤ coerciveFloor nextState
    nextRowMassControlled : rowMass nextState ≤ rowMassCap parameters
    nextStencilRangeControlled :
      stencilRange nextState ≡ stencilRangeCap parameters
    nextCouplingAmplitudeControlled :
      couplingAmplitude nextState ≤ couplingAmplitudeCap parameters
    nextRemainderControlled :
      remainderSize nextState ≤ remainderCap parameters

open RGGoodStep public

preserveGoodClass :
  ∀ parameters scale
    (current : GoodScale parameters scale) →
  RGGoodStep parameters scale current →
  GoodScale parameters (nextScale scale)
preserveGoodClass parameters scale current step =
  goodScale
    (nextState step)
    (nextCoerciveFloorRetained step)
    (nextRowMassControlled step)
    (nextStencilRangeControlled step)
    (nextCouplingAmplitudeControlled step)
    (nextRemainderControlled step)

record ExactRemainderContraction : Set where
  constructor exactRemainderContraction
  field
    theta deltaZero deltaOne deltaTwo : ℚ
    firstContraction : deltaOne ≡ theta * deltaZero
    secondContraction : deltaTwo ≡ theta * deltaOne

open ExactRemainderContraction public

twoStepRemainderContractionDirect :
  ∀ theta deltaZero deltaOne deltaTwo →
  deltaOne ≡ theta * deltaZero →
  deltaTwo ≡ theta * deltaOne →
  deltaTwo ≡ (theta * theta) * deltaZero
twoStepRemainderContractionDirect
  theta deltaZero .(theta * deltaZero)
  .(theta * (theta * deltaZero)) refl refl =
  solve (theta ∷ deltaZero ∷ [])

twoStepRemainderContraction :
  (chain : ExactRemainderContraction) →
  deltaTwo chain
  ≡ (theta chain * theta chain) * deltaZero chain
twoStepRemainderContraction chain =
  twoStepRemainderContractionDirect
    (theta chain)
    (deltaZero chain)
    (deltaOne chain)
    (deltaTwo chain)
    (firstContraction chain)
    (secondContraction chain)

record RGGoodClassBoundary : Set where
  constructor rgGoodClassBoundary
  field
    abstractPreservationSuppliesPhysicalNextStep : Set
    abstractPreservationDoesNotSupplyPhysicalNextStep :
      abstractPreservationSuppliesPhysicalNextStep → Set

    exactContractionSuppliesThetaBelowTwo : Set
    exactContractionDoesNotSupplyThetaBelowTwo :
      exactContractionSuppliesThetaBelowTwo → Set

canonicalRGGoodClassBoundary : RGGoodClassBoundary
canonicalRGGoodClassBoundary =
  rgGoodClassBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
