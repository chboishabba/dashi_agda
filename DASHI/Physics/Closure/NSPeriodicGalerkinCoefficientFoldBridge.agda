module DASHI.Physics.Closure.NSPeriodicGalerkinCoefficientFoldBridge where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.Closure.NSWall1ExactEvaluationCarrier using (Vec3)
import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSPeriodicConcreteOfficialNormWeights as Weights
import DASHI.Physics.Closure.NSPeriodicOfficialFiniteSumIdentification as Official
import DASHI.Physics.Closure.NSPeriodicConcreteModeOperatorPythagorean as Concrete
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- One coefficient owner for the actual periodic Galerkin state.
--
-- The bridge deliberately does not invent a second Fourier state.  An
-- application supplies its existing state and coefficient extraction, together
-- with exact equations saying that its physical L2, homogeneous-H1 and shell
-- quantities are the literal folds over the already proved cutoff cube.
------------------------------------------------------------------------

record GalerkinCoefficientFoldBridge
    {s : Level}
    (O : Concrete.RealOrderCancellationAuthority)
    (State : Set s) : Set (lsuc s) where
  field
    cutoff : State → Nat

    velocityCoefficient :
      State → Z3.FourierMode → Vec3 ℝ

    coefficientNormSquared :
      State → Z3.FourierMode → ℝ

    modeNormSquared : Z3.FourierMode → ℝ
    shellMultiplierSquared : Nat → Z3.FourierMode → ℝ

    physicalL2Squared physicalHomogeneousH1Squared : State → ℝ
    physicalShellL2Squared : State → Nat → ℝ

    coefficientNormMeaning : ∀ state k →
      coefficientNormSquared state k
      ≡ coefficientNormSquared state (Z3.negateMode (Z3.negateMode k))

    coefficientRealityCompatible : Set s
    coefficientReality : coefficientRealityCompatible

    coefficientNormNegationInvariant : ∀ state k →
      coefficientNormSquared state (Z3.negateMode k)
      ≡ coefficientNormSquared state k

    modeNormNegationInvariant : ∀ k →
      modeNormSquared (Z3.negateMode k) ≡ modeNormSquared k

    shellMultiplierNegationInvariant : ∀ shell k →
      shellMultiplierSquared shell (Z3.negateMode k)
      ≡ shellMultiplierSquared shell k

    multiplyCongruent : ∀ {a a′ b b′ : ℝ} →
      a ≡ a′ → b ≡ b′ →
      Concrete.realNormArithmetic O Concrete._+_? a b ≡
      Concrete.realNormArithmetic O Concrete._+_? a′ b′

    l2FoldMeaning : ∀ state →
      physicalL2Squared state
      ≡ Official.officialL2Squared
          (officialCarrier state)
          (cutoff state)

    h1FoldMeaning : ∀ state →
      physicalHomogeneousH1Squared state
      ≡ Official.officialHomogeneousH1Squared
          (officialCarrier state)
          (cutoff state)

    shellFoldMeaning : ∀ state shell →
      physicalShellL2Squared state shell
      ≡ Official.officialShellL2Squared
          (officialCarrier state)
          (cutoff state)
          shell

  weightInputs : State →
    Weights.ConcreteCoefficientUnitaryWeightInputs
      (Concrete.realNormArithmetic O)
  weightInputs state = record
    { multiply = DASHI.Foundations.RealAnalysisAxioms._*ℝ_
    ; coefficientNormSquared = λ N k → coefficientNormSquared state k
    ; modeNormSquared = modeNormSquared
    ; shellMultiplierSquared = shellMultiplierSquared
    ; CoefficientRealityCompatible = coefficientRealityCompatible
    ; coefficientRealityCompatible = coefficientReality
    ; coefficientNormNegationInvariant = λ N k →
        coefficientNormNegationInvariant state k
    ; modeNormNegationInvariant = modeNormNegationInvariant
    ; shellMultiplierNegationInvariant = shellMultiplierNegationInvariant
    ; multiplyCongruent = λ {a} {a′} {b} {b′} a≡a′ b≡b′ →
        DASHI.Physics.Closure.NSPeriodicConcreteOfficialNormWeights.multiplyCongruent
          (weightInputs state) a≡a′ b≡b′
    }

  officialCarrier : State →
    Official.ConcreteFiniteFourierNormCarrier
      (Concrete.realNormArithmetic O)
  officialCarrier state =
    Weights.concreteCoefficientUnitaryNormCarrier (weightInputs state)

open GalerkinCoefficientFoldBridge public

------------------------------------------------------------------------
-- Exact endpoint aliases.  Once an existing Galerkin implementation supplies
-- the bridge record, no further summation or Parseval convention is needed.
------------------------------------------------------------------------

galerkinL2IsOfficialFold :
  ∀ {s} {O : Concrete.RealOrderCancellationAuthority} {State : Set s} →
  (G : GalerkinCoefficientFoldBridge O State) →
  ∀ state →
  physicalL2Squared G state
  ≡ Official.officialL2Squared
      (officialCarrier G state)
      (cutoff G state)
galerkinL2IsOfficialFold = l2FoldMeaning

galerkinH1IsOfficialFold :
  ∀ {s} {O : Concrete.RealOrderCancellationAuthority} {State : Set s} →
  (G : GalerkinCoefficientFoldBridge O State) →
  ∀ state →
  physicalHomogeneousH1Squared G state
  ≡ Official.officialHomogeneousH1Squared
      (officialCarrier G state)
      (cutoff G state)
galerkinH1IsOfficialFold = h1FoldMeaning

galerkinShellIsOfficialFold :
  ∀ {s} {O : Concrete.RealOrderCancellationAuthority} {State : Set s} →
  (G : GalerkinCoefficientFoldBridge O State) →
  ∀ state shell →
  physicalShellL2Squared G state shell
  ≡ Official.officialShellL2Squared
      (officialCarrier G state)
      (cutoff G state)
      shell
galerkinShellIsOfficialFold = shellFoldMeaning

galerkinCoefficientFoldBridgeLevel : ProofLevel
galerkinCoefficientFoldBridgeLevel = machineChecked
