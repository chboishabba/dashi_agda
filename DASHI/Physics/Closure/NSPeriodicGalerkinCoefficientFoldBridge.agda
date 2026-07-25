module DASHI.Physics.Closure.NSPeriodicGalerkinCoefficientFoldBridge where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.Closure.NSWall1ExactEvaluationCarrier using (Vec3)
import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteOfficialNormWeights as Weights
import DASHI.Physics.Closure.NSPeriodicOfficialFiniteSumIdentification as Official
import DASHI.Physics.Closure.NSPeriodicConcreteModeOperatorPythagorean as Concrete
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- One coefficient owner for an existing periodic Galerkin state.
--
-- An application supplies its actual state and coefficient extraction, one
-- concrete weight package, and exact equations identifying its physical L2,
-- homogeneous-H1 and shell quantities with the official literal finite folds.
-- No second enumerator, Parseval convention, or shell norm can enter here.
------------------------------------------------------------------------

record GalerkinCoefficientFoldBridge
    {s : Level}
    (O : Concrete.RealOrderCancellationAuthority)
    (State : Set s) : Set (lsuc s) where
  field
    cutoff : State → Nat

    velocityCoefficient :
      State → Z3.FourierMode → Vec3 ℝ

    vorticityCoefficient :
      State → Z3.FourierMode → Vec3 ℝ

    physicalL2Squared physicalHomogeneousH1Squared : State → ℝ
    physicalShellL2Squared : State → Nat → ℝ

    coefficientWeights : State →
      Weights.ConcreteCoefficientUnitaryWeightInputs
        (Concrete.realNormArithmetic O)

    coefficientExtractionMeaning : Set s
    coefficientExtractionIsActual : coefficientExtractionMeaning

    l2FoldMeaning : ∀ state →
      physicalL2Squared state
      ≡ Official.officialL2Squared
          (Weights.concreteCoefficientUnitaryNormCarrier
            (coefficientWeights state))
          (cutoff state)

    h1FoldMeaning : ∀ state →
      physicalHomogeneousH1Squared state
      ≡ Official.officialHomogeneousH1Squared
          (Weights.concreteCoefficientUnitaryNormCarrier
            (coefficientWeights state))
          (cutoff state)

    shellFoldMeaning : ∀ state shell →
      physicalShellL2Squared state shell
      ≡ Official.officialShellL2Squared
          (Weights.concreteCoefficientUnitaryNormCarrier
            (coefficientWeights state))
          (cutoff state)
          shell

    divergenceFreeCoefficientIdentity : Set s
    divergenceFreeCoefficients : divergenceFreeCoefficientIdentity

    vorticityCurlCoefficientIdentity : Set s
    vorticityCurlCoefficients : vorticityCurlCoefficientIdentity

    biotSavartInverseCoefficientIdentity : Set s
    biotSavartInverseCoefficients : biotSavartInverseCoefficientIdentity

open GalerkinCoefficientFoldBridge public

officialCarrier :
  ∀ {s} {O : Concrete.RealOrderCancellationAuthority} {State : Set s} →
  GalerkinCoefficientFoldBridge O State → State →
  Official.ConcreteFiniteFourierNormCarrier
    (Concrete.realNormArithmetic O)
officialCarrier G state =
  Weights.concreteCoefficientUnitaryNormCarrier
    (coefficientWeights G state)

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
