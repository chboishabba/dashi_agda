module DASHI.Physics.Closure.NSPeriodicOfficialOperatorFoldIdentification where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSWall1ExactEvaluationCarrier using (Vec3)
import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSPeriodicConcreteIntegerModeNorm as ModeNorm
import DASHI.Physics.Closure.NSPeriodicConcreteModeOperatorPythagorean as Concrete
import DASHI.Physics.Closure.NSPeriodicFinitePythagoreanSum as Finite
import DASHI.Physics.Closure.NSPeriodicOfficialFiniteSumIdentification as Official
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- The official finite-norm module and the Pythagorean transport module use
-- extensionally identical recursive folds.  This theorem prevents those two
-- definitions from becoming independent norm owners.
------------------------------------------------------------------------

finitePythagoreanFoldIsOfficialFold :
  ∀ {A : AbsorptionArithmetic} {Item : Set}
    (weight : Item → Scalar A) (items : List Item) →
  Finite.sumBy weight items ≡ Official.sumBy weight items
finitePythagoreanFoldIsOfficialFold weight [] = refl
finitePythagoreanFoldIsOfficialFold {A = A} weight (item ∷ items) =
  cong
    (λ tail → _+_ A (weight item) tail)
    (finitePythagoreanFoldIsOfficialFold weight items)

------------------------------------------------------------------------
-- Literal operator folds over the exact cutoff cube are therefore official
-- finite folds, not merely numerically equal quantities from a second list.
------------------------------------------------------------------------

lerayInputIsOfficialFold :
  (O : Concrete.RealOrderCancellationAuthority) →
  (A : ModeNorm.ConcretePeriodicModeNormAuthority) →
  (N : Nat) →
  (coefficient : Z3.FourierMode → Vec3 ℝ) →
  Concrete.lerayInputCutoffSum O A N coefficient
  ≡
  Official.sumBy
    (Concrete.lerayModeInput A coefficient)
    (Cube.cutoffModes N)
lerayInputIsOfficialFold O A N coefficient =
  finitePythagoreanFoldIsOfficialFold
    (Concrete.lerayModeInput A coefficient)
    (Cube.cutoffModes N)

lerayOutputIsOfficialFold :
  (O : Concrete.RealOrderCancellationAuthority) →
  (A : ModeNorm.ConcretePeriodicModeNormAuthority) →
  (N : Nat) →
  (coefficient : Z3.FourierMode → Vec3 ℝ) →
  Concrete.lerayOutputCutoffSum O A N coefficient
  ≡
  Official.sumBy
    (Concrete.lerayModeOutput A coefficient)
    (Cube.cutoffModes N)
lerayOutputIsOfficialFold O A N coefficient =
  finitePythagoreanFoldIsOfficialFold
    (Concrete.lerayModeOutput A coefficient)
    (Cube.cutoffModes N)

lerayComplementIsOfficialFold :
  (O : Concrete.RealOrderCancellationAuthority) →
  (A : ModeNorm.ConcretePeriodicModeNormAuthority) →
  (N : Nat) →
  (coefficient : Z3.FourierMode → Vec3 ℝ) →
  Concrete.lerayComplementCutoffSum O A N coefficient
  ≡
  Official.sumBy
    (Concrete.lerayModeComplement A coefficient)
    (Cube.cutoffModes N)
lerayComplementIsOfficialFold O A N coefficient =
  finitePythagoreanFoldIsOfficialFold
    (Concrete.lerayModeComplement A coefficient)
    (Cube.cutoffModes N)

biotSavartInputIsOfficialFold :
  (O : Concrete.RealOrderCancellationAuthority) →
  (A : ModeNorm.ConcretePeriodicModeNormAuthority) →
  (N : Nat) →
  (coefficient : Z3.FourierMode → Vec3 ℝ) →
  Concrete.biotSavartInputCutoffSum O A N coefficient
  ≡
  Official.sumBy
    (Concrete.biotSavartModeInput A coefficient)
    (Cube.cutoffModes N)
biotSavartInputIsOfficialFold O A N coefficient =
  finitePythagoreanFoldIsOfficialFold
    (Concrete.biotSavartModeInput A coefficient)
    (Cube.cutoffModes N)

biotSavartOutputIsOfficialFold :
  (O : Concrete.RealOrderCancellationAuthority) →
  (A : ModeNorm.ConcretePeriodicModeNormAuthority) →
  (N : Nat) →
  (coefficient : Z3.FourierMode → Vec3 ℝ) →
  Concrete.biotSavartOutputCutoffSum O A N coefficient
  ≡
  Official.sumBy
    (Concrete.biotSavartModeOutput A coefficient)
    (Cube.cutoffModes N)
biotSavartOutputIsOfficialFold O A N coefficient =
  finitePythagoreanFoldIsOfficialFold
    (Concrete.biotSavartModeOutput A coefficient)
    (Cube.cutoffModes N)

biotSavartComplementIsOfficialFold :
  (O : Concrete.RealOrderCancellationAuthority) →
  (A : ModeNorm.ConcretePeriodicModeNormAuthority) →
  (N : Nat) →
  (coefficient : Z3.FourierMode → Vec3 ℝ) →
  Concrete.biotSavartComplementCutoffSum O A N coefficient
  ≡
  Official.sumBy
    (Concrete.biotSavartModeComplement A coefficient)
    (Cube.cutoffModes N)
biotSavartComplementIsOfficialFold O A N coefficient =
  finitePythagoreanFoldIsOfficialFold
    (Concrete.biotSavartModeComplement A coefficient)
    (Cube.cutoffModes N)

record OfficialOperatorFoldIdentification
    (O : Concrete.RealOrderCancellationAuthority)
    (A : ModeNorm.ConcretePeriodicModeNormAuthority)
    (N : Nat)
    (velocityCoefficient vorticityCoefficient :
      Z3.FourierMode → Vec3 ℝ) : Set where
  field
    leray-input-is-official :
      Concrete.lerayInputCutoffSum O A N velocityCoefficient
      ≡ Official.sumBy
          (Concrete.lerayModeInput A velocityCoefficient)
          (Cube.cutoffModes N)

    leray-output-is-official :
      Concrete.lerayOutputCutoffSum O A N velocityCoefficient
      ≡ Official.sumBy
          (Concrete.lerayModeOutput A velocityCoefficient)
          (Cube.cutoffModes N)

    biot-savart-input-is-official :
      Concrete.biotSavartInputCutoffSum O A N vorticityCoefficient
      ≡ Official.sumBy
          (Concrete.biotSavartModeInput A vorticityCoefficient)
          (Cube.cutoffModes N)

    biot-savart-output-is-official :
      Concrete.biotSavartOutputCutoffSum O A N vorticityCoefficient
      ≡ Official.sumBy
          (Concrete.biotSavartModeOutput A vorticityCoefficient)
          (Cube.cutoffModes N)

open OfficialOperatorFoldIdentification public

officialOperatorFoldIdentification :
  (O : Concrete.RealOrderCancellationAuthority) →
  (A : ModeNorm.ConcretePeriodicModeNormAuthority) →
  (N : Nat) →
  (velocityCoefficient vorticityCoefficient :
    Z3.FourierMode → Vec3 ℝ) →
  OfficialOperatorFoldIdentification
    O A N velocityCoefficient vorticityCoefficient
officialOperatorFoldIdentification O A N velocityCoefficient vorticityCoefficient =
  record
    { leray-input-is-official =
        lerayInputIsOfficialFold O A N velocityCoefficient
    ; leray-output-is-official =
        lerayOutputIsOfficialFold O A N velocityCoefficient
    ; biot-savart-input-is-official =
        biotSavartInputIsOfficialFold O A N vorticityCoefficient
    ; biot-savart-output-is-official =
        biotSavartOutputIsOfficialFold O A N vorticityCoefficient
    }

------------------------------------------------------------------------
-- Status: enumeration, norm weights, and the concrete operator inequalities now
-- use one recursive finite-fold owner over the same literal cube.
------------------------------------------------------------------------

officialOperatorFoldIdentificationLevel : ProofLevel
officialOperatorFoldIdentificationLevel = machineChecked
