module DASHI.Physics.YangMills.BalabanClayT5PhysicalMassTransportExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

partialFrom : (Nat → ℚ) → Nat → ℚ
partialFrom sequence zero = 0ℚ
partialFrom sequence (suc depth) =
  partialFrom sequence depth + sequence depth

------------------------------------------------------------------------
-- T5: exact physical-gap transport.
------------------------------------------------------------------------

record PhysicalMassInterlacing : Set₁ where
  field
    physicalGap defect : Nat → ℚ
    terminalScale : Nat

    terminalMass defectBudget survivingMass : ℚ

    reflexive : ∀ value → value ≤ value
    transitive : ∀ {left middle right} →
      left ≤ middle → middle ≤ right → left ≤ right
    addMonotone : ∀ {left leftUpper right rightUpper} →
      left ≤ leftUpper → right ≤ rightUpper →
      left + right ≤ leftUpper + rightUpper
    addRightCancel : ∀ {left right common} →
      left + common ≤ right + common → left ≤ right

    oneStepInterlacing : ∀ depth →
      physicalGap (suc depth) ≤ physicalGap depth + defect depth

    TerminalMassPositive : Set
    terminalMassPositive : TerminalMassPositive

    terminalGapDominates : terminalMass ≤ physicalGap terminalScale

    defectPartialBound :
      partialFrom defect terminalScale ≤ defectBudget

    survivalIdentity : survivingMass + defectBudget ≡ terminalMass

    SurvivingMassPositive : Set
    survivingMassPositive : SurvivingMassPositive

open PhysicalMassInterlacing public

partialDefect : PhysicalMassInterlacing → Nat → ℚ
partialDefect dataSet = partialFrom (defect dataSet)

gapAtDepthBelowInitialPlusDefects :
  (dataSet : PhysicalMassInterlacing) → ∀ depth →
  physicalGap dataSet depth
  ≤ physicalGap dataSet zero + partialDefect dataSet depth
gapAtDepthBelowInitialPlusDefects dataSet zero =
  subst
    (λ right → physicalGap dataSet zero ≤ right)
    (ℚRing.solve-∀)
    (reflexive dataSet (physicalGap dataSet zero))
gapAtDepthBelowInitialPlusDefects dataSet (suc depth) =
  subst
    (λ right → physicalGap dataSet (suc depth) ≤ right)
    (ℚRing.solve-∀)
    (transitive dataSet
      (oneStepInterlacing dataSet depth)
      (addMonotone dataSet
        (gapAtDepthBelowInitialPlusDefects dataSet depth)
        (reflexive dataSet (defect dataSet depth))))

terminalMassBelowInitialPlusBudget :
  (dataSet : PhysicalMassInterlacing) →
  terminalMass dataSet
  ≤ physicalGap dataSet zero + defectBudget dataSet
terminalMassBelowInitialPlusBudget dataSet =
  transitive dataSet
    (terminalGapDominates dataSet)
    (transitive dataSet
      (gapAtDepthBelowInitialPlusDefects dataSet (terminalScale dataSet))
      (addMonotone dataSet
        (reflexive dataSet (physicalGap dataSet zero))
        (defectPartialBound dataSet)))

positivePhysicalMassSurvives :
  (dataSet : PhysicalMassInterlacing) →
  survivingMass dataSet ≤ physicalGap dataSet zero
positivePhysicalMassSurvives dataSet =
  addRightCancel dataSet
    (subst
      (λ left →
        left ≤ physicalGap dataSet zero + defectBudget dataSet)
      (sym (survivalIdentity dataSet))
      (terminalMassBelowInitialPlusBudget dataSet))

------------------------------------------------------------------------
-- Dimensional transmutation normalization.
------------------------------------------------------------------------

terminalPhysicalMass : ℚ → ℚ → ℚ
terminalPhysicalMass dimensionlessGap inverseTerminalSpacing =
  dimensionlessGap * inverseTerminalSpacing

record DimensionalTransmutationWitness : Set₁ where
  field
    terminalSpacing inverseTerminalSpacing lambdaYM : ℚ
    dimensionlessTerminalGap physicalTerminalGap : ℚ

    reciprocalScaleExact :
      inverseTerminalSpacing ≡ lambdaYM

    physicalGapDefinition :
      physicalTerminalGap
      ≡ terminalPhysicalMass dimensionlessTerminalGap inverseTerminalSpacing

open DimensionalTransmutationWitness public

terminalGapIsLambdaMultiple :
  (dataSet : DimensionalTransmutationWitness) →
  physicalTerminalGap dataSet
  ≡ dimensionlessTerminalGap dataSet * lambdaYM dataSet
terminalGapIsLambdaMultiple dataSet =
  trans
    (physicalGapDefinition dataSet)
    (cong (dimensionlessTerminalGap dataSet *_) (reciprocalScaleExact dataSet))

physicalMassInterlacingFiniteSumLevel : ProofLevel
physicalMassInterlacingFiniteSumLevel = machineChecked

positiveMassAfterSummableDefectsLevel : ProofLevel
positiveMassAfterSummableDefectsLevel = machineChecked

dimensionalTransmutationNormalizationLevel : ProofLevel
dimensionalTransmutationNormalizationLevel = machineChecked

physicalTransferOperatorInterlacingLevel : ProofLevel
physicalTransferOperatorInterlacingLevel = conditional
