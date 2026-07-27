module DASHI.Physics.YangMills.BalabanClayT5PhysicalMassTransportExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- T5: exact physical-gap transport.
--
-- The recurrence is stated after conversion to physical units.  It is the
-- rigorous form of
--
--   m_k >= m_{k+1} - delta_k.
--
-- A positive terminal mass survives whenever the total interlacing defect is
-- strictly smaller than that terminal mass.
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
      let
        partial : Nat → ℚ
        partial zero = Data.Rational.0ℚ
        partial (suc depth) = partial depth + defect depth
      in partial terminalScale ≤ defectBudget

    survivalIdentity : survivingMass + defectBudget ≡ terminalMass

    SurvivingMassPositive : Set
    survivingMassPositive : SurvivingMassPositive

open PhysicalMassInterlacing public

partialDefect : PhysicalMassInterlacing → Nat → ℚ
partialDefect dataSet zero = Data.Rational.0ℚ
partialDefect dataSet (suc depth) =
  partialDefect dataSet depth + defect dataSet depth

gapAtDepthBelowInitialPlusDefects :
  (dataSet : PhysicalMassInterlacing) → ∀ depth →
  physicalGap dataSet depth
  ≤ physicalGap dataSet zero + partialDefect dataSet depth
gapAtDepthBelowInitialPlusDefects dataSet zero =
  subst
    (λ right → physicalGap dataSet zero ≤ right)
    (ℚRing.solve-∀ (physicalGap dataSet zero))
    (reflexive dataSet (physicalGap dataSet zero))
gapAtDepthBelowInitialPlusDefects dataSet (suc depth) =
  subst
    (λ right → physicalGap dataSet (suc depth) ≤ right)
    (ℚRing.solve-∀
      (physicalGap dataSet zero)
      (partialDefect dataSet depth)
      (defect dataSet depth))
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
      (survivalIdentity dataSet)
      (terminalMassBelowInitialPlusBudget dataSet))

------------------------------------------------------------------------
-- Dimensional transmutation normalization.
--
-- At the terminal scale a dimensionless lattice gap m_0 and inverse terminal
-- spacing Lambda produce the physical gap m_0 Lambda.  Keeping this equality
-- explicit prevents a dimensionless lattice bound from being mistaken for the
-- continuum mass statement.
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
    (subst
      (λ inverseScale →
        dimensionlessTerminalGap dataSet * inverseTerminalSpacing dataSet
        ≡ dimensionlessTerminalGap dataSet * inverseScale)
      (reciprocalScaleExact dataSet)
      (Agda.Builtin.Equality.refl))

physicalMassInterlacingFiniteSumLevel : ProofLevel
physicalMassInterlacingFiniteSumLevel = machineChecked

positiveMassAfterSummableDefectsLevel : ProofLevel
positiveMassAfterSummableDefectsLevel = machineChecked

dimensionalTransmutationNormalizationLevel : ProofLevel
dimensionalTransmutationNormalizationLevel = machineChecked

-- The remaining physical theorem is to derive the interlacing inequality and
-- summable defect bound from the reflection-positive RG transfer operator, and
-- to identify the terminal inverse spacing with the generated Lambda_YM scale.
physicalTransferOperatorInterlacingLevel : ProofLevel
physicalTransferOperatorInterlacingLevel = conditional
