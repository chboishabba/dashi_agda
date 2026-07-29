module DASHI.Physics.YangMills.BalabanClayGate4AnalyticityRadiusCouplingControlExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- Secondary locator only, not theorem authority:
-- Lluis Eriksson, "Exponential Clustering and Mass Gap for Four-Dimensional
-- SU(N) Lattice Yang--Mills Theory Via Balaban's Renormalization Group and
-- Multiscale Correlator Decoupling -- a Conditional Clustering Theorem --",
-- ai.viXra:2602.0088v3 (July 2026), no DOI recorded.
-- It explicitly labels the uniform analyticity radius (H-Rbeta) and the profile
-- inequality exp(-p0(g)) <= g^4 (H-P0') as hypotheses.
------------------------------------------------------------------------

record CauchyRadiusCouplingStep (Bound : Set) : Set₁ where
  field
    zero b0Half closureBudget : Bound
    add : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    smallFieldRemainder largeFieldRemainder totalRemainder : Nat → Bound

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (add left right) (add leftUpper rightUpper)

    totalRemainderSplits : ∀ scale →
      LessEqual (totalRemainder scale)
        (add (smallFieldRemainder scale) (largeFieldRemainder scale))

    smallFieldCauchyBound : ∀ scale →
      LessEqual (smallFieldRemainder scale) closureBudget

    largeFieldPenaltyBound : ∀ scale →
      LessEqual (largeFieldRemainder scale) closureBudget

    twoBudgetsBelowB0Half :
      LessEqual (add closureBudget closureBudget) b0Half

open CauchyRadiusCouplingStep public

couplingRemainderBelowB0Half :
  ∀ {Bound} (dataSet : CauchyRadiusCouplingStep Bound) scale →
  LessEqual dataSet (totalRemainder dataSet scale) (b0Half dataSet)
couplingRemainderBelowB0Half dataSet scale =
  transitive dataSet
    (totalRemainderSplits dataSet scale)
    (transitive dataSet
      (addMonotone dataSet
        (smallFieldCauchyBound dataSet scale)
        (largeFieldPenaltyBound dataSet scale))
      (twoBudgetsBelowB0Half dataSet))

record InverseCouplingIteration
    {Bound : Set} (stepData : CauchyRadiusCouplingStep Bound) : Set₁ where
  field
    inverseCoupling : Nat → Bound
    addStep : Bound → Bound → Bound
    natScale : Nat → Bound → Bound

    stepLowerBound : ∀ scale →
      LessEqual stepData
        (addStep (inverseCoupling scale) (b0Half stepData))
        (inverseCoupling (suc scale))

    addStepMonotoneRight : ∀ common {left right} →
      LessEqual stepData left right →
      LessEqual stepData (addStep left common) (addStep right common)

    baseIdentity :
      addStep (inverseCoupling zero)
        (natScale zero (b0Half stepData))
      ≡ inverseCoupling zero

    iterationIdentity : ∀ scale →
      addStep
        (addStep (inverseCoupling zero)
          (natScale scale (b0Half stepData)))
        (b0Half stepData)
      ≡ addStep (inverseCoupling zero)
          (natScale (suc scale) (b0Half stepData))

open InverseCouplingIteration public

inverseCouplingGrowsLinearly :
  ∀ {Bound} {stepData : CauchyRadiusCouplingStep Bound}
    (iteration : InverseCouplingIteration stepData) scale →
  LessEqual stepData
    (addStep iteration
      (inverseCoupling iteration zero)
      (natScale iteration scale (b0Half stepData)))
    (inverseCoupling iteration scale)
inverseCouplingGrowsLinearly {stepData = stepData} iteration zero =
  subst
    (λ lower → LessEqual stepData lower (inverseCoupling iteration zero))
    (sym (baseIdentity iteration))
    (reflexive stepData (inverseCoupling iteration zero))
inverseCouplingGrowsLinearly {stepData = stepData} iteration (suc scale) =
  subst
    (λ lower → LessEqual stepData lower
      (inverseCoupling iteration (suc scale)))
    (iterationIdentity iteration scale)
    (transitive stepData
      (addStepMonotoneRight iteration (b0Half stepData)
        (inverseCouplingGrowsLinearly iteration scale))
      (stepLowerBound iteration scale))

record FiniteWeakCouplingWindow (Bound : Set) : Set₁ where
  field
    cutoff : Nat
    WithinWindow : Nat → Set
    largeFieldContribution smallFieldBudget : Nat → Bound
    LessEqual : Bound → Bound → Set
    everyScaleThroughCutoffInside : ∀ scale → Set
    absorbedInsideWindow : ∀ scale →
      WithinWindow scale →
      LessEqual (largeFieldContribution scale) (smallFieldBudget scale)

open FiniteWeakCouplingWindow public

windowedAbsorption :
  ∀ {Bound} (window : FiniteWeakCouplingWindow Bound) scale →
  WithinWindow window scale →
  LessEqual window
    (largeFieldContribution window scale)
    (smallFieldBudget window scale)
windowedAbsorption = absorbedInsideWindow

cauchyLargeFieldRemainderAssemblyLevel : ProofLevel
cauchyLargeFieldRemainderAssemblyLevel = machineChecked

inverseCouplingLinearGrowthInductionLevel : ProofLevel
inverseCouplingLinearGrowthInductionLevel = machineChecked

finiteWeakCouplingWindowAssemblyLevel : ProofLevel
finiteWeakCouplingWindowAssemblyLevel = machineChecked

uniformBetaAnalyticityRadiusInputsLevel : ProofLevel
uniformBetaAnalyticityRadiusInputsLevel = conditional

p0ProfileGFourthInputsLevel : ProofLevel
p0ProfileGFourthInputsLevel = conditional

allScalePenaltyBeyondFiniteWindowInputsLevel : ProofLevel
allScalePenaltyBeyondFiniteWindowInputsLevel = conditional
