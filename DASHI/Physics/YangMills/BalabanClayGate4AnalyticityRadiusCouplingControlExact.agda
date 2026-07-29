module DASHI.Physics.YangMills.BalabanClayGate4AnalyticityRadiusCouplingControlExact where

open import Agda.Builtin.Nat using (Nat; zero; suc)

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

    -- H-Rbeta: Cauchy estimate in h = g^2 with radius and bound uniform in k.
    smallFieldCauchyBound : ∀ scale →
      LessEqual (smallFieldRemainder scale) closureBudget

    -- H-P0': the large-field penalty profile is separately strong enough that
    -- C_lf exp(-p0(g_k)) fits the chosen closure budget.
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

    addStepMonotoneLeft : ∀ common {left right} →
      LessEqual stepData left right →
      LessEqual stepData (addStep common left) (addStep common right)

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
inverseCouplingGrowsLinearly iteration zero =
  reflexive _ (inverseCoupling iteration zero)
inverseCouplingGrowsLinearly {stepData = stepData} iteration (suc scale) =
  transportLeft
    (iterationIdentity iteration scale)
    (transitive stepData
      (addStepMonotoneLeft iteration (inverseCoupling iteration zero)
        (inverseCouplingGrowsLinearly iteration scale))
      (stepLowerBound iteration scale))
  where
  transportLeft : ∀ {A : Set} {R : A → A → Set} {left left' right} →
    left ≡ left' → R left' right → R left right
  transportLeft refl proof = proof

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
