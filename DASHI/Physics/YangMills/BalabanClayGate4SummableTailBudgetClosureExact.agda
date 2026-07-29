module DASHI.Physics.YangMills.BalabanClayGate4SummableTailBudgetClosureExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- The theorem is elementary but decisive: a summable error sequence should be
-- consumed through its remaining tail, not forced into a false pointwise
-- geometric p0 estimate. If T_k = e_k + T_{k+1}, then a contractive one-step
-- bound preserves the combined invariant quantity ||E_k|| + T_k.
------------------------------------------------------------------------

record SummableTailOneStepData (Bound : Set) : Set₁ where
  field
    norm error tail : Nat → Bound
    lambda : Bound
    add multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (add left right) (add leftUpper rightUpper)

    addAssociative : ∀ left middle right →
      add (add left middle) right ≡ add left (add middle right)

    oneStepNormBound : ∀ scale →
      LessEqual (norm (suc scale))
        (add (multiply lambda (norm scale)) (error scale))

    contractionBelowIdentity : ∀ scale →
      LessEqual (multiply lambda (norm scale)) (norm scale)

    tailSplit : ∀ scale →
      tail scale ≡ add (error scale) (tail (suc scale))

open SummableTailOneStepData public

budgetedNorm :
  ∀ {Bound} → SummableTailOneStepData Bound → Nat → Bound
budgetedNorm dataSet scale = add dataSet (norm dataSet scale) (tail dataSet scale)

regroupOneStepErrorIntoTail :
  ∀ {Bound} (dataSet : SummableTailOneStepData Bound) scale →
  add dataSet
    (add dataSet
      (multiply dataSet (lambda dataSet) (norm dataSet scale))
      (error dataSet scale))
    (tail dataSet (suc scale))
  ≡ add dataSet
      (multiply dataSet (lambda dataSet) (norm dataSet scale))
      (tail dataSet scale)
regroupOneStepErrorIntoTail dataSet scale =
  trans
    (addAssociative dataSet
      (multiply dataSet (lambda dataSet) (norm dataSet scale))
      (error dataSet scale)
      (tail dataSet (suc scale)))
    (cong
      (add dataSet
        (multiply dataSet (lambda dataSet) (norm dataSet scale)))
      (sym (tailSplit dataSet scale)))

nextBudgetBelowContractedCurrentAndTail :
  ∀ {Bound} (dataSet : SummableTailOneStepData Bound) scale →
  LessEqual dataSet
    (budgetedNorm dataSet (suc scale))
    (add dataSet
      (multiply dataSet (lambda dataSet) (norm dataSet scale))
      (tail dataSet scale))
nextBudgetBelowContractedCurrentAndTail dataSet scale =
  subst
    (λ upper → LessEqual dataSet
      (budgetedNorm dataSet (suc scale)) upper)
    (regroupOneStepErrorIntoTail dataSet scale)
    (addMonotone dataSet
      (oneStepNormBound dataSet scale)
      (reflexive dataSet (tail dataSet (suc scale))))

budgetedNormNonincreasing :
  ∀ {Bound} (dataSet : SummableTailOneStepData Bound) scale →
  LessEqual dataSet
    (budgetedNorm dataSet (suc scale))
    (budgetedNorm dataSet scale)
budgetedNormNonincreasing dataSet scale =
  transitive dataSet
    (nextBudgetBelowContractedCurrentAndTail dataSet scale)
    (addMonotone dataSet
      (contractionBelowIdentity dataSet scale)
      (reflexive dataSet (tail dataSet scale)))

record InitialTailBudget
    {Bound : Set} (dataSet : SummableTailOneStepData Bound) : Set₁ where
  field
    cap : Bound
    initialBudgetBelowCap : LessEqual dataSet (budgetedNorm dataSet zero) cap

open InitialTailBudget public

allScaleTailBudgetBelowCap :
  ∀ {Bound} (dataSet : SummableTailOneStepData Bound) →
  (initial : InitialTailBudget dataSet) →
  ∀ scale → LessEqual dataSet (budgetedNorm dataSet scale) (cap initial)
allScaleTailBudgetBelowCap dataSet initial zero =
  initialBudgetBelowCap initial
allScaleTailBudgetBelowCap dataSet initial (suc scale) =
  transitive dataSet
    (budgetedNormNonincreasing dataSet scale)
    (allScaleTailBudgetBelowCap dataSet initial scale)

summableTailOneStepReductionLevel : ProofLevel
summableTailOneStepReductionLevel = machineChecked

tailBudgetMonotonicityLevel : ProofLevel
tailBudgetMonotonicityLevel = machineChecked

allScaleTailBudgetInductionLevel : ProofLevel
allScaleTailBudgetInductionLevel = machineChecked

physicalErrorTailDefinitionInputsLevel : ProofLevel
physicalErrorTailDefinitionInputsLevel = conditional

physicalTailSplitAndConvergenceInputsLevel : ProofLevel
physicalTailSplitAndConvergenceInputsLevel = conditional

physicalTailBudgetImpliesPolymerAdmissibilityInputsLevel : ProofLevel
physicalTailBudgetImpliesPolymerAdmissibilityInputsLevel = conditional
