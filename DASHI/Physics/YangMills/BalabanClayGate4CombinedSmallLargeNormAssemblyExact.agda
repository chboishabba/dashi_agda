module DASHI.Physics.YangMills.BalabanClayGate4CombinedSmallLargeNormAssemblyExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCriticalMapRGCutsetCompletion as ExistingRG

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
-- The exact theorem-level source for each norm convention remains pending direct
-- primary verification.  The result below is the order-algebra assembly required
-- once the small-field estimate and absorbed large-field contribution are stated
-- in one common norm.
------------------------------------------------------------------------

record CombinedSmallLargeNormData
    (State Bound : Set) : Set₁ where
  field
    oldState nextSmallState nextCombinedState : State
    norm : State → Bound

    lambda perturbativeError largeFieldContribution totalError : Bound
    add multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (add left right) (add leftUpper rightUpper)

    combinedSplitsBelowSmallPlusLarge :
      LessEqual
        (norm nextCombinedState)
        (add (norm nextSmallState) largeFieldContribution)

    smallFieldOneStep :
      LessEqual
        (norm nextSmallState)
        (add (multiply lambda (norm oldState)) perturbativeError)

    largeFieldAbsorbed :
      LessEqual largeFieldContribution totalError

    combineErrors :
      add
        (add (multiply lambda (norm oldState)) perturbativeError)
        totalError
      ≡ add
          (multiply lambda (norm oldState))
          (add perturbativeError totalError)

open CombinedSmallLargeNormData public

combinedOneStepPolymerNorm :
  ∀ {State Bound} (dataSet : CombinedSmallLargeNormData State Bound) →
  LessEqual dataSet
    (norm dataSet (nextCombinedState dataSet))
    (add dataSet
      (multiply dataSet (lambda dataSet)
        (norm dataSet (oldState dataSet)))
      (add dataSet
        (perturbativeError dataSet)
        (totalError dataSet)))
combinedOneStepPolymerNorm dataSet =
  transitive dataSet
    (combinedSplitsBelowSmallPlusLarge dataSet)
    (subst
      (λ upper → LessEqual dataSet
        (add dataSet
          (norm dataSet (nextSmallState dataSet))
          (largeFieldContribution dataSet))
        upper)
      (combineErrors dataSet)
      (addMonotone dataSet
        (smallFieldOneStep dataSet)
        (largeFieldAbsorbed dataSet)))

------------------------------------------------------------------------
-- Adapter retaining the existing OneStepRGCutset as the small-field authority.
------------------------------------------------------------------------

record ExistingRGCombinedLargeFieldBridge
    {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density}
    (rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density) : Set₁ where
  field
    combinedPolymer : Polymer
    largeFieldContribution totalLargeFieldError : Bound

    combinedBelowSmallPlusLarge :
      ExistingRG.LessEqual rg
        (ExistingRG.polymerNorm rg combinedPolymer)
        (ExistingRG.addBound rg
          (ExistingRG.polymerNorm rg (ExistingRG.E-next rg))
          largeFieldContribution)

    largeFieldAbsorbed :
      ExistingRG.LessEqual rg largeFieldContribution totalLargeFieldError

    reassociateErrors :
      ExistingRG.addBound rg
        (ExistingRG.addBound rg
          (ExistingRG.multiplyBound rg
            (ExistingRG.lambdaPolymer rg)
            (ExistingRG.polymerNorm rg (ExistingRG.E rg)))
          (ExistingRG.perturbativeError rg))
        totalLargeFieldError
      ≡ ExistingRG.addBound rg
          (ExistingRG.multiplyBound rg
            (ExistingRG.lambdaPolymer rg)
            (ExistingRG.polymerNorm rg (ExistingRG.E rg)))
          (ExistingRG.addBound rg
            (ExistingRG.perturbativeError rg)
            totalLargeFieldError)

open ExistingRGCombinedLargeFieldBridge public

combinedOneStepFromExistingSmallFieldRG :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density}
    {rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density}
    (bridge : ExistingRGCombinedLargeFieldBridge rg) →
  ExistingRG.LessEqual rg
    (ExistingRG.polymerNorm rg (combinedPolymer bridge))
    (ExistingRG.addBound rg
      (ExistingRG.multiplyBound rg
        (ExistingRG.lambdaPolymer rg)
        (ExistingRG.polymerNorm rg (ExistingRG.E rg)))
      (ExistingRG.addBound rg
        (ExistingRG.perturbativeError rg)
        (totalLargeFieldError bridge)))
combinedOneStepFromExistingSmallFieldRG {rg = rg} bridge =
  ExistingRG.lessEqualTransitive rg
    (combinedBelowSmallPlusLarge bridge)
    (subst
      (λ upper → ExistingRG.LessEqual rg
        (ExistingRG.addBound rg
          (ExistingRG.polymerNorm rg (ExistingRG.E-next rg))
          (largeFieldContribution bridge))
        upper)
      (reassociateErrors bridge)
      (ExistingRG.addBoundMonotone rg
        (ExistingRG.oneStepPolymerContraction rg)
        (largeFieldAbsorbed bridge)))

combinedSmallLargeNormAssemblyLevel : ProofLevel
combinedSmallLargeNormAssemblyLevel = machineChecked

existingSmallFieldRGCombinedAssemblyLevel : ProofLevel
existingSmallFieldRGCombinedAssemblyLevel = machineChecked

-- The remaining physical seam is now explicit: identify the actual combined
-- polymer with the sum of the existing small-field next polymer and the R-sector
-- activity, and prove the latter is bounded by the absorption budget.
combinedPolymerRepresentationInputsLevel : ProofLevel
combinedPolymerRepresentationInputsLevel = conditional

largeFieldAbsorptionIntoExistingNormInputsLevel : ProofLevel
largeFieldAbsorptionIntoExistingNormInputsLevel = conditional
