module DASHI.Physics.YangMills.BalabanExplicitContractionBudget where

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Final scalar producer for B7.
------------------------------------------------------------------------

record ExplicitContractionBudget (Bound : Set) : Set₁ where
  field
    referenceGreenUpper correctionUpper nonlinearUpper rhoG one : Bound
    multiply : Bound → Bound → Bound
    LessEqual StrictlyBelow : Bound → Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    multiplyMonotone : ∀ {left left′ right right′} →
      LessEqual left left′ → LessEqual right right′ →
      LessEqual (multiply left right) (multiply left′ right′)

    greenUpper : Bound
    greenUpperDefinition :
      greenUpper ≡ multiply referenceGreenUpper correctionUpper

    producedProductBelowRho :
      LessEqual (multiply
        (multiply referenceGreenUpper correctionUpper)
        nonlinearUpper) rhoG

    rhoStrict : StrictlyBelow rhoG one

open ExplicitContractionBudget public

greenTimesNonlinearBelowRho :
  ∀ {Bound : Set} →
  (budget : ExplicitContractionBudget Bound) →
  LessEqual budget
    (multiply budget (greenUpper budget) (nonlinearUpper budget))
    (rhoG budget)
greenTimesNonlinearBelowRho budget
  rewrite greenUpperDefinition budget = producedProductBelowRho budget

record ContractionWitness {Bound : Set}
    (budget : ExplicitContractionBudget Bound) : Set₁ where
  field
    commonProductBound :
      LessEqual budget
        (multiply budget (greenUpper budget) (nonlinearUpper budget))
        (rhoG budget)
    strictBelowOne : StrictlyBelow budget (rhoG budget) (one budget)

assembleContractionWitness :
  ∀ {Bound : Set} →
  (budget : ExplicitContractionBudget Bound) →
  ContractionWitness budget
assembleContractionWitness budget = record
  { commonProductBound = greenTimesNonlinearBelowRho budget
  ; strictBelowOne = rhoStrict budget
  }

explicitContractionBudgetAssemblyLevel : ProofLevel
explicitContractionBudgetAssemblyLevel = machineChecked

explicitNumericalSmallnessInputsLevel : ProofLevel
explicitNumericalSmallnessInputsLevel = conditional
