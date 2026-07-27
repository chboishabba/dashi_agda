module DASHI.Physics.Closure.NSTriadKNFinalCutoffUniformDualBoundAssembly where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres; Pierre Germain; Oleg
-- Kiriukhin; DASHI repository contributors.
-- Title: "Final cutoff-uniform dual trilinear bound assembly for Stage 3".
-- Venue/year: Journal of Functional Analysis 187 (2001), 1--24; Journal of
-- Differential Equations 226 (2006), 373--428; arXiv:2604.12188v1 (2026);
-- DASHI formal development, 2026.
-- DOI: 10.1006/jfan.2001.3804; 10.1016/j.jde.2005.10.007;
-- 10.48550/arXiv.2604.12188; repository-original final assembly has no DOI.
-- Uses: the three concrete Grafakos-Torres conditions, signed-to-positive
-- domination, and explicit shell, overlap, orbit, helicity, reality and
-- direction constants chosen before the Galerkin cutoff.
-- Relationship: proves the final transitive assembly generically and exposes
-- every multiplicative constant.  The repository theorem remains open until
-- the concrete three-condition package and all transport factors are closed.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNGrafakosTorresComponentAssembly as GT

data ConstantFactor : Set where
  shellFactor overlapFactor orbitFactor helicityFactor realityFactor
  directionFactor : ConstantFactor

record FinalDualBoundCarrier
    {c s st : Level} : Set (lsuc (c ⊔ s ⊔ st)) where
  field
    Cutoff : Set c
    Scalar : Set s
    State : Set st

    zero one : Scalar
    multiply : Scalar → Scalar → Scalar
    _≤_ : Scalar → Scalar → Set s
    absoluteValue : Scalar → Scalar

    trilinearForm : Cutoff → State → State → State → Scalar
    leftNorm rightNorm outputNorm : State → Scalar

    positiveKernelBound : Cutoff → State → State → State → Scalar
    factorConstant : ConstantFactor → Scalar

    leqTransitive : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c

open FinalDualBoundCarrier public

combinedTransportConstant :
  ∀ {c s st} (C : FinalDualBoundCarrier {c} {s} {st}) → Scalar C
combinedTransportConstant C =
  multiply C (factorConstant C shellFactor)
    (multiply C (factorConstant C overlapFactor)
      (multiply C (factorConstant C orbitFactor)
        (multiply C (factorConstant C helicityFactor)
          (multiply C
            (factorConstant C realityFactor)
            (factorConstant C directionFactor)))))

productOfThreeNorms :
  ∀ {c s st} (C : FinalDualBoundCarrier {c} {s} {st}) →
  State C → State C → State C → Scalar C
productOfThreeNorms C left right output =
  multiply C (leftNorm C left)
    (multiply C (rightNorm C right) (outputNorm C output))

record FinalDualBoundInputs
    {c s st : Level}
    (C : FinalDualBoundCarrier {c} {s} {st}) : Set (lsuc (c ⊔ s ⊔ st)) where
  field
    factorPositive : ConstantFactor → Set s
    everyFactorIndependentOfCutoff : ConstantFactor → Set s

    signedBelowPositive : ∀ cutoff left right output →
      _≤_ C
        (absoluteValue C (trilinearForm C cutoff left right output))
        (positiveKernelBound C cutoff left right output)

    threeConditionPositiveBound : ∀ cutoff left right output →
      _≤_ C
        (positiveKernelBound C cutoff left right output)
        (multiply C
          (combinedTransportConstant C)
          (productOfThreeNorms C left right output))

    concreteThreeConditionAssembly : Set s
    signedRealityAssembly : Set s
    actualStage3KernelIdentified : Set s

open FinalDualBoundInputs public

finalCutoffUniformDualBound :
  ∀ {c s st}
    {C : FinalDualBoundCarrier {c} {s} {st}} →
  (I : FinalDualBoundInputs C) →
  ∀ cutoff left right output →
  _≤_ C
    (absoluteValue C (trilinearForm C cutoff left right output))
    (multiply C
      (combinedTransportConstant C)
      (productOfThreeNorms C left right output))
finalCutoffUniformDualBound {C = C} I cutoff left right output =
  leqTransitive C
    (signedBelowPositive I cutoff left right output)
    (threeConditionPositiveBound I cutoff left right output)

record ConcreteFinalStage3Cutset : Set₁ where
  field
    allThreeGrafakosTorresConditions : Set
    signedCoefficientDominatedByPositiveKernel : Set

    shellConstantExplicit : Set
    overlapConstantExplicit : Set
    orbitConstantExplicit : Set
    helicityConstantExplicit : Set
    realityConstantExplicit : Set
    directionConstantExplicit : Set

    everyConstantChosenBeforeCutoff : Set
    exactStateNormIdentification : Set
    exactStage3TrilinearIdentification : Set

open ConcreteFinalStage3Cutset public

finalTransitiveAssemblyClosed : Bool
finalTransitiveAssemblyClosed = true

finalTransitiveAssemblyClosedIsTrue :
  finalTransitiveAssemblyClosed ≡ true
finalTransitiveAssemblyClosedIsTrue = refl

allSixConstantFactorsExposed : Bool
allSixConstantFactorsExposed = true

allSixConstantFactorsExposedIsTrue : allSixConstantFactorsExposed ≡ true
allSixConstantFactorsExposedIsTrue = refl

concreteStage3CutoffUniformDualBoundClosed : Bool
concreteStage3CutoffUniformDualBoundClosed = false

concreteStage3CutoffUniformDualBoundClosedIsFalse :
  concreteStage3CutoffUniformDualBoundClosed ≡ false
concreteStage3CutoffUniformDualBoundClosedIsFalse = refl
