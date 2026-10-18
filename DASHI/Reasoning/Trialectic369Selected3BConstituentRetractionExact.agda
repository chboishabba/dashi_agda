module DASHI.Reasoning.Trialectic369Selected3BConstituentRetractionExact where

------------------------------------------------------------------------
-- CONSTITUENT RETRACTION -> FAITHFUL INCLUSION
--
-- DASHI CONTRIBUTION
--
-- The selected-3B full-grade max-cut isolates faithfulness of the 196883
-- constituent inclusion as one remaining source receipt.
--
-- Representation-theoretically, the cleaner witness is a retraction:
--
--   full grade-two carrier --project--> constituent
--   constituent --include--> full grade-two carrier
--
-- with project(include(x)) = x.
--
-- Any such retraction proves inclusion injectivity automatically and therefore
-- discharges the faithfulness half of the full-grade action max-cut.
--
-- No direct-sum decomposition or projection is manufactured here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

import DASHI.Geometry.HilbertLorentzForcing as Linear
import DASHI.Moonshine.GradedRepresentationLinearRealisationExact as LinearRep
import DASHI.Moonshine.MonsterWeightTwoLinearActionBridgeExact as WeightTwo
import DASHI.Reasoning.Trialectic369CanonicalSelected3BLinearCoreExact as Core
import DASHI.Reasoning.Trialectic369Selected3BFullGradeActionMaxCutExact as MaxCut

------------------------------------------------------------------------
-- 1. Retraction data on the exact core.
------------------------------------------------------------------------

record ConstituentRetraction
    {Monster K : Set}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K})
    : Setω where
  field
    projectToConstituent :
      Linear.Vector
        (LinearRep.linearCarrier
          (WeightTwo.fullWeightTwoLinearRealisation
            (Core.weightTwoLinearBridge core)))
      →
      Linear.Vector
        (WeightTwo.constituentLinearCarrier
          (Core.weightTwoLinearBridge core))

    leftInverse :
      (state :
        Linear.Vector
          (WeightTwo.constituentLinearCarrier
            (Core.weightTwoLinearBridge core))) →
      projectToConstituent
        (WeightTwo.constituentInclusion
          (Core.weightTwoLinearBridge core)
          state)
      ≡ state

open ConstituentRetraction public

------------------------------------------------------------------------
-- 2. Retraction compiles faithfulness.
------------------------------------------------------------------------

inclusionInjectiveFromRetraction :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  ConstituentRetraction core →
  ∀ {left right :
    Linear.Vector
      (WeightTwo.constituentLinearCarrier
        (Core.weightTwoLinearBridge core))} →
  WeightTwo.constituentInclusion
    (Core.weightTwoLinearBridge core) left
  ≡
  WeightTwo.constituentInclusion
    (Core.weightTwoLinearBridge core) right
  →
  left ≡ right
inclusionInjectiveFromRetraction core retraction {left} {right} equality =
  trans
    (sym (leftInverse retraction left))
    (trans
      (cong
        (projectToConstituent retraction)
        equality)
      (leftInverse retraction right))

faithfulConstituentFromRetraction :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  ConstituentRetraction core →
  MaxCut.FaithfulWeightTwoConstituent core
faithfulConstituentFromRetraction core retraction =
  record
    { inclusionInjective =
        inclusionInjectiveFromRetraction core retraction
    }

------------------------------------------------------------------------
-- 3. Retraction + one full-grade equality closes canonical completion.
------------------------------------------------------------------------

canonicalActionFromRetractionAndFullGrade :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  ConstituentRetraction core →
  MaxCut.SelectedNormalizerFullGradeTwoAgreement core →
  Core.CanonicalSelected3BActionIntertwining core
canonicalActionFromRetractionAndFullGrade core retraction agreement =
  MaxCut.canonicalActionIntertwiningFromFullGrade
    core
    (faithfulConstituentFromRetraction core retraction)
    agreement

canonicalCompletionFromRetractionAndFullGrade :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  ConstituentRetraction core →
  MaxCut.SelectedNormalizerFullGradeTwoAgreement core →
  Core.CanonicalSelected3BLinearCompletion {Monster} {K}
canonicalCompletionFromRetractionAndFullGrade core retraction agreement =
  MaxCut.canonicalCompletionFromFullGrade
    core
    (faithfulConstituentFromRetraction core retraction)
    agreement

------------------------------------------------------------------------
-- 4. Firewalls.
------------------------------------------------------------------------

data DimensionSplitCreatesRetraction : Set where
data Arithmetic196884Equals196883PlusOneCreatesRetraction : Set where
data ConformalFixedPointCreatesLinearProjection : Set where

dimensionDoesNotCreateRetraction :
  DimensionSplitCreatesRetraction → ⊥
dimensionDoesNotCreateRetraction ()

arithmeticSplitDoesNotCreateRetraction :
  Arithmetic196884Equals196883PlusOneCreatesRetraction → ⊥
arithmeticSplitDoesNotCreateRetraction ()

fixedPointDoesNotCreateProjection :
  ConformalFixedPointCreatesLinearProjection → ⊥
fixedPointDoesNotCreateProjection ()

------------------------------------------------------------------------
-- 5. Machine-readable frontier.
------------------------------------------------------------------------

record Trialectic369Selected3BConstituentRetractionBoundary : Set where
  constructor trialectic-369-selected3b-constituent-retraction-boundary
  field
    retractionImpliesFaithfulInclusion : Bool
    faithfulInclusionCompilerOwned : Bool
    retractionPlusFullGradeAgreementClosesAction : Bool
    retractionPlusFullGradeAgreementClosesCompletion : Bool
    arithmeticDimensionSplitNotEnough : Bool
    actualConstituentRetractionInhabitedHere : Bool
    actualFullGradeAgreementInhabitedHere : Bool
    canonicalCompletionInhabitedHere : Bool

canonicalTrialectic369Selected3BConstituentRetractionBoundary :
  Trialectic369Selected3BConstituentRetractionBoundary
canonicalTrialectic369Selected3BConstituentRetractionBoundary =
  trialectic-369-selected3b-constituent-retraction-boundary
    true true true true true
    false false false
