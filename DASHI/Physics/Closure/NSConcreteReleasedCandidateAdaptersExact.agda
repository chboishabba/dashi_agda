module DASHI.Physics.Closure.NSConcreteReleasedCandidateAdaptersExact where

------------------------------------------------------------------------
-- CONCRETE C/D / CANDIDATE-LEVEL ADAPTERS ALL THE WAY TO THE RUN TARGET
--
-- After porting the two released comparator wrappers, the concrete Fefferman
-- semantics can consume candidate-level packages directly.  This removes the
-- comparator theorem itself from the reconstruction frontier:
--
--   C compact candidate family -> released C witness -> literal C -> run target
--   D periodic candidate family -> released D witness -> literal D -> run target.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal

import DASHI.Physics.Closure.NSCanonicalEuclideanPeriodicSemanticCarriersExact as Canonical
import DASHI.Physics.Closure.NSConcreteFeffermanSemanticsExact as Concrete
import DASHI.Physics.Closure.NSConcreteLiteralClayABCDRunTargetExact as Run
import DASHI.Physics.Closure.NSConcreteReleasedCDNativeReconstructionExact as Native
import DASHI.Physics.Closure.NSOpenAI2026ReleasedOptionCCompactCandidateAdapterExact as C
import DASHI.Physics.Closure.NSOpenAI2026ReleasedOptionDPeriodicCandidateAdapterExact as D

ConcreteCCompactCandidateFamily :
  Concrete.FeffermanAnalyticKernel → Set₁
ConcreteCCompactCandidateFamily K =
  (viscosity : BishopReal.ℝ) →
  Canonical.PositiveReal (Run.concreteSemantics K) viscosity →
  C.OptionCCompactCandidateAdapter
    (Run.concreteSemantics K) viscosity

ConcreteDPeriodicCandidateFamily :
  Concrete.FeffermanAnalyticKernel → Set₁
ConcreteDPeriodicCandidateFamily K =
  (viscosity : BishopReal.ℝ) →
  Canonical.PositiveReal (Run.concreteSemantics K) viscosity →
  D.OptionDPeriodicCandidateAdapter
    (Run.concreteSemantics K) viscosity

compactCandidateFamilyToReleasedCTheorem :
  ∀ {K} →
  ConcreteCCompactCandidateFamily K →
  Native.ConcreteReleasedComparatorCTheorem K
compactCandidateFamilyToReleasedCTheorem family viscosity positive =
  C.optionCOfCompactCandidate (family viscosity positive)

periodicCandidateFamilyToReleasedDTheorem :
  ∀ {K} →
  ConcreteDPeriodicCandidateFamily K →
  Native.ConcreteReleasedComparatorDTheorem K
periodicCandidateFamilyToReleasedDTheorem family viscosity positive =
  D.optionDOfPeriodicCandidate (family viscosity positive)

compactCandidateFamilyToLiteralC :
  ∀ {K} →
  ConcreteCCompactCandidateFamily K →
  Run.LiteralC K
compactCandidateFamilyToLiteralC family =
  Native.nativeReleasedComparatorCToLiteralC
    (compactCandidateFamilyToReleasedCTheorem family)

periodicCandidateFamilyToLiteralD :
  ∀ {K} →
  ConcreteDPeriodicCandidateFamily K →
  Run.LiteralD K
periodicCandidateFamilyToLiteralD family =
  Native.nativeReleasedComparatorDToLiteralD
    (periodicCandidateFamilyToReleasedDTheorem family)

compactCandidateFamilyToRunTarget :
  ∀ {K} →
  ConcreteCCompactCandidateFamily K →
  Run.ConcreteLiteralNSRunTarget K
compactCandidateFamilyToRunTarget family =
  Run.runTargetFromC (compactCandidateFamilyToLiteralC family)

periodicCandidateFamilyToRunTarget :
  ∀ {K} →
  ConcreteDPeriodicCandidateFamily K →
  Run.ConcreteLiteralNSRunTarget K
periodicCandidateFamilyToRunTarget family =
  Run.runTargetFromD (periodicCandidateFamilyToLiteralD family)

cComparatorWrapperRemovedFromFrontier : Bool
cComparatorWrapperRemovedFromFrontier = true

dComparatorWrapperRemovedFromFrontier : Bool
dComparatorWrapperRemovedFromFrontier = true

cActualCompactCandidateFamilyConstructedHere : Bool
cActualCompactCandidateFamilyConstructedHere = false

dActualPeriodicCandidateFamilyConstructedHere : Bool
dActualPeriodicCandidateFamilyConstructedHere = false

clayPromotionWithoutCandidateFamily : Bool
clayPromotionWithoutCandidateFamily = false

cComparatorWrapperRemovedFromFrontierIsTrue :
  cComparatorWrapperRemovedFromFrontier ≡ true
cComparatorWrapperRemovedFromFrontierIsTrue = refl

dComparatorWrapperRemovedFromFrontierIsTrue :
  dComparatorWrapperRemovedFromFrontier ≡ true
dComparatorWrapperRemovedFromFrontierIsTrue = refl
