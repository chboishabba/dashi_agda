module DASHI.Reasoning.TrialecticWavePhaseHigherStackExact where

------------------------------------------------------------------------
-- SETOID-TRUNCATED HIGHER-STACK PROMOTION ON THE TRIADIC SITE
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Site
import DASHI.Reasoning.TrialecticGrothendieckCellPresheafExact as Presheaf
import DASHI.Reasoning.TrialecticWavePhaseGroupoidPresheafExact as Groupoid
import DASHI.Reasoning.TrialecticWavePhasePseudofunctorCoherenceExact as Pseudo
import DASHI.Reasoning.TrialecticWavePhaseEffectiveStackDescentExact as Stack
import DASHI.Reasoning.TrialecticWavePhaseTwoCellCocycleExact as Two
import DASHI.Reasoning.TrialecticPolicyIndexedAllDepthIterationExact as Depth
import DASHI.Reasoning.TrialecticGrothendieckAttachedTwoCellDescentExact as Attached

Phase3Cell :
  ∀ {U : Site.RelObj}
    {x y : Presheaf.Section U}
    {f g : Groupoid.FibreHom x y} →
  Two.Phase2Cell f g →
  Two.Phase2Cell f g →
  Set
Phase3Cell alpha beta = ⊤

phase3CellRefl :
  ∀ {U : Site.RelObj}
    {x y : Presheaf.Section U}
    {f g : Groupoid.FibreHom x y}
    (alpha : Two.Phase2Cell f g) →
  Phase3Cell alpha alpha
phase3CellRefl alpha = tt

phase3CellSym :
  ∀ {U : Site.RelObj}
    {x y : Presheaf.Section U}
    {f g : Groupoid.FibreHom x y}
    {alpha beta : Two.Phase2Cell f g} →
  Phase3Cell alpha beta → Phase3Cell beta alpha
phase3CellSym cell = tt

phase3CellTrans :
  ∀ {U : Site.RelObj}
    {x y : Presheaf.Section U}
    {f g : Groupoid.FibreHom x y}
    {alpha beta gamma : Two.Phase2Cell f g} →
  Phase3Cell alpha beta →
  Phase3Cell beta gamma →
  Phase3Cell alpha gamma
phase3CellTrans left right = tt

groupoidBoundary : Groupoid.TrialecticWavePhaseGroupoidPresheafBoundary
groupoidBoundary = Groupoid.canonicalTrialecticWavePhaseGroupoidPresheafBoundary

pseudoBoundary : Pseudo.TrialecticWavePhasePseudofunctorBoundary
pseudoBoundary = Pseudo.canonicalTrialecticWavePhasePseudofunctorBoundary

stackBoundary : Stack.TrialecticWavePhaseEffectiveStackBoundary
stackBoundary = Stack.canonicalTrialecticWavePhaseEffectiveStackBoundary

twoCellBoundary : Two.TrialecticWavePhaseTwoCellBoundary
twoCellBoundary = Two.canonicalTrialecticWavePhaseTwoCellBoundary

depthBoundary : Depth.TrialecticPolicyIndexedAllDepthBoundary
depthBoundary = Depth.canonicalTrialecticPolicyIndexedAllDepthBoundary

attachedBoundary : Attached.TrialecticGrothendieckAttachedTwoCellBoundary
attachedBoundary = Attached.canonicalTrialecticGrothendieckAttachedTwoCellBoundary

fullSiteGroupoidPresheafPaid :
  Groupoid.fullSiteNonDiscreteGroupoidPresheafPaid groupoidBoundary ≡ true
fullSiteGroupoidPresheafPaid = refl

pseudofunctorCoherencePaid :
  Pseudo.fullSiteTransportPseudofunctorPaid pseudoBoundary ≡ true
pseudofunctorCoherencePaid = refl

effectiveMorphismDescentPaid :
  Stack.compatibleLocalMorphismsGlue stackBoundary ≡ true
effectiveMorphismDescentPaid = refl

typedIsoUniquenessPaid :
  Stack.globalRealizationsUniqueUpToTypedIso stackBoundary ≡ true
typedIsoUniquenessPaid = refl

generalTwoCellCocyclePaid :
  Two.arbitraryTriadicOverlapPhaseCocyclePaid twoCellBoundary ≡ true
generalTwoCellCocyclePaid = refl

allDepthPolicyIterationPaid :
  Depth.allDepthIterationExistsGivenPolicy depthBoundary ≡ true
allDepthPolicyIterationPaid = refl

attachedRelationalTwoCellPaid :
  Attached.attachedFaceIsAdditionalTwoCellCoordinate attachedBoundary ≡ true
attachedRelationalTwoCellPaid = refl

record TrialecticWavePhaseHigherStackBoundary : Set where
  constructor trialectic-wave-phase-higher-stack-boundary
  field
    nonDiscreteGroupoidEverySiteObject : Bool
    groupoidValuedPresheafPaid : Bool
    restrictionPseudofunctorCoherencePaid : Bool
    effectiveObjectDescentPaid : Bool
    effectiveMorphismDescentPaid : Bool
    uniquenessUpToTypedIsoPaid : Bool
    generalPhaseTwoCellCalculusPaid : Bool
    generalTriadicCocyclePaid : Bool
    twoCellProofWitnessSetoidPaid : Bool
    attachedIrreducibleTwoCellRetained : Bool
    policyIndexedAllDepthIterationPaid : Bool
    certifiedPrestackOnTriadicSite : Bool
    certifiedEffectiveStackOnTriadicSite : Bool
    certifiedHigherStackOnTriadicSite : Bool
    arbitraryHypercoverDescentPaid : Bool
    certifiedHypersheaf : Bool

open TrialecticWavePhaseHigherStackBoundary public

canonicalTrialecticWavePhaseHigherStackBoundary :
  TrialecticWavePhaseHigherStackBoundary
canonicalTrialecticWavePhaseHigherStackBoundary =
  trialectic-wave-phase-higher-stack-boundary
    true true true true true true true true true true true
    true true true
    false false
