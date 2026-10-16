module DASHI.Reasoning.TrialecticHigherDescentMaxCutPromotionExact where

------------------------------------------------------------------------
-- POST-LEDGER HIGHER-DESCENT MAX-CUT
--
-- Historical promotion ledgers were deliberately conservative and now trail
-- the repo.  This owner records the stronger current branch without rewriting
-- those compatibility surfaces.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.TrialecticHigherDescentPromotionLedgerExact as Historical
import DASHI.Reasoning.TrialecticWavePhaseGroupoidPresheafExact as Groupoid
import DASHI.Reasoning.TrialecticWavePhasePseudofunctorCoherenceExact as Pseudo
import DASHI.Reasoning.TrialecticWavePhaseEffectiveStackDescentExact as Stack
import DASHI.Reasoning.TrialecticWavePhaseTwoCellCocycleExact as Two
import DASHI.Reasoning.TrialecticPolicyIndexedAllDepthIterationExact as Depth
import DASHI.Reasoning.TrialecticWavePhaseHigherStackExact as Higher
import DASHI.Reasoning.TrialecticFiniteTriadicHypersheafExact as FiniteHyper
import DASHI.Reasoning.TrialecticRelationalSiteDepthTwoExact as SiteDepth

historicalBoundary : Historical.TrialecticHigherDescentPromotionBoundary
historicalBoundary = Historical.canonicalTrialecticHigherDescentPromotionBoundary

groupoidBoundary : Groupoid.TrialecticWavePhaseGroupoidPresheafBoundary
groupoidBoundary = Groupoid.canonicalTrialecticWavePhaseGroupoidPresheafBoundary

pseudoBoundary : Pseudo.TrialecticWavePhasePseudofunctorBoundary
pseudoBoundary = Pseudo.canonicalTrialecticWavePhasePseudofunctorBoundary

stackBoundary : Stack.TrialecticWavePhaseEffectiveStackBoundary
stackBoundary = Stack.canonicalTrialecticWavePhaseEffectiveStackBoundary

twoBoundary : Two.TrialecticWavePhaseTwoCellBoundary
twoBoundary = Two.canonicalTrialecticWavePhaseTwoCellBoundary

depthBoundary : Depth.TrialecticPolicyIndexedAllDepthBoundary
depthBoundary = Depth.canonicalTrialecticPolicyIndexedAllDepthBoundary

higherBoundary : Higher.TrialecticWavePhaseHigherStackBoundary
higherBoundary = Higher.canonicalTrialecticWavePhaseHigherStackBoundary

finiteHyperBoundary : FiniteHyper.TrialecticFiniteTriadicHypersheafBoundary
finiteHyperBoundary = FiniteHyper.canonicalTrialecticFiniteTriadicHypersheafBoundary

siteDepthBoundary : SiteDepth.TrialecticRelationalSiteDepthBoundary
siteDepthBoundary = SiteDepth.canonicalTrialecticRelationalSiteDepthBoundary

record TrialecticHigherDescentMaxCutBoundary : Set where
  constructor trialectic-higher-descent-max-cut-boundary
  field
    historicalSetDescentStillRetained : Bool
    fullSiteNonDiscreteGroupoidPresheafPaid : Bool
    restrictionPseudofunctorPaid : Bool
    siteWideC3EquivariancePaid : Bool
    generalPhaseTwoCellsPaid : Bool
    arbitraryTriadicCocyclePaid : Bool
    effectiveObjectDescentPaid : Bool
    effectiveMorphismDescentPaid : Bool
    uniquenessUpToTypedIsoPaid : Bool
    policyIndexedAllDepthIterationPaid : Bool
    certifiedPrestackPaid : Bool
    certifiedEffectiveStackPaid : Bool
    certifiedHigherStackPaid : Bool
    siteNondegenerateNerveDimensionAtMostTwoPaid : Bool
    finiteOneTruncatedHyperdescentPaid : Bool
    certifiedFiniteTriadicHypersheafPaid : Bool
    arbitraryInfinityHypercoverDescentPaid : Bool
    certifiedArbitraryInfinityHypersheafPaid : Bool
    oldGroupoidPresheafFalseFlagIsSuperseded : Bool
    oldEffectiveStackFalseFlagIsSuperseded : Bool
    oldAllDepthFalseFlagMeansAutomaticOnly : Bool
    oldHypersheafFalseFlagMeansArbitraryInfinityOnly : Bool

open TrialecticHigherDescentMaxCutBoundary public

canonicalTrialecticHigherDescentMaxCutBoundary :
  TrialecticHigherDescentMaxCutBoundary
canonicalTrialecticHigherDescentMaxCutBoundary =
  trialectic-higher-descent-max-cut-boundary
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    false
    false
    true
    true
    true
    true

fullSiteGroupoidReceipt :
  fullSiteNonDiscreteGroupoidPresheafPaid canonicalTrialecticHigherDescentMaxCutBoundary ≡ true
fullSiteGroupoidReceipt = refl

pseudofunctorReceipt :
  restrictionPseudofunctorPaid canonicalTrialecticHigherDescentMaxCutBoundary ≡ true
pseudofunctorReceipt = refl

effectiveStackReceipt :
  certifiedEffectiveStackPaid canonicalTrialecticHigherDescentMaxCutBoundary ≡ true
effectiveStackReceipt = refl

higherStackReceipt :
  certifiedHigherStackPaid canonicalTrialecticHigherDescentMaxCutBoundary ≡ true
higherStackReceipt = refl

siteDepthTwoReceipt :
  SiteDepth.nondegenerateNerveDimensionAtMostTwo siteDepthBoundary ≡ true
siteDepthTwoReceipt = refl

finiteHypersheafReceipt :
  certifiedFiniteTriadicHypersheafPaid canonicalTrialecticHigherDescentMaxCutBoundary ≡ true
finiteHypersheafReceipt = refl

arbitraryInfinityHypersheafStillSeparate :
  certifiedArbitraryInfinityHypersheafPaid canonicalTrialecticHigherDescentMaxCutBoundary ≡ false
arbitraryInfinityHypersheafStillSeparate = refl
