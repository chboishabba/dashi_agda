module DASHI.Reasoning.TrialecticHypersheafHypercoverFrontierExact where

------------------------------------------------------------------------
-- HYPERSHEAF / HYPERCOVER FRONTIER
--
-- The concrete triadic-site stack and phase 2-cell layer are paid.  The repo
-- now also owns a direct finite 1-truncated hyperdescent receipt for this exact
-- seven-object topology.  The remaining stronger frontier is therefore NOT
-- "hypersheaf machinery absent"; it is only an arbitrary external infinity-
-- hypercover / infinity-topos hypercompletion claim.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.TrialecticWavePhaseHigherStackExact as Higher
import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric
import DASHI.Reasoning.TrialecticFiniteTriadicHypersheafExact as FiniteHyper

higherBoundary : Higher.TrialecticWavePhaseHigherStackBoundary
higherBoundary = Higher.canonicalTrialecticWavePhaseHigherStackBoundary

hyperfabricBoundary : Hyperfabric.TypedHyperfabricAuthorityBoundary
hyperfabricBoundary = Hyperfabric.canonicalTypedHyperfabricAuthorityBoundary

finiteHyperBoundary : FiniteHyper.TrialecticFiniteTriadicHypersheafBoundary
finiteHyperBoundary = FiniteHyper.canonicalTrialecticFiniteTriadicHypersheafBoundary

higherStackPrerequisitePaid :
  Higher.certifiedHigherStackOnTriadicSite higherBoundary ≡ true
higherStackPrerequisitePaid = refl

higherArityHyperfabricPrerequisitePaid :
  Hyperfabric.higherArityRelationsRepresentable hyperfabricBoundary ≡ true
higherArityHyperfabricPrerequisitePaid = refl

stalkRestrictionPrerequisitePaid :
  Hyperfabric.restrictionMapsRepresentable hyperfabricBoundary ≡ true
stalkRestrictionPrerequisitePaid = refl

finiteTriadicHyperdescentPaid :
  FiniteHyper.certifiedFiniteOneTruncatedHypersheaf finiteHyperBoundary ≡ true
finiteTriadicHyperdescentPaid = refl

arbitraryInfinityHyperdescentStillSeparate :
  FiniteHyper.certifiedArbitraryInfinityHypersheaf finiteHyperBoundary ≡ false
arbitraryInfinityHyperdescentStillSeparate = refl

------------------------------------------------------------------------
-- Generic stronger promotion sockets remain available for an external notion
-- of arbitrary infinity-hypercover descent or a separately formalised theorem
-- that this 1-truncated stack is hypercomplete in such semantics.
------------------------------------------------------------------------

record HypercoverDescentReceipt : Set₁ where
  field
    Hypercover : Set
    hypercoverDescent : Hypercover → Set
    everyDeclaredHypercoverDescends :
      (cover : Hypercover) → hypercoverDescent cover

record TruncatedStackHypercompleteReceipt : Set₁ where
  field
    hypercomplete : Set
    oneTruncatedStackImpliesHypercomplete : hypercomplete

record HypersheafPromotionReceipt : Set₁ where
  constructor hypersheaf-promotion-receipt
  field
    directHypercoverReceipt : HypercoverDescentReceipt

record HypersheafPromotionViaTruncation : Set₁ where
  constructor hypersheaf-promotion-via-truncation
  field
    truncationReceipt : TruncatedStackHypercompleteReceipt

promoteFromDirectHypercover :
  HypersheafPromotionReceipt → Bool
promoteFromDirectHypercover receipt = true

promoteFromTruncation :
  HypersheafPromotionViaTruncation → Bool
promoteFromTruncation receipt = true

record TrialecticHypersheafHypercoverFrontierBoundary : Set where
  constructor trialectic-hypersheaf-hypercover-frontier-boundary
  field
    higherStackPrerequisiteReady : Bool
    typedHyperfabricPrerequisiteReady : Bool
    effectiveObjectMorphismDescentReady : Bool
    generalTwoCellCocycleReady : Bool
    policyIndexedDepthReady : Bool
    finiteTriadicHypercoverAPIConstructed : Bool
    finiteOneTruncatedHypersheafCertified : Bool
    arbitraryInfinityHypercoverAPIAlreadyFoundInRepo : Bool
    arbitraryTruncationHypercompleteTheoremAlreadyWelded : Bool
    allFiniteTriadicHypersheafPrerequisitesPaid : Bool
    remainingFrontierIsOnlyArbitraryInfinityHyperdescent : Bool

open TrialecticHypersheafHypercoverFrontierBoundary public

canonicalTrialecticHypersheafHypercoverFrontierBoundary :
  TrialecticHypersheafHypercoverFrontierBoundary
canonicalTrialecticHypersheafHypercoverFrontierBoundary =
  trialectic-hypersheaf-hypercover-frontier-boundary
    true true true true true
    true true
    false false
    true true
