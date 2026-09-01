module DASHI.Analysis.RiemannG2CanonicalCharacterHighestAlphaReconciliationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannG2QuarterPeriodAnalyticRouteReconciliationExact as Route

------------------------------------------------------------------------
-- H_X HIGHEST-ALPHA RECONCILIATION
--
-- Cross-branch repo audit (PR #677) shows that the ordinary constructed
-- complex-number, phase, exponential and cosine machinery has already been
-- recursively reduced to an assembled constructed character donor.  Its final
-- H_X seam is not another transcendental theorem but an exact attachment to the
-- canonical Riemann AnalyticSubstrate carrier.
--
-- This file deliberately does not import the open #677 branch and does not
-- transport its proof terms.  Instead it tightens the #676 search graph: under
-- the standing assumption that ordinary machinery is available within-repo,
-- the live H_X payment is same-carrier realization, not rebuilding phase/exp
-- algebra.
------------------------------------------------------------------------

record CrossBranchConstructedCharacterReturn : Set where
  constructor cross-branch-constructed-character-return
  field
    sourceBranch : String
    sourceHead : String
    ordinaryConstructedComplexCarrierOwned : Bool
    ordinaryConstructedComplexCarrierOwnedIsTrue :
      ordinaryConstructedComplexCarrierOwned ≡ true
    targetCharacterProductReducedToOrdinaryMachinery : Bool
    targetCharacterProductReducedToOrdinaryMachineryIsTrue :
      targetCharacterProductReducedToOrdinaryMachinery ≡ true
    reflectionEvenCosineProjectionOwnedByConstructedCore : Bool
    reflectionEvenCosineProjectionOwnedByConstructedCoreIsTrue :
      reflectionEvenCosineProjectionOwnedByConstructedCore ≡ true
    finalCanonicalCarrierAttachmentStillRequired : Bool
    finalCanonicalCarrierAttachmentStillRequiredIsTrue :
      finalCanonicalCarrierAttachmentStillRequired ≡ true
    importedAsProofTermsHere : Bool
    importedAsProofTermsHereIsFalse : importedAsProofTermsHere ≡ false

open CrossBranchConstructedCharacterReturn public

canonicalCrossBranchConstructedCharacterReturn :
  CrossBranchConstructedCharacterReturn
canonicalCrossBranchConstructedCharacterReturn =
  cross-branch-constructed-character-return
    "PR #677 agent/aristotle-experimental-proof-search"
    "107436163baf6016f985f6b95fce82460a992cfb"
    true refl
    true refl
    true refl
    true refl
    false refl

------------------------------------------------------------------------
-- Exact carrier-level payment visible on this branch.
--
-- Matching operation names are insufficient.  The donor's Real/Complex
-- carriers must be identified with the exact carriers selected by the concrete
-- AnalyticSubstrate consumed by RiemannHypothesisFor.
------------------------------------------------------------------------

record CanonicalCharacterCarrierAttachment
    (analytic : Analytic.AnalyticSubstrate) : Set₁ where
  private
    AC = Analytic.AnalyticSubstrate.carrier analytic
  field
    DonorReal DonorComplex : Set
    realCarrierIdentity :
      Analytic.ComplexAnalyticCarrier.Real AC ≡ DonorReal
    complexCarrierIdentity :
      Analytic.ComplexAnalyticCarrier.Complex AC ≡ DonorComplex
    attachmentReference : String

open CanonicalCharacterCarrierAttachment public

------------------------------------------------------------------------
-- Search pruning after accepting ordinary in-repo machinery as infrastructure.
------------------------------------------------------------------------

data HXSearchAction : Set where
  rebuildConstructedComplexNumbers
  reproveRealPhaseCoherence
  reproveComplexExpAdditivity
  reproveCosineProjection
  proveCanonicalCarrierAttachment
  continueToCanonicalTestModulation
  : HXSearchAction

HXRelevant : HXSearchAction → Set
HXRelevant rebuildConstructedComplexNumbers = ⊥
HXRelevant reproveRealPhaseCoherence = ⊥
HXRelevant reproveComplexExpAdditivity = ⊥
HXRelevant reproveCosineProjection = ⊥
HXRelevant proveCanonicalCarrierAttachment = ⊤
HXRelevant continueToCanonicalTestModulation = ⊤

rebuildConstructedComplexNumbersPruned :
  HXRelevant rebuildConstructedComplexNumbers → ⊥
rebuildConstructedComplexNumbersPruned x = x

reproveRealPhaseCoherencePruned :
  HXRelevant reproveRealPhaseCoherence → ⊥
reproveRealPhaseCoherencePruned x = x

reproveComplexExpAdditivityPruned :
  HXRelevant reproveComplexExpAdditivity → ⊥
reproveComplexExpAdditivityPruned x = x

reproveCosineProjectionPruned :
  HXRelevant reproveCosineProjection → ⊥
reproveCosineProjectionPruned x = x

characterInfrastructureMayAdvanceBeforeCrossing :
  Route.CanAdvanceBeforeCrossing Route.HXcomplexCharacter
characterInfrastructureMayAdvanceBeforeCrossing = tt

record CanonicalCharacterHighestAlphaBoundary : Set where
  constructor canonical-character-highest-alpha-boundary
  field
    ordinaryComplexInfrastructureIsPrimaryResearchLeaf : Bool
    ordinaryComplexInfrastructureIsPrimaryResearchLeafIsFalse :
      ordinaryComplexInfrastructureIsPrimaryResearchLeaf ≡ false

    canonicalSameCarrierAttachmentIsImmediateHXPayment : Bool
    canonicalSameCarrierAttachmentIsImmediateHXPaymentIsTrue :
      canonicalSameCarrierAttachmentIsImmediateHXPayment ≡ true

    quarterPeriodCrossingMustPrecedeCanonicalHXAttachment : Bool
    quarterPeriodCrossingMustPrecedeCanonicalHXAttachmentIsFalse :
      quarterPeriodCrossingMustPrecedeCanonicalHXAttachment ≡ false

    closingCarrierEqualityAloneProvesFullHX : Bool
    closingCarrierEqualityAloneProvesFullHXIsFalse :
      closingCarrierEqualityAloneProvesFullHX ≡ false

    crossBranchProofTermsImportedHere : Bool
    crossBranchProofTermsImportedHereIsFalse :
      crossBranchProofTermsImportedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalCharacterHighestAlphaBoundary : CanonicalCharacterHighestAlphaBoundary
canonicalCharacterHighestAlphaBoundary =
  canonical-character-highest-alpha-boundary
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl
    "Assuming ordinary constructed real/complex/transcendental machinery is already available within-repo, do not spend RH search budget rebuilding phase algebra, exp additivity or cosine projection. The #677 recursion already identifies the final H_X seam as exact realization on the canonical Riemann analytic carrier. On #676 the immediate payment is therefore the typed same-carrier attachment; after that, continue forward to the canonical test-modulation/spectral-shift consumer. Carrier equality by itself is not claimed to transport every operation or theorem, and no #677 proof term is imported here."
