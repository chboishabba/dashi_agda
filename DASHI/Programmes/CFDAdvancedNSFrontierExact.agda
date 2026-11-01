module DASHI.Programmes.CFDAdvancedNSFrontierExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- BIDI weld from dashiCFD to the live advanced Navier--Stokes programme.
--
-- The current NS research branch (PR #634) has advanced substantially beyond
-- the generic `navierStokesClosure` programme tag.  Because that branch is not
-- yet merged into the base of PR #636, this module does NOT duplicate or
-- import its theorem owners.  Instead it freezes the exact cross-branch
-- interface that the CFD satellite must preserve when those owners are joined.
--
-- Authoritative current NS shapes on PR #634:
--
-- R220: positive cell mass is already paid by 36 E D; only coherent Gram debt
--       remains in the quartic companion.
-- R222: the weakest sufficient research target is a nonnegative majorant of
--       the actual signed coherent Gram debt whose time integral is bounded
--       uniformly in Galerkin cutoff.  Gram negativity and pointwise uniform
--       smallness are not required.
-- R223--R228: the same companion collapses to the complete fixed-output
--       mixed-helicity carrier and its cutoff-uniform spacetime budget.
-- R229--R231: cellwise viscous coercivity does not survive coherent summation;
--       the product tangent reaches a weighted covariance / cubic commutator
--       wall.  That is the live analytic frontier, not a selected-dictionary
--       frame diagnostic.
------------------------------------------------------------------------

record CFDAdvancedNSMeasurementReceipt : Set₁ where
  constructor cfd-advanced-ns-measurement-receipt
  field
    Cutoff Time Output : Set

    -- The numerical run must stay indexed by the Galerkin cutoff and time.
    observedCutoff : Cutoff
    observedTime : Time

    -- Same-object observables needed by the theorem branch.  Their concrete
    -- numerical representations remain satellite-owned; the preservation
    -- receipt below is what matters for formal transport.
    coherentGramDebtObservation : Output
    coherentMajorantObservation : Output
    mixedHelicityFixedOutputObservation : Output
    mixedHelicitySpacetimeObservation : Output

    -- Evidence that the satellite quantities are the same physical objects as
    -- the corresponding theorem-branch carriers, rather than merely similar
    -- diagnostics or renamed plots.
    coherentGramSameObjectReceipt : Set
    mixedHelicitySameObjectReceipt : Set

    -- Finite numerical observation is deliberately not a cutoff-uniform
    -- analytic estimate.
    finiteRunOnly : Bool
    finiteRunOnlyIsTrue : finiteRunOnly ≡ true

open CFDAdvancedNSMeasurementReceipt public

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record CFDAdvancedNSFrontierBoundary : Set where
  constructor cfd-advanced-ns-frontier-boundary
  field
    positiveCellMassStillNovelCFDTarget : Bool
    positiveCellMassStillNovelCFDTargetIsFalse :
      positiveCellMassStillNovelCFDTarget ≡ false

    selectedDictionaryFrameBoundClosesCurrentNSFrontier : Bool
    selectedDictionaryFrameBoundClosesCurrentNSFrontierIsFalse :
      selectedDictionaryFrameBoundClosesCurrentNSFrontier ≡ false

    currentNSFrontierRequiresGramNegativity : Bool
    currentNSFrontierRequiresGramNegativityIsFalse :
      currentNSFrontierRequiresGramNegativity ≡ false

    currentNSFrontierRequiresPointwiseCutoffUniformSmallness : Bool
    currentNSFrontierRequiresPointwiseCutoffUniformSmallnessIsFalse :
      currentNSFrontierRequiresPointwiseCutoffUniformSmallness ≡ false

    currentNSFrontierIsCutoffUniformIntegratedCoherentBudget : Bool
    currentNSFrontierIsCutoffUniformIntegratedCoherentBudgetIsTrue :
      currentNSFrontierIsCutoffUniformIntegratedCoherentBudget ≡ true

    mixedHelicityFixedOutputCarrierIsLiveConsumer : Bool
    mixedHelicityFixedOutputCarrierIsLiveConsumerIsTrue :
      mixedHelicityFixedOutputCarrierIsLiveConsumer ≡ true

    dynamicCovarianceWallIsLiveAnalyticFrontier : Bool
    dynamicCovarianceWallIsLiveAnalyticFrontierIsTrue :
      dynamicCovarianceWallIsLiveAnalyticFrontier ≡ true

    finiteCFDRunClosesPackageAByItself : Bool
    finiteCFDRunClosesPackageAByItselfIsFalse :
      finiteCFDRunClosesPackageAByItself ≡ false

canonicalCFDAdvancedNSFrontierBoundary : CFDAdvancedNSFrontierBoundary
canonicalCFDAdvancedNSFrontierBoundary =
  cfd-advanced-ns-frontier-boundary
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl

------------------------------------------------------------------------
-- Branch-integration status.
------------------------------------------------------------------------

record CFDAdvancedNSBranchWeldStatus : Set where
  constructor cfd-advanced-ns-branch-weld-status
  field
    advancedNSOwnersCurrentlyLiveOnSeparatePR : Bool
    advancedNSOwnersCurrentlyLiveOnSeparatePRIsTrue :
      advancedNSOwnersCurrentlyLiveOnSeparatePR ≡ true

    copyOwnersIntoProgrammeLayer : Bool
    copyOwnersIntoProgrammeLayerIsFalse :
      copyOwnersIntoProgrammeLayer ≡ false

    joinByIdentityAdapterAfterNSBranchMerge : Bool
    joinByIdentityAdapterAfterNSBranchMergeIsTrue :
      joinByIdentityAdapterAfterNSBranchMerge ≡ true

canonicalCFDAdvancedNSBranchWeldStatus : CFDAdvancedNSBranchWeldStatus
canonicalCFDAdvancedNSBranchWeldStatus =
  cfd-advanced-ns-branch-weld-status
    true refl
    false refl
    true refl
