module DASHI.Analysis.RiemannAristotleCurrentFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record AristotleCurrentFrontier : Set where
  constructor aristotle-current-frontier
  field
    universalEvenConeConstructionClosedInLean : Bool
    universalEvenConeConstructionClosedInLeanIsTrue : universalEvenConeConstructionClosedInLean ≡ true
    twoRadiusOffLineDiscriminatorClosedInLean : Bool
    twoRadiusOffLineDiscriminatorClosedInLeanIsTrue : twoRadiusOffLineDiscriminatorClosedInLean ≡ true
    highOrdinatePrimeProjectiveDebtZeroInLean : Bool
    highOrdinatePrimeProjectiveDebtZeroInLeanIsTrue : highOrdinatePrimeProjectiveDebtZeroInLean ≡ true
    targetLeadingCoefficientAndRemainderClosedInLean : Bool
    targetLeadingCoefficientAndRemainderClosedInLeanIsTrue : targetLeadingCoefficientAndRemainderClosedInLean ≡ true
    reflectionPairKernelClosedInLean : Bool
    reflectionPairKernelClosedInLeanIsTrue : reflectionPairKernelClosedInLean ≡ true
    reflectionFarTailAbsoluteConvergenceClosedInLean : Bool
    reflectionFarTailAbsoluteConvergenceClosedInLeanIsTrue : reflectionFarTailAbsoluteConvergenceClosedInLean ≡ true
    uniformReflectionCarrierCurvatureClosedInLean : Bool
    uniformReflectionCarrierCurvatureClosedInLeanIsTrue : uniformReflectionCarrierCurvatureClosedInLean ≡ true
    latestLeanBridgeBuildKernelChecked : Bool
    latestLeanBridgeBuildKernelCheckedIsTrue : latestLeanBridgeBuildKernelChecked ≡ true
    wholePostSchurCarrierStrictBudgetIsContradictionTarget : Bool
    wholePostSchurCarrierStrictBudgetIsContradictionTargetIsTrue : wholePostSchurCarrierStrictBudgetIsContradictionTarget ≡ true
    eliminationAlgebraAloneClosesStrictBudget : Bool
    eliminationAlgebraAloneClosesStrictBudgetIsFalse : eliminationAlgebraAloneClosesStrictBudget ≡ false
    nearFarShellCompositionCompilerClosedInAgda : Bool
    nearFarShellCompositionCompilerClosedInAgdaIsTrue : nearFarShellCompositionCompilerClosedInAgda ≡ true
    nearFarAllowanceCompilerClosedInAgda : Bool
    nearFarAllowanceCompilerClosedInAgdaIsTrue : nearFarAllowanceCompilerClosedInAgda ≡ true
    jointCutoffCompilerClosedInAgda : Bool
    jointCutoffCompilerClosedInAgdaIsTrue : jointCutoffCompilerClosedInAgda ≡ true
    quantitativeFarShellEnvelopeClosed : Bool
    quantitativeFarShellEnvelopeClosedIsFalse : quantitativeFarShellEnvelopeClosed ≡ false
    explicitFarTailModulusTransportedToAgda : Bool
    explicitFarTailModulusTransportedToAgdaIsFalse : explicitFarTailModulusTransportedToAgda ≡ false
    finiteSignedNearShellCoreClosed : Bool
    finiteSignedNearShellCoreClosedIsFalse : finiteSignedNearShellCoreClosed ≡ false
    jointNearFarCutoffFound : Bool
    jointNearFarCutoffFoundIsFalse : jointNearFarCutoffFound ≡ false
    deterministicNuisanceThreeTaperConstructionClosed : Bool
    deterministicNuisanceThreeTaperConstructionClosedIsFalse : deterministicNuisanceThreeTaperConstructionClosed ≡ false
    lowOrdinateComplementCertified : Bool
    lowOrdinateComplementCertifiedIsFalse : lowOrdinateComplementCertified ≡ false
    finalRHImplicationClosed : Bool
    finalRHImplicationClosedIsFalse : finalRHImplicationClosed ≡ false

    -- Explicit-cutoff tranche. These are additive compatibility fields; the
    -- older public projections above are intentionally retained.
    deterministicProjectiveSchurKernelCheckedInLean : Bool
    deterministicProjectiveSchurKernelCheckedInLeanIsTrue : deterministicProjectiveSchurKernelCheckedInLean ≡ true
    explicitFarShellCutoffBoundClosedInLean : Bool
    explicitFarShellCutoffBoundClosedInLeanIsTrue : explicitFarShellCutoffBoundClosedInLean ≡ true
    explicitFarShellTendsToZeroClosedInLean : Bool
    explicitFarShellTendsToZeroClosedInLeanIsTrue : explicitFarShellTendsToZeroClosedInLean ≡ true
    finiteSignedNearCarrierClosedInLean : Bool
    finiteSignedNearCarrierClosedInLeanIsTrue : finiteSignedNearCarrierClosedInLean ≡ true
    literalDoffCutoffCarrierClosedInLean : Bool
    literalDoffCutoffCarrierClosedInLeanIsTrue : literalDoffCutoffCarrierClosedInLean ≡ true
    finiteNearCoreSchurPerturbationCompilerClosedInAgda : Bool
    finiteNearCoreSchurPerturbationCompilerClosedInAgdaIsTrue : finiteNearCoreSchurPerturbationCompilerClosedInAgda ≡ true
    explicitLeanTailFormulaTransportedAsAgdaProof : Bool
    explicitLeanTailFormulaTransportedAsAgdaProofIsFalse : explicitLeanTailFormulaTransportedAsAgdaProof ≡ false
    finiteSignedNearSchurCancellationClosed : Bool
    finiteSignedNearSchurCancellationClosedIsFalse : finiteSignedNearSchurCancellationClosed ≡ false
    jointFiniteNearFarMarginClosed : Bool
    jointFiniteNearFarMarginClosedIsFalse : jointFiniteNearFarMarginClosed ≡ false

    -- Bidi refinement after inspecting the literal finite carrier.
    finiteNearCarrierReflectionStableInLeanSource : Bool
    finiteNearCarrierReflectionStableInLeanSourceIsTrue : finiteNearCarrierReflectionStableInLeanSource ≡ true
    finiteNearSummandAlreadyReflectionPaired : Bool
    finiteNearSummandAlreadyReflectionPairedIsTrue : finiteNearSummandAlreadyReflectionPaired ≡ true
    finiteNearGramCancellationCompilerClosedInAgda : Bool
    finiteNearGramCancellationCompilerClosedInAgdaIsTrue : finiteNearGramCancellationCompilerClosedInAgda ≡ true
    literalFiniteNearGramIdentityInstantiated : Bool
    literalFiniteNearGramIdentityInstantiatedIsFalse : literalFiniteNearGramIdentityInstantiated ≡ false
    signedFiniteNearCrossTermEstimateClosed : Bool
    signedFiniteNearCrossTermEstimateClosedIsFalse : signedFiniteNearCrossTermEstimateClosed ≡ false
    conjugationOrbitCompressionOwned : Bool
    conjugationOrbitCompressionOwnedIsFalse : conjugationOrbitCompressionOwned ≡ false

    boundedReading : String

open AristotleCurrentFrontier public

canonicalAristotleCurrentFrontier : AristotleCurrentFrontier
canonicalAristotleCurrentFrontier =
  aristotle-current-frontier
    true refl true refl true refl true refl true refl true refl true refl true refl
    true refl false refl true refl true refl true refl
    false refl false refl false refl false refl false refl false refl false refl
    true refl true refl true refl true refl true refl true refl false refl false refl false refl
    true refl true refl true refl false refl false refl false refl
    "The explicit-cutoff Lean tranche closes the infinite S2 tail and constructs the literal finite nearOffFinset carrier on D_off. Source inspection further shows that nearOffFinset is reflection-stable because membership depends only on the ordinate gap, while reflection preserves the ordinate; the stored summand is already Z_sigma + Z_Rsigma, so reflection compression is exhausted and the odd-height channel is already cancelled. Agda now owns both the finite-near perturbation compiler and a finite signed Gram ledger that rewrites the post-Schur near energy as diagonal mass plus a signed twice-cross covariance term. The first unproved S2 analytic theorem is therefore the literal finite Gram identity/instantiation together with a signed bound on its cross term strong enough that the diagonal plus covariance budget, plus the explicit far error, lies below the S1 cluster margin. No conjugation-orbit theorem is claimed because no checked conjugation carrier API was identified. S1, the finite signed covariance estimate, the joint margin, and low-ordinate certification remain open. RH is not derived."
