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

    -- New 2026-08-30 explicit-cutoff tranche.  These are additive compatibility
    -- fields; the older public projections above are intentionally retained.
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

    boundedReading : String

open AristotleCurrentFrontier public

canonicalAristotleCurrentFrontier : AristotleCurrentFrontier
canonicalAristotleCurrentFrontier =
  aristotle-current-frontier
    true refl true refl true refl true refl true refl true refl true refl true refl
    true refl false refl true refl true refl true refl
    false refl false refl false refl false refl false refl false refl false refl
    true refl true refl true refl true refl true refl true refl false refl false refl false refl
    "The newest kernel-checked Lean tranche closes an explicit every-cutoff far-shell modulus, its decay to zero, a genuinely finite signed near carrier, and transport of that decomposition onto literal D_off. The deterministic projective Schur compiler is also now covered by the reported 8883-job aggregate build. Agda preserves the previous near/far compiler API and adds a finite post-Schur perturbation consumer. The first unproved S2 theorem is now a signed bound on ||E D_near(J)||^2 strong enough that, together with the explicit far-error energy, it lies below the surviving S1 cluster margin. The infinite zero tail is no longer the research bottleneck; S1, the finite signed near-Schur estimate, the joint margin, and low-ordinate certification remain open. RH is not derived."
