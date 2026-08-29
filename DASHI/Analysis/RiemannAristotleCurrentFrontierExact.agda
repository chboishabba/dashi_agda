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

    -- Historical NS-specialized reuse. Round180 itself is rational Complex3,
    -- so a DIRECT literal RH-real -> Round180-rational identification remains
    -- false. It is retained as a boundary regression, not used as G1 closure.
    round180ExactFiniteGramLedgerReusedForRH : Bool
    round180ExactFiniteGramLedgerReusedForRHIsTrue : round180ExactFiniteGramLedgerReusedForRH ≡ true
    rhToRound180CarrierAdapterClosedInAgda : Bool
    rhToRound180CarrierAdapterClosedInAgdaIsTrue : rhToRound180CarrierAdapterClosedInAgda ≡ true
    literalRHPostSchurCellsIdentifiedWithRound180Carrier : Bool
    literalRHPostSchurCellsIdentifiedWithRound180CarrierIsFalse : literalRHPostSchurCellsIdentifiedWithRound180Carrier ≡ false

    -- Correct G1 closure: extract Round180's finite telescope to a scalar-
    -- generic exact Gram carrier, then weld the literal three-coordinate RH
    -- post-Schur cell to that generic carrier. No R -> Q coercion is used.
    genericFiniteSignedGramTelescopeExtractedInAgda : Bool
    genericFiniteSignedGramTelescopeExtractedInAgdaIsTrue :
      genericFiniteSignedGramTelescopeExtractedInAgda ≡ true
    literalRHPostSchurGenericGramWeldClosedInAgda : Bool
    literalRHPostSchurGenericGramWeldClosedInAgdaIsTrue :
      literalRHPostSchurGenericGramWeldClosedInAgda ≡ true

    signedRHGramDebtEstimateClosed : Bool
    signedRHGramDebtEstimateClosedIsFalse : signedRHGramDebtEstimateClosed ≡ false

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
    true refl true refl false refl
    true refl true refl
    false refl
    "The explicit-cutoff Lean tranche closes the infinite S2 tail and constructs the literal finite reflection-paired near carrier on D_off. Bidi reuse exposed a type boundary in the first Round180 idea: NS Round180 is specialized to rational Complex3 whereas literal RH responses are real, so direct RH-real -> Round180-rational identification remains correctly false. The reusable mathematics has now been extracted instead: FiniteSignedGramTelescopeExact proves the exact finite diagonal-plus-signed-Gram-debt identity over any exact polarized additive carrier, and RiemannAristotleLiteralPostSchurFiniteGramWeldExact maps the literal three-coordinate RH post-Schur shape definitionally into that generic theorem. Thus G1 is closed without an R-to-Q coercion. The only live S2 cancellation theorem is G2: bound the finite signed RH gramDebt strongly enough that diagonal mass plus signed covariance, together with the explicit far-error energy, lies below the surviving S1 cluster margin. S1, G2, the joint margin, and low-ordinate certification remain open. RH is not derived."
