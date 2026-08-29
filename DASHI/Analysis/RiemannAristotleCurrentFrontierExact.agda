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

    -- Cross-lane reuse: generic finite Gram algebra already exists in NS Round180.
    round180ExactFiniteGramLedgerReusedForRH : Bool
    round180ExactFiniteGramLedgerReusedForRHIsTrue : round180ExactFiniteGramLedgerReusedForRH ≡ true
    rhToRound180CarrierAdapterClosedInAgda : Bool
    rhToRound180CarrierAdapterClosedInAgdaIsTrue : rhToRound180CarrierAdapterClosedInAgda ≡ true
    literalRHPostSchurCellsIdentifiedWithRound180Carrier : Bool
    literalRHPostSchurCellsIdentifiedWithRound180CarrierIsFalse : literalRHPostSchurCellsIdentifiedWithRound180Carrier ≡ false
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
    true refl true refl false refl false refl
    "The explicit-cutoff Lean tranche closes the infinite S2 tail and constructs the literal finite reflection-paired near carrier on D_off. Bidi reuse across the repo shows that the generic finite Gram theorem is already machine-checked in NS Round180: ||sum cells||^2 = cellMassSum + signed gramDebt, with no absolute-value or cardinality loss. The new RH adapter proves that once the literal three-taper post-Schur near contributions are identified with the same exact Complex3 carrier, Round180 supplies the Gram identity automatically. Thus the live S2 mathematics is narrower again: G1 identify the literal RH post-Schur near contributions with Round180 cells; G2 bound the resulting signed Gram debt strongly enough that diagonal mass plus signed covariance, together with the explicit far-error energy, lies below the S1 cluster margin. Reflection compression is already exhausted; no conjugation-orbit claim is made without a checked source API. S1, G1, G2, the joint margin, and low-ordinate certification remain open. RH is not derived."
