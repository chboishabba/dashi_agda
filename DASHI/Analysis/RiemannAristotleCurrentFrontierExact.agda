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

    -- G2 bidi decomposition.
    finiteGramDebtExpandedToOrderedPairCovarianceInAgda : Bool
    finiteGramDebtExpandedToOrderedPairCovarianceInAgdaIsTrue :
      finiteGramDebtExpandedToOrderedPairCovarianceInAgda ≡ true
    threeTaperSchurKernelBilinearCompilerClosedInAgda : Bool
    threeTaperSchurKernelBilinearCompilerClosedInAgdaIsTrue :
      threeTaperSchurKernelBilinearCompilerClosedInAgda ≡ true
    literalLeanElim2MatrixIdentifiedInAgda : Bool
    literalLeanElim2MatrixIdentifiedInAgdaIsFalse :
      literalLeanElim2MatrixIdentifiedInAgda ≡ false
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
    true refl true refl false refl false refl
    "The explicit-cutoff Lean tranche closes the infinite S2 tail and constructs the literal finite reflection-paired near carrier on D_off. G1 is closed at the type-correct scalar-generic level: the finite diagonal-plus-signed-Gram identity is inherited without identifying RH reals with NS rationals. G2 is now decomposed bidirectionally as well. RiemannAristotleFiniteNearOrderedPairGramDebtExact expands the finite Gram debt exactly to the signed ordered-pair covariance sum, with no absolute values. RiemannAristotleThreeTaperSchurKernelBilinearExact keeps the deterministic Schur map explicit and expands each post-Schur covariance in the raw three-taper coordinates. The reflection-pair Lean source already identifies each raw coordinate with the 4*g*cosh(a*u)*cos(delta*u) kernel and cancels the odd sinh*sin channel. The remaining representation seam is literal source provenance: identify Lean's actual elim2 with one fixed three-dimensional Schur operator E. After that, the only live S2 analysis is the signed finite oscillatory covariance bound strong enough to beat the remaining cluster margin. S1, the literal elim2 coefficient weld, the G2 signed covariance estimate, the joint margin, and low-ordinate certification remain open. RH is not derived."
