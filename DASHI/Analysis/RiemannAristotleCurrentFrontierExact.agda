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

    round180ExactFiniteGramLedgerReusedForRH : Bool
    round180ExactFiniteGramLedgerReusedForRHIsTrue : round180ExactFiniteGramLedgerReusedForRH ≡ true
    rhToRound180CarrierAdapterClosedInAgda : Bool
    rhToRound180CarrierAdapterClosedInAgdaIsTrue : rhToRound180CarrierAdapterClosedInAgda ≡ true
    literalRHPostSchurCellsIdentifiedWithRound180Carrier : Bool
    literalRHPostSchurCellsIdentifiedWithRound180CarrierIsFalse : literalRHPostSchurCellsIdentifiedWithRound180Carrier ≡ false

    genericFiniteSignedGramTelescopeExtractedInAgda : Bool
    genericFiniteSignedGramTelescopeExtractedInAgdaIsTrue :
      genericFiniteSignedGramTelescopeExtractedInAgda ≡ true
    literalRHPostSchurGenericGramWeldClosedInAgda : Bool
    literalRHPostSchurGenericGramWeldClosedInAgdaIsTrue :
      literalRHPostSchurGenericGramWeldClosedInAgda ≡ true

    finiteGramDebtExpandedToOrderedPairCovarianceInAgda : Bool
    finiteGramDebtExpandedToOrderedPairCovarianceInAgdaIsTrue :
      finiteGramDebtExpandedToOrderedPairCovarianceInAgda ≡ true
    threeTaperSchurKernelBilinearCompilerClosedInAgda : Bool
    threeTaperSchurKernelBilinearCompilerClosedInAgdaIsTrue :
      threeTaperSchurKernelBilinearCompilerClosedInAgda ≡ true
    literalLeanElim2MatrixIdentifiedInAgda : Bool
    literalLeanElim2MatrixIdentifiedInAgdaIsFalse :
      literalLeanElim2MatrixIdentifiedInAgda ≡ false

    determinantScalarizationCompilerClosedInAgda : Bool
    determinantScalarizationCompilerClosedInAgdaIsTrue :
      determinantScalarizationCompilerClosedInAgda ≡ true
    literalLeanBilinearDeterminantIdentitySupplied : Bool
    literalLeanBilinearDeterminantIdentitySuppliedIsFalse :
      literalLeanBilinearDeterminantIdentitySupplied ≡ false

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
    true refl true refl false refl
    true refl false refl
    false refl
    "The explicit-cutoff Lean tranche closes the infinite S2 tail and constructs the literal finite reflection-paired near carrier on D_off. G1 is closed at the type-correct scalar-generic level. G2a now expands finite Gram debt exactly to the signed ordered-pair covariance sum; G2b keeps the deterministic Schur map explicit and expands every post-Schur covariance in raw three-taper coordinates. The reflection-pair Lean source supplies each raw coordinate through the 4*g*cosh(a*u)*cos(delta*u) kernel with the odd sinh*sin channel already cancelled. A stronger one-dimensional compiler is also ready: if Lean supplies the exact bilinear determinant identity <E x,E y> = det(n1,n2,x) det(n1,n2,y) / wedgeSq(n1,n2), Agda automatically converts the whole finite Schur covariance to a scalar determinant covariance. That identity is not claimed here. The remaining leaves are therefore source-identification of the literal elim2/determinant bilinear form and the genuine signed finite oscillatory covariance estimate; S1, the joint margin, low-ordinate certification, and RH remain open."
