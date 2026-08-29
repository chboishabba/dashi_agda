module DASHI.Analysis.RiemannAristotleG2CurrentCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

record AristotleG2CurrentCut : Set where
  constructor aristotle-g2-current-cut
  field
    g1ThreeCoordinateToGenericGramClosed : Bool
    g1ThreeCoordinateToGenericGramClosedIsTrue :
      g1ThreeCoordinateToGenericGramClosed ≡ true

    g2aOrderedPairGramDebtClosed : Bool
    g2aOrderedPairGramDebtClosedIsTrue : g2aOrderedPairGramDebtClosed ≡ true

    g2bRawThreeTaperBilinearCompilerClosed : Bool
    g2bRawThreeTaperBilinearCompilerClosedIsTrue :
      g2bRawThreeTaperBilinearCompilerClosed ≡ true

    checkedLeanNormDeterminantIdentityExists : Bool
    checkedLeanNormDeterminantIdentityExistsIsTrue :
      checkedLeanNormDeterminantIdentityExists ≡ true

    g2cPolarizationDerivationClosedInAgda : Bool
    g2cPolarizationDerivationClosedInAgdaIsTrue :
      g2cPolarizationDerivationClosedInAgda ≡ true

    g2cFreshLeanBilinearKernelReceiptPresent : Bool
    g2cFreshLeanBilinearKernelReceiptPresentIsFalse :
      g2cFreshLeanBilinearKernelReceiptPresent ≡ false

    reflectionPairOddSinhSinCancellationClosedInLean : Bool
    reflectionPairOddSinhSinCancellationClosedInLeanIsTrue :
      reflectionPairOddSinhSinCancellationClosedInLean ≡ true

    reflectionOnlyForcesRemainingGramCancellation : Bool
    reflectionOnlyForcesRemainingGramCancellationIsFalse :
      reflectionOnlyForcesRemainingGramCancellation ≡ false

    g2dReducedToSingleSignedScalarDeterminantSum : Bool
    g2dReducedToSingleSignedScalarDeterminantSumIsTrue :
      g2dReducedToSingleSignedScalarDeterminantSum ≡ true

    g2dAdditionalOrdinatePhaseCancellationBoundClosed : Bool
    g2dAdditionalOrdinatePhaseCancellationBoundClosedIsFalse :
      g2dAdditionalOrdinatePhaseCancellationBoundClosed ≡ false

    genericGramOrSchurAlgebraRemaining : Bool
    genericGramOrSchurAlgebraRemainingIsFalse :
      genericGramOrSchurAlgebraRemaining ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    boundedReading : String

open AristotleG2CurrentCut public

canonicalAristotleG2CurrentCut : AristotleG2CurrentCut
canonicalAristotleG2CurrentCut =
  aristotle-g2-current-cut
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
    "G1, G2a and G2b are closed at source level. G2c is no longer an open mathematical identity: ThreeTaperSchurMargin.lean already owns normSqP(elim2 x)=det3(n1,n2,x)^2/wedgeSq, and exact polarization plus elim2/determinant additivity yields the bilinear determinant formula. A fresh Lean kernel receipt for that stitched theorem is still absent. The G2d bidi audit rejects reflection-only cancellation because each stored near cell is already reflection paired and hence reflection invariant, producing positive duplicate covariance on a non-fixed reflection orbit. The final analytic leaf is therefore one additional signed ordinate/phase cancellation estimate for the scalar responses d_sigma=det3(n1,n2,k_sigma), equivalently a bound on sum d_sigma strong enough to beat the cluster determinant margin after the explicit far error. No generic Gram or Schur algebra remains, and RH is not derived."
