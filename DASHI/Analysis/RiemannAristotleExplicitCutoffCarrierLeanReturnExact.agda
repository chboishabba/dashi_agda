module DASHI.Analysis.RiemannAristotleExplicitCutoffCarrierLeanReturnExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record ExplicitCutoffCarrierLeanReturn : Set where
  constructor explicit-cutoff-carrier-lean-return
  field
    owner : String
    farShellModule : String
    nearFarModule : String
    literalOffOrdModule : String
    leanKernelChecked : Bool
    leanKernelCheckedIsTrue : leanKernelChecked ≡ true
    aggregateBuildJobsReported : String
    axiomAuditStandardOnly : Bool
    axiomAuditStandardOnlyIsTrue : axiomAuditStandardOnly ≡ true
    explicitFarShellFormulaOwned : Bool
    explicitFarShellFormulaOwnedIsTrue : explicitFarShellFormulaOwned ≡ true
    explicitEveryCutoffBoundOwned : Bool
    explicitEveryCutoffBoundOwnedIsTrue : explicitEveryCutoffBoundOwned ≡ true
    farShellTendsToZeroOwned : Bool
    farShellTendsToZeroOwnedIsTrue : farShellTendsToZeroOwned ≡ true
    arbitraryAccuracyCutoffOwned : Bool
    arbitraryAccuracyCutoffOwnedIsTrue : arbitraryAccuracyCutoffOwned ≡ true
    finiteSignedNearCarrierOwned : Bool
    finiteSignedNearCarrierOwnedIsTrue : finiteSignedNearCarrierOwned ≡ true
    literalDoffCutoffTransportOwned : Bool
    literalDoffCutoffTransportOwnedIsTrue : literalDoffCutoffTransportOwned ≡ true
    leanProofTransportedIntoAgda : Bool
    leanProofTransportedIntoAgdaIsFalse : leanProofTransportedIntoAgda ≡ false
    finiteSignedNearCancellationClosed : Bool
    finiteSignedNearCancellationClosedIsFalse : finiteSignedNearCancellationClosed ≡ false
    riemannHypothesisDerived : Bool
    riemannHypothesisDerivedIsFalse : riemannHypothesisDerived ≡ false
    explicitFormula : String
    boundedReading : String

open ExplicitCutoffCarrierLeanReturn public

canonicalExplicitCutoffCarrierLeanReturn : ExplicitCutoffCarrierLeanReturn
canonicalExplicitCutoffCarrierLeanReturn =
  explicit-cutoff-carrier-lean-return
    "Aristotle / Zeta23Bridge Lean"
    "FarShellCutoffTailBound.lean"
    "NearFarCarrierSplit.lean"
    "OffOrdinateCutoffCarrier.lean"
    true refl
    "8883"
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "farShellBound A |t| J = 18*A*log(|t|+4)/J + 72*A/sqrt(J)"
    "Lean now closes the infinite S2 tail quantitatively at every cutoff J and transports the finite-near-plus-explicit-far decomposition onto the literal offOrdProjectiveDefect. The remaining analytic content is finite signed cancellation for the nearOffFinset carrier, together with the three-taper Schur observer and final joint margin. No Lean proof term is promoted into Agda by this status owner."
