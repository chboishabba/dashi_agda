module DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotleExplicitCutoffCarrierLeanReturnExact as LeanReturn
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar

------------------------------------------------------------------------
-- CHECKED LEAN CUTOFF THEOREM -> AGDA NEAR/FAR BUDGET TRANSPORT INTERFACE
--
-- The Lean return records that the literal every-cutoff split and far-tail
-- inequality were kernel-checked.  It does NOT transport those proof terms into
-- Agda.  This owner makes that cross-prover seam proof-relevant.
--
-- After this transport exists, the only new zero-side analytic theorem needed
-- to build NearFarOffOrdinateBudget at a selected cutoff is the near upper:
--
--   nearResponse(J) <= nearBudget(J).
------------------------------------------------------------------------

record ExplicitCutoffNearFarAgdaTransport
    (S : NearFar.OrderedAdditiveNearFarSurface) : Set₁ where
  field
    Taper Cutoff : Set
    universalPoleQuotientTaper : Taper

    fullResponse : Taper -> NearFar.Scalar S
    nearResponseAt farRemainderAt : Cutoff -> NearFar.Scalar S
    nearBudgetAt farBudgetAt : Cutoff -> NearFar.Scalar S

    fullBelowNearPlusFarAt :
      (J : Cutoff) ->
      NearFar._≤_ S
        (fullResponse universalPoleQuotientTaper)
        (NearFar.add S (nearResponseAt J) (farRemainderAt J))

    farUpperAt :
      (J : Cutoff) ->
      NearFar._≤_ S
        (farRemainderAt J)
        (farBudgetAt J)

    sameLeanOwner : Set
    sameLeanOwnerReceipt : sameLeanOwner

    sameLiteralOffResponse : Set
    sameLiteralOffResponseReceipt : sameLiteralOffResponse

    sameFiniteNearCarrier : Set
    sameFiniteNearCarrierReceipt : sameFiniteNearCarrier

    sameFarShellFormula : Set
    sameFarShellFormulaReceipt : sameFarShellFormula

    transportReference : String

open ExplicitCutoffNearFarAgdaTransport public

record FiniteNearUpperAt
    {S : NearFar.OrderedAdditiveNearFarSurface}
    (transport : ExplicitCutoffNearFarAgdaTransport S)
    (J : Cutoff transport) : Set where
  field
    nearUpper :
      NearFar._≤_ S
        (nearResponseAt transport J)
        (nearBudgetAt transport J)

    nearUpperReference : String

open FiniteNearUpperAt public

compileNearFarBudgetAt :
  forall {S} ->
  (transport : ExplicitCutoffNearFarAgdaTransport S) ->
  (J : Cutoff transport) ->
  FiniteNearUpperAt transport J ->
  NearFar.NearFarOffOrdinateBudget S
compileNearFarBudgetAt transport J near =
  NearFar.near-far-off-ordinate-budget
    (fullResponse transport (universalPoleQuotientTaper transport))
    (nearResponseAt transport J)
    (farRemainderAt transport J)
    (nearBudgetAt transport J)
    (farBudgetAt transport J)
    (fullBelowNearPlusFarAt transport J)
    (nearUpper near)
    (farUpperAt transport J)

compiledFullResponse :
  forall {S} ->
  (transport : ExplicitCutoffNearFarAgdaTransport S) ->
  (J : Cutoff transport) ->
  (near : FiniteNearUpperAt transport J) ->
  NearFar.fullResponse (compileNearFarBudgetAt transport J near)
  ≡ fullResponse transport (universalPoleQuotientTaper transport)
compiledFullResponse transport J near = refl

compiledNearBudget :
  forall {S} ->
  (transport : ExplicitCutoffNearFarAgdaTransport S) ->
  (J : Cutoff transport) ->
  (near : FiniteNearUpperAt transport J) ->
  NearFar.nearBudget (compileNearFarBudgetAt transport J near)
  ≡ nearBudgetAt transport J
compiledNearBudget transport J near = refl

compiledFarBudget :
  forall {S} ->
  (transport : ExplicitCutoffNearFarAgdaTransport S) ->
  (J : Cutoff transport) ->
  (near : FiniteNearUpperAt transport J) ->
  NearFar.farBudget (compileNearFarBudgetAt transport J near)
  ≡ farBudgetAt transport J
compiledFarBudget transport J near = refl

------------------------------------------------------------------------
-- Exact trust/frontier boundary.
------------------------------------------------------------------------

checkedLeanEveryCutoffSplitOwned :
  LeanReturn.explicitEveryCutoffBoundOwned
    LeanReturn.canonicalExplicitCutoffCarrierLeanReturn ≡ true
checkedLeanEveryCutoffSplitOwned = refl

checkedLeanFarTailFormulaOwned :
  LeanReturn.explicitFarShellFormulaOwned
    LeanReturn.canonicalExplicitCutoffCarrierLeanReturn ≡ true
checkedLeanFarTailFormulaOwned = refl

checkedLeanProofNotYetAgdaProof :
  LeanReturn.leanProofTransportedIntoAgda
    LeanReturn.canonicalExplicitCutoffCarrierLeanReturn ≡ false
checkedLeanProofNotYetAgdaProof = refl

record ExplicitCutoffNearFarAgdaTransportBoundary : Set where
  constructor explicit-cutoff-near-far-agda-transport-boundary
  field
    checkedLeanSplitAndFarBoundExist : Bool
    checkedLeanSplitAndFarBoundExistIsTrue :
      checkedLeanSplitAndFarBoundExist ≡ true

    checkedLeanBooleanStatusInhabitsAgdaInequality : Bool
    checkedLeanBooleanStatusInhabitsAgdaInequalityIsFalse :
      checkedLeanBooleanStatusInhabitsAgdaInequality ≡ false

    crossProverSplitFarTransportStillRequired : Bool
    crossProverSplitFarTransportStillRequiredIsTrue :
      crossProverSplitFarTransportStillRequired ≡ true

    afterTransportOnlyNearUpperIsFreshBudgetField : Bool
    afterTransportOnlyNearUpperIsFreshBudgetFieldIsTrue :
      afterTransportOnlyNearUpperIsFreshBudgetField ≡ true

    nearFarBudgetCompilerClosedConditionally : Bool
    nearFarBudgetCompilerClosedConditionallyIsTrue :
      nearFarBudgetCompilerClosedConditionally ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalExplicitCutoffNearFarAgdaTransportBoundary :
  ExplicitCutoffNearFarAgdaTransportBoundary
canonicalExplicitCutoffNearFarAgdaTransportBoundary =
  explicit-cutoff-near-far-agda-transport-boundary
    true refl
    false refl
    true refl
    true refl
    true refl
    false refl
    "The checked Lean cutoff return owns the literal every-J off = near + far control and explicit far-shell theorem, but its status Booleans are not Agda inequality proofs. Transport those checked theorem statements/proofs into the final Agda ordered-additive carrier once. After that transport, NearFarOffOrdinateBudget at a chosen J requires only one genuinely fresh zero-side analytic field: nearResponse(J) <= nearBudget(J). The constructor then compiles the full split and far upper mechanically. RH is not derived."
