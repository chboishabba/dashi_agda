module DASHI.Analysis.RiemannG2ReflectionPairSignedResidualLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- REFLECTION-PAIR SIGNED EXTERNAL RESIDUAL CUTSET
--
-- Companion Lean source proves that on the literal short-support projective
-- carrier an off-line target rho and its functional-equation partner contribute
-- the same nonnegative same-ordinate defect.  Every other same-ordinate defect
-- is also nonnegative.  Hence
--
--   2 D_rho <= D_cluster.
--
-- The exact literal projective balance gives
--
--   D_cluster = D_off + D_Gamma + D_pole.
--
-- Therefore the following single signed payment is contradictory:
--
--   D_off + D_Gamma + D_pole < 2 D_rho.
--
-- This route needs neither a finite/Fintype enumeration of SameOrd(t), nor
-- nuisance selection, nor a bound on a same-ordinate tail.  The whole
-- same-ordinate remainder is favorable before projection.
------------------------------------------------------------------------

record ReflectionPairSignedResidualLeanReceipt : Set where
  constructor reflection-pair-signed-residual-lean-receipt
  field
    repository : String
    branch : String
    sourcePath : String
    paymentTheorem : String
    channelCompilerTheorem : String
    highCompilerTheorem : String
    sourceCommit : String
    rootWiringCommit : String

open ReflectionPairSignedResidualLeanReceipt public

currentReflectionPairSignedResidualLeanReceipt :
  ReflectionPairSignedResidualLeanReceipt
currentReflectionPairSignedResidualLeanReceipt =
  reflection-pair-signed-residual-lean-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannReflectionPairSignedResidualCutset.lean"
    "Synthesis.false_of_reflectionPairSignedResidualPayment"
    "Synthesis.false_of_reflectionPairSignedChannelBounds"
    "Synthesis.high_zero_realPart_eq_half_of_reflectionPairSignedProducer"
    "09fd8412ed68f2a9b095b11ebd1de767338c6b88"
    "dbc1dc1530bdbf98a5eada94916c295b0e3746a1"

record ReflectionPairSignedResidualBoundary : Set where
  constructor reflection-pair-signed-residual-boundary
  field
    reflectionPartnerDoublesTargetSignalSourceWritten : Bool
    wholeSameOrdinateRemainderFavorableSourceWritten : Bool
    exactProjectiveExternalBalanceSourceOwned : Bool
    signedExternalResidualCutsetSourceWritten : Bool

    sameOrdinateFintypeRequired : Bool
    nuisanceSelectionPrimitiveOnThisRoute : Bool
    sameOrdinateResidualBudgetPrimitiveOnThisRoute : Bool
    schurProjectionPrimitiveOnThisRoute : Bool

    signedExternalResidualPaymentPaid : Bool
    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgda : Bool
    uniformHighContradictionPaid : Bool
    rhDerivedHere : Bool

open ReflectionPairSignedResidualBoundary public

canonicalReflectionPairSignedResidualBoundary :
  ReflectionPairSignedResidualBoundary
canonicalReflectionPairSignedResidualBoundary =
  reflection-pair-signed-residual-boundary
    true
    true
    true
    true

    false
    false
    false
    false

    false
    false
    false
    false
    false

sameOrdinateNuisanceNoLongerPrimitiveHere :
  ReflectionPairSignedResidualBoundary.nuisanceSelectionPrimitiveOnThisRoute
    canonicalReflectionPairSignedResidualBoundary ≡ false
sameOrdinateNuisanceNoLongerPrimitiveHere = refl

sameOrdinateBudgetNoLongerPrimitiveHere :
  ReflectionPairSignedResidualBoundary.sameOrdinateResidualBudgetPrimitiveOnThisRoute
    canonicalReflectionPairSignedResidualBoundary ≡ false
sameOrdinateBudgetNoLongerPrimitiveHere = refl

externalSignedResidualIsRemainingPayment :
  ReflectionPairSignedResidualBoundary.signedExternalResidualPaymentPaid
    canonicalReflectionPairSignedResidualBoundary ≡ false
externalSignedResidualIsRemainingPayment = refl
