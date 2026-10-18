module DASHI.Analysis.RiemannG2CenteredComplementCanonicalHighLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CANONICAL HIGH-ORDINATE CENTERED COMPLEMENT REDUCTION
--
-- Companion Lean source now combines:
--
--   * nonpositive centered finite-near reflection pairs inside the canonical
--     cosine window;
--   * the explicit far-only centered Off upper at
--       J = floor(|t|/9);
--   * the exact literal signed complement
--       S_h(t,0) = D_off(h,t,0) + Q_Gamma(h,t,0).
--
-- Therefore the centered literal-complement sign reduces to ONE remaining
-- Gamma-vs-far inequality:
--
--   Q_Gamma(h_r,t,0) <= - centeredOffHighEnvelope
--     -> S_{h_r}(t,0) <= 0.
--
-- No projective response/balance and no downstream final explicit-formula
-- balance enter this reduction.  In particular, an independent positive
-- finite-near budget is no longer primitive on this route.
------------------------------------------------------------------------

record CenteredComplementCanonicalHighLeanReceipt : Set where
  constructor centered-complement-canonical-high-lean-receipt
  field
    repository : String
    branch : String
    sourcePath : String
    theoremUpper : String
    theoremSignReduction : String
    sourceCommit : String

open CenteredComplementCanonicalHighLeanReceipt public

currentCenteredComplementCanonicalHighLeanReceipt :
  CenteredComplementCanonicalHighLeanReceipt
currentCenteredComplementCanonicalHighLeanReceipt =
  centered-complement-canonical-high-lean-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannCenteredComplementCanonicalHighUpper.lean"
    "Synthesis.exists_centeredLiteralComplement_canonicalHigh_upper"
    "Synthesis.exists_centeredLiteralComplement_sign_reduction"
    "4cc5193c0f78490aadf9769783dd9ebfd6e5a30d"

record CenteredComplementCanonicalHighBoundary : Set where
  constructor centered-complement-canonical-high-boundary
  field
    centeredFiniteNearPositiveRiskEliminated : Bool
    literalSignedComplementUsed : Bool
    explicitCanonicalFarEnvelopeUsed : Bool
    centeredComplementSignReducedToGammaVersusFar : Bool

    independentAdaptiveFiniteNearR2EstimatePrimitive : Bool
    projectiveBalanceImported : Bool
    finalBalanceUsedToManufactureAnalyticPayment : Bool

    gammaVersusFarLeafPaid : Bool
    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgda : Bool
    r2ClosedHere : Bool
    rhDerivedHere : Bool

open CenteredComplementCanonicalHighBoundary public

canonicalCenteredComplementCanonicalHighBoundary :
  CenteredComplementCanonicalHighBoundary
canonicalCenteredComplementCanonicalHighBoundary =
  centered-complement-canonical-high-boundary
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

centeredNearNoLongerPrimitiveR2Leaf :
  CenteredComplementCanonicalHighBoundary.independentAdaptiveFiniteNearR2EstimatePrimitive
    canonicalCenteredComplementCanonicalHighBoundary ≡ false
centeredNearNoLongerPrimitiveR2Leaf = refl

gammaVersusFarIsRemainingCenteredSignLeaf :
  CenteredComplementCanonicalHighBoundary.centeredComplementSignReducedToGammaVersusFar
    canonicalCenteredComplementCanonicalHighBoundary ≡ true
gammaVersusFarIsRemainingCenteredSignLeaf = refl
