module DASHI.Unified.YMA1SourceFrontierExact where

------------------------------------------------------------------------
-- CANONICAL ROW-A1 SOURCE FRONTIER
--
-- This module normalizes existing Yang-Mills A1 theorem owners.
-- It adds no new analytic estimate.
-- It keeps Agda as theorem authority.
-- It keeps Lean results as cross-prover evidence only.
--
-- Primary sources:
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Commun. Math. Phys. 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Commun. Math. Phys. 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Current source-native Gaussian object:
--
--   Ahat(U) = C(U)^* A(U) C(U).
--
-- Current first-variation identity:
--
--   D Ahat = C'^* A C + C^* A' C + C^* A C'.
--
-- Current finite-g route:
--
--   beta >= b_fixed - C_beta gamma^4.
--
-- Existing arithmetic chooses a positive gamma when b_fixed > 0 and C_beta is
-- finite and nonnegative.  Therefore the current Row-A1 work is source
-- identification and uniformity.  It is not another absorption calculation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.YangMills.CompactLieProofLevel as Proof
import DASHI.Physics.YangMills.BalabanCMP109DirectBetaSourceRegression as Direct
import DASHI.Physics.YangMills.BalabanRowARecentLeanCrossProverProgressExact as Cross
import DASHI.Physics.YangMills.BalabanYM4RowALiteralProducerAdapterExact as Producer
import DASHI.Unified.YMImplementAToDTOEMaxCutExact as Gate4

------------------------------------------------------------------------
-- ZKP governance frame.
--
-- O/R/C/S/L/P/G/F are labels.
-- Preconditions, invariants, and postconditions are explicit text receipts.
-- They do not replace theorem types.
------------------------------------------------------------------------

record YMA1ZKPFrame : Set where
  field
    O-organization : String
    R-request : String
    C-code : String
    S-state : String
    L-lattice : String
    P-proposal : String
    G-governance : String
    F-gap : String

    preconditions : List String
    invariants : List String
    postconditions : List String

open YMA1ZKPFrame public

canonicalYMA1ZKPFrame : YMA1ZKPFrame
canonicalYMA1ZKPFrame = record
  { O-organization =
      "DASHI TOE / Yang-Mills / Row A1 / Bałaban source frontier"
  ; R-request =
      "Reuse existing A1 owners. Identify the literal fixed-coordinate Gaussian and the history-uniform finite-g remainder."
  ; C-code =
      "Agda is golden. Lean is a non-promoting mirror. Reuse, deduplicate, extend, then construct."
  ; S-state =
      "Mixed Wilson 64-atom algebra, tangent trivialization, eliminated-coordinate algebra, tangential trace cancellation, and small-coupling absorption are compiler-paid. Literal source welds remain open."
  ; L-lattice =
      "CMP98 averaging -> CMP99 constrained coordinates -> CMP109 fixed Gaussian C*AC -> direct beta projection -> history-uniform quartic remainder."
  ; P-proposal =
      "Close the literal source identifications. Do not add a second A1 ontology."
  ; G-governance =
      "Fail closed. Preserve attribution. Do not edit ESD surfaces. Keep zkperf, zos-server, erdfa-py, and aristotle-cli-rs as separately attributed meta-introspector donors, not theorem authority. Use deterministic verification and exact non-promotion."
  ; F-gap =
      "Open source producers are literal Q prime and pivot data, the same-object C*AC weld and positive patch, history-uniform five-channel source control, and the cumulative beta sensitivity q<1 reported by the Lean lane."
  ; preconditions =
      "All theorem owners are on the same repository branch."
      ∷ "The fixed-coordinate Gaussian is the CMP109/CMP99 source object."
      ∷ "Cross-prover Lean results are evidence only."
      ∷ []
  ; invariants =
      "Conditional proof levels do not self-promote."
      ∷ "Finite lattice results do not imply continuum Yang-Mills."
      ∷ "The 58 formal-gap fleet scope remains separate from physical promotion."
      ∷ "No ESD theorem authority is introduced."
      ∷ []
  ; postconditions =
      "The current A1 compiler results are reachable from one Unified surface."
      ∷ "The current A1 physical blockers remain explicit."
      ∷ "The frozen A/B/C/D research count remains four."
      ∷ "Row A remains non-promoted until literal source producers are inhabited in Agda."
      ∷ []
  }

------------------------------------------------------------------------
-- Canonical receipt.
------------------------------------------------------------------------

record YMA1SourceFrontierReceipt : Set where
  field
    eliminatedCoordinateDerivativeCompiler : Proof.ProofLevel
    eliminatedPivotDerivativeCompiler : Proof.ProofLevel
    mixedWilson64AtomCompiler : Proof.ProofLevel
    wilsonTrivializationCompiler : Proof.ProofLevel
    tangentialTraceCancellationCompiler : Proof.ProofLevel
    explicitSmallCouplingAbsorptionCompiler : Proof.ProofLevel

    literalCMP98QPrime : Proof.ProofLevel
    literalCoordinateEmbeddingVariation : Proof.ProofLevel
    literalRestrictedThreeTermVariation : Proof.ProofLevel
    literalWilsonFourierSymbol : Proof.ProofLevel
    literalFixedCoordinatePositivePatch : Proof.ProofLevel
    literalFiveChannelUniformOverHistory : Proof.ProofLevel
    literalCumulativeBetaSensitivityBelowOne : Proof.ProofLevel

    rowACompletion : Proof.ProofLevel

    gate4FormalGapCount : Nat
    gate4FormalGapCountIs58 : gate4FormalGapCount ≡ 58

    frozenResearchCount : Nat
    frozenResearchCountIsFour : frozenResearchCount ≡ 4

    rowAPromoted : Bool
    rowAPromotedIsFalse : rowAPromoted ≡ false

open YMA1SourceFrontierReceipt public

canonicalYMA1SourceFrontierReceipt : YMA1SourceFrontierReceipt
canonicalYMA1SourceFrontierReceipt = record
  { eliminatedCoordinateDerivativeCompiler =
      Direct.eliminatedCoordinateDerivativeAlgebraRegressionLevel
  ; eliminatedPivotDerivativeCompiler =
      Direct.eliminatedPivotDerivativeAlgebraRegressionLevel
  ; mixedWilson64AtomCompiler =
      Direct.wilsonBackgroundQuadratic64AtomRegressionLevel
  ; wilsonTrivializationCompiler =
      Direct.wilsonBackgroundTrivializationRegressionLevel
  ; tangentialTraceCancellationCompiler =
      Direct.tangentialConnectionTraceRegressionLevel
  ; explicitSmallCouplingAbsorptionCompiler =
      Direct.explicitSmallCouplingQuarticAbsorptionRegressionLevel

  ; literalCMP98QPrime =
      Direct.literalCMP98OneStepQPrimeRegressionLevel
  ; literalCoordinateEmbeddingVariation =
      Direct.literalCoordinateEmbeddingVariationRegressionLevel
  ; literalRestrictedThreeTermVariation =
      Direct.literalRestrictedThreeTermVariationRegressionLevel
  ; literalWilsonFourierSymbol =
      Direct.literalMixedWilson64AtomFourierSymbolRegressionLevel
  ; literalFixedCoordinatePositivePatch =
      Direct.literalFixedCoordinatePositivePatchRegressionLevel
  ; literalFiveChannelUniformOverHistory =
      Direct.literalFiveChannelUniformOverHistoryRegressionLevel
  ; literalCumulativeBetaSensitivityBelowOne =
      Cross.literalCumulativeBetaSensitivityQStrictlyBelowOneCurrentLevel

  ; rowACompletion =
      Cross.rowACompletionAfterRecentCrossProverProgressLevel

  ; gate4FormalGapCount =
      Gate4.gate4UnresolvedCount Gate4.canonicalYMImplementAToDTOEMaxCutReceipt
  ; gate4FormalGapCountIs58 =
      Gate4.gate4UnresolvedCountIs58 Gate4.canonicalYMImplementAToDTOEMaxCutReceipt

  ; frozenResearchCount =
      Direct.currentFrozenResearchCountRegression
  ; frozenResearchCountIsFour =
      refl

  ; rowAPromoted =
      false
  ; rowAPromotedIsFalse =
      refl
  }

------------------------------------------------------------------------
-- Exact authority and non-promotion checks.
------------------------------------------------------------------------

rowACompletionDoesNotSelfPromote :
  Proof.promotable
    (rowACompletion canonicalYMA1SourceFrontierReceipt)
  ≡ false
rowACompletionDoesNotSelfPromote =
  Proof.conditionalDoesNotSelfPromote

literalCumulativeSensitivityDoesNotSelfPromote :
  Proof.promotable
    (literalCumulativeBetaSensitivityBelowOne
      canonicalYMA1SourceFrontierReceipt)
  ≡ false
literalCumulativeSensitivityDoesNotSelfPromote =
  Proof.conditionalDoesNotSelfPromote

gate4FormalGapCountStill58 :
  gate4FormalGapCount canonicalYMA1SourceFrontierReceipt ≡ 58
gate4FormalGapCountStill58 =
  gate4FormalGapCountIs58 canonicalYMA1SourceFrontierReceipt

frozenResearchCountStillFour :
  frozenResearchCount canonicalYMA1SourceFrontierReceipt ≡ 4
frozenResearchCountStillFour =
  frozenResearchCountIsFour canonicalYMA1SourceFrontierReceipt

rowAStillNotPromoted :
  rowAPromoted canonicalYMA1SourceFrontierReceipt ≡ false
rowAStillNotPromoted =
  rowAPromotedIsFalse canonicalYMA1SourceFrontierReceipt

------------------------------------------------------------------------
-- Existing literal-producer adapter remains the preferred finite source shape.
------------------------------------------------------------------------

rowALiteralProducerCompilerLevel : Proof.ProofLevel
rowALiteralProducerCompilerLevel =
  Producer.rowALiteralProducerCanonicalGammaLevel

rowALiteralProducerSameObjectIdentificationLevel : Proof.ProofLevel
rowALiteralProducerSameObjectIdentificationLevel =
  Producer.literalRowAProducerSameObjectIdentificationLevel
