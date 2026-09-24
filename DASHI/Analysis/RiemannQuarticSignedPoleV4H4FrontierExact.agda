module DASHI.Analysis.RiemannQuarticSignedPoleV4H4FrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- RH CLAY-FACING V4 / H4 RECUT OWNER
--
-- This module supersedes the older reading in
--
--   RiemannQuarticSignedPoleBidiMarkedFourthExact
--
-- that treated a localized target-centred Montgomery producer as the
-- mandatory next analytic theorem.
--
-- The newer Lean tranche splits the literal centred fourth-angular statistic
-- into
--
--   A4_local = V4 + H4,
--
-- with
--
--   V4
--     = sum m_rho (gamma_rho-t)^4
--         - integral (x-t)^4 mu(x) dx,
--
--   H4
--     = sum m_rho a_rho^2
--         (a_rho^2 - 6 (gamma_rho-t)^2).
--
-- V4 is source-written in Lean by specializing the already-owned literal
-- N-mu Abel identity to phi_t(x)=(x-t)^4 and combining it with the existing
-- arbitrary-endpoint RvM discrepancy theorem.
--
-- The source-written generic compiler is
--
--   |V4(t,r)| <= 9 r^4 E
--
-- whenever the cumulative N-mu discrepancy from the left endpoint is bounded
-- by E throughout the symmetric window.
--
-- H4 now has a sharper signed recut.  Define the adverse cone by
--
--   6 delta^2 < a^2.
--
-- Outside this cone the exact H4 summand is nonpositive.  Inside it,
--
--   a^2(a^2-6 delta^2) <= a^4.
--
-- The adverse cone is a subset of the already-owned broader local cone, where
-- the zeta strip theorem gives |a|<=1/2.  Therefore each adverse envelope is
-- at most 1/16 times multiplicity, and the existing fixed-window local zero
-- count supplies an unconditional O(log t) finite H4 upper bound.
--
-- IMPORTANT TRUST BOUNDARY
--
-- These V4/H4 quantitative facts are Lean source-written donors.  This Agda
-- module records the authoritative programme state and does NOT claim that
-- those analytic proofs have been independently replayed by the Agda kernel.
--
-- Montgomery / marked-pair machinery remains a retained optional alternative,
-- not a Clay-facing required premise.
------------------------------------------------------------------------

data V4H4Coordinate : Set where
  exactVerticalHorizontalFourthSplit : V4H4Coordinate
  verticalFourthLiteralNMuAbelSpecialization : V4H4Coordinate
  verticalFourthNineR4ECompiler : V4H4Coordinate
  verticalFourthArbitraryEndpointRvMProducer : V4H4Coordinate

  horizontalExactPolynomial : V4H4Coordinate
  horizontalAdverseConeSignSplit : V4H4Coordinate
  horizontalAdverseConeFourthEnvelope : V4H4Coordinate
  horizontalAdverseConeSubsetExistingLocalCone : V4H4Coordinate
  horizontalFiniteLocalCountBound : V4H4Coordinate

  localizedMontgomeryProducer : V4H4Coordinate
  finiteV4CarrierWeld : V4H4Coordinate
  finalSignedAbsorption : V4H4Coordinate
  terminalG3Compiler : V4H4Coordinate

data V4H4Status : Set where
  theoremOwned : V4H4Status
  leanSourceWrittenDonor : V4H4Status
  optionalAlternative : V4H4Status
  openAssembly : V4H4Status
  openAnalyticObstruction : V4H4Status
  compilerOwned : V4H4Status

v4h4Status : V4H4Coordinate -> V4H4Status
v4h4Status exactVerticalHorizontalFourthSplit = theoremOwned

v4h4Status verticalFourthLiteralNMuAbelSpecialization =
  leanSourceWrittenDonor
v4h4Status verticalFourthNineR4ECompiler =
  leanSourceWrittenDonor
v4h4Status verticalFourthArbitraryEndpointRvMProducer =
  leanSourceWrittenDonor

v4h4Status horizontalExactPolynomial = theoremOwned
v4h4Status horizontalAdverseConeSignSplit =
  leanSourceWrittenDonor
v4h4Status horizontalAdverseConeFourthEnvelope =
  leanSourceWrittenDonor
v4h4Status horizontalAdverseConeSubsetExistingLocalCone =
  leanSourceWrittenDonor
v4h4Status horizontalFiniteLocalCountBound =
  leanSourceWrittenDonor

v4h4Status localizedMontgomeryProducer = optionalAlternative
v4h4Status finiteV4CarrierWeld = openAssembly
v4h4Status finalSignedAbsorption = openAnalyticObstruction
v4h4Status terminalG3Compiler = compilerOwned

record V4H4Boundary : Set where
  constructor v4-h4-boundary
  field
    exactVerticalHorizontalFourthSplitPaid : Bool

    verticalFourthLiteralNMuAbelSourceWritten : Bool
    verticalFourthNineR4ECompilerSourceWritten : Bool
    verticalFourthArbitraryEndpointRvMSourceWritten : Bool

    horizontalExactPolynomialPaid : Bool
    horizontalAdverseConeSignSplitSourceWritten : Bool
    horizontalAdverseConeFourthEnvelopeSourceWritten : Bool
    horizontalAdverseConeSubsetExistingConeSourceWritten : Bool
    horizontalFiniteLocalCountBoundSourceWritten : Bool

    localizedMontgomeryRequired : Bool
    finiteV4CarrierWeldPaid : Bool
    finalSignedAbsorptionPaid : Bool
    terminalG3CompilerPaid : Bool

    exactVerticalHorizontalFourthSplitPaidIsTrue :
      exactVerticalHorizontalFourthSplitPaid ≡ true

    verticalFourthLiteralNMuAbelSourceWrittenIsTrue :
      verticalFourthLiteralNMuAbelSourceWritten ≡ true
    verticalFourthNineR4ECompilerSourceWrittenIsTrue :
      verticalFourthNineR4ECompilerSourceWritten ≡ true
    verticalFourthArbitraryEndpointRvMSourceWrittenIsTrue :
      verticalFourthArbitraryEndpointRvMSourceWritten ≡ true

    horizontalExactPolynomialPaidIsTrue :
      horizontalExactPolynomialPaid ≡ true
    horizontalAdverseConeSignSplitSourceWrittenIsTrue :
      horizontalAdverseConeSignSplitSourceWritten ≡ true
    horizontalAdverseConeFourthEnvelopeSourceWrittenIsTrue :
      horizontalAdverseConeFourthEnvelopeSourceWritten ≡ true
    horizontalAdverseConeSubsetExistingConeSourceWrittenIsTrue :
      horizontalAdverseConeSubsetExistingConeSourceWritten ≡ true
    horizontalFiniteLocalCountBoundSourceWrittenIsTrue :
      horizontalFiniteLocalCountBoundSourceWritten ≡ true

    localizedMontgomeryRequiredIsFalse :
      localizedMontgomeryRequired ≡ false
    finiteV4CarrierWeldPaidIsFalse :
      finiteV4CarrierWeldPaid ≡ false
    finalSignedAbsorptionPaidIsFalse :
      finalSignedAbsorptionPaid ≡ false
    terminalG3CompilerPaidIsTrue :
      terminalG3CompilerPaid ≡ true

    interpretation : String
    nextResearchCut : String
    trustBoundary : String

canonicalV4H4Boundary : V4H4Boundary
canonicalV4H4Boundary =
  v4-h4-boundary
    true
    true true true
    true true true true true
    false false false true
    refl
    refl refl refl
    refl refl refl refl refl
    refl refl refl refl
    "The preferred Clay-facing local fourth-angular route is now V4 plus H4, not a mandatory localized Montgomery theorem. V4 is an ordinary literal N-mu/RvM Abel specialization with a source-written 9*r^4*E compiler. H4 preserves sign: only 6*delta^2<a^2 can contribute positively, and that adverse cone is paid above by an a^4 envelope plus the existing fixed-window local zero-count theorem. The old marked 0/2/4 producer remains available only as an optional alternative."
    "First weld the literal finite centred vertical fourth carrier used by the angular obstruction to the theorem-bearing Zeta23 window V4 object (or prove the exact eventual/cofinal equality already implicit in the finite exhaustion). Then perform the final signed absorption with the existing sixth-order debt and FarExact kept signed. Do not reintroduce Montgomery as a required hypothesis."
    "V4 and the new adverse-cone H4 estimates are Lean source-written donors only. This owner is an Agda programme/status theorem and does not claim independent Agda-kernel replay of those analytic Lean proofs."

montgomeryProducerIsOptional :
  v4h4Status localizedMontgomeryProducer ≡ optionalAlternative
montgomeryProducerIsOptional = refl

v4SourceWrittenNotAgdaNative :
  v4h4Status verticalFourthNineR4ECompiler ≡ leanSourceWrittenDonor
v4SourceWrittenNotAgdaNative = refl

h4SourceWrittenNotAgdaNative :
  v4h4Status horizontalFiniteLocalCountBound ≡ leanSourceWrittenDonor
h4SourceWrittenNotAgdaNative = refl

finiteVerticalCarrierWeldStillOpen :
  v4h4Status finiteV4CarrierWeld ≡ openAssembly
finiteVerticalCarrierWeldStillOpen = refl

absorptionRemainsTheAnalyticCut :
  v4h4Status finalSignedAbsorption ≡ openAnalyticObstruction
absorptionRemainsTheAnalyticCut = refl
