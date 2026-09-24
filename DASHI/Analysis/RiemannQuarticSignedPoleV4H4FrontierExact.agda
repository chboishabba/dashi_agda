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
  explicitLeftEndpointAtom : V4H4Coordinate
  explicitV4H4AbsorbBudgetSurface : V4H4Coordinate
  fourthAngularToG3OrientationFirewall : V4H4Coordinate
  v4h4BudgetToLiteralG3Weld : V4H4Coordinate
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
v4h4Status finiteV4CarrierWeld = leanSourceWrittenDonor
v4h4Status explicitLeftEndpointAtom = leanSourceWrittenDonor
v4h4Status explicitV4H4AbsorbBudgetSurface = leanSourceWrittenDonor
v4h4Status fourthAngularToG3OrientationFirewall = leanSourceWrittenDonor
v4h4Status v4h4BudgetToLiteralG3Weld = leanSourceWrittenDonor
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
    finiteV4CarrierWeldSourceWritten : Bool
    explicitLeftEndpointAtomSourceWritten : Bool
    explicitV4H4AbsorbBudgetSurfaceSourceWritten : Bool
    fourthAngularToG3OrientationFirewallSourceWritten : Bool
    v4h4BudgetToLiteralG3WeldSourceWritten : Bool
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
    finiteV4CarrierWeldSourceWrittenIsTrue :
      finiteV4CarrierWeldSourceWritten ≡ true
    explicitLeftEndpointAtomSourceWrittenIsTrue :
      explicitLeftEndpointAtomSourceWritten ≡ true
    explicitV4H4AbsorbBudgetSurfaceSourceWrittenIsTrue :
      explicitV4H4AbsorbBudgetSurfaceSourceWritten ≡ true
    fourthAngularToG3OrientationFirewallSourceWrittenIsTrue :
      fourthAngularToG3OrientationFirewallSourceWritten ≡ true
    v4h4BudgetToLiteralG3WeldSourceWrittenIsTrue :
      v4h4BudgetToLiteralG3WeldSourceWritten ≡ true
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
    false
    true true true true
    true false true
    refl
    refl refl refl refl
    refl refl refl refl refl
    refl
    refl refl refl refl
    refl refl refl
    "The preferred Clay-facing local fourth-angular route is V4 plus H4, not a mandatory localized Montgomery theorem. V4 is an ordinary literal N-mu/RvM Abel specialization with a source-written 9*r^4*E compiler. H4 preserves sign: only 6*delta^2<a^2 can contribute positively, and that adverse cone is paid above by an a^4 envelope plus the existing fixed-window local zero-count theorem. Lean now also source-writes the exact finite carrier convention weld: the closed local vertical fourth carrier equals the literal half-open Zeta23 V4 carrier plus one explicit left-endpoint atom; SameOrd(t) contributes zero because the fourth weight vanishes there. The endpoint atom is bounded by the literal one-unit zero count rather than a generic-position choice. A new orientation firewall proves P_G3(rho)=m*S/(6*r^6)*(a^4-fourthAngular(rho)); therefore an upper bound on V4+H4 naturally gives a lower bound on the leading G3 quartic polynomial. Lean then pays the correct polarity instead: |V4| supplies a lower V4 bound, H4 has the unconditional lower envelope H4>=-(3/2)r^2 times local multiplicity, the local a^4 mass is at most 1/16 times that multiplicity, and the multiplicity is theorem-welded to the literal expanded Zeta23 count N(t-r-1,t+r]. This yields a source-written upper bound for literalOffOrdExactAt with the smooth mu fourth moment and FarExact still signed. The old marked 0/2/4 producer remains an optional alternative."
    "The orientation problem is now paid source-written by the lower-fourth-angular route. The remaining Clay-facing analytic task is the literal strict scalar absorption inequality for the corrected budget: targetStrength/(6*(t/16)^6) times [EV + (1/16 + (3/2)r^2)*N(t-r-1,t+r] - localMuFourth] plus local remainder debt plus signed FarExact must lie below compensationTargetThreshold by a positive margin. Inspect and sharpen the dominating paid term if this fails; do not introduce a new abstract hypothesis or absolute-value FarExact."
    "V4, H4, the endpoint carrier weld, the orientation firewall, and the corrected budget-to-literal-G3 upper weld are Lean source-written donors only. The strict scalar absorption inequality remains unpaid. This owner is an Agda programme/status theorem and does not claim independent Agda-kernel replay or an exact-head Lean kernel receipt for those source tranches."

montgomeryProducerIsOptional :
  v4h4Status localizedMontgomeryProducer ≡ optionalAlternative
montgomeryProducerIsOptional = refl

v4SourceWrittenNotAgdaNative :
  v4h4Status verticalFourthNineR4ECompiler ≡ leanSourceWrittenDonor
v4SourceWrittenNotAgdaNative = refl

h4SourceWrittenNotAgdaNative :
  v4h4Status horizontalFiniteLocalCountBound ≡ leanSourceWrittenDonor
h4SourceWrittenNotAgdaNative = refl

finiteVerticalCarrierWeldIsSourceWritten :
  v4h4Status finiteV4CarrierWeld ≡ leanSourceWrittenDonor
finiteVerticalCarrierWeldIsSourceWritten = refl

leftEndpointAtomIsExplicit :
  v4h4Status explicitLeftEndpointAtom ≡ leanSourceWrittenDonor
leftEndpointAtomIsExplicit = refl

fourthAngularOrientationFirewallIsSourceWritten :
  v4h4Status fourthAngularToG3OrientationFirewall ≡ leanSourceWrittenDonor
fourthAngularOrientationFirewallIsSourceWritten = refl

budgetToLiteralG3WeldIsSourceWritten :
  v4h4Status v4h4BudgetToLiteralG3Weld ≡ leanSourceWrittenDonor
budgetToLiteralG3WeldIsSourceWritten = refl

absorptionRemainsTheAnalyticCut :
  v4h4Status finalSignedAbsorption ≡ openAnalyticObstruction
absorptionRemainsTheAnalyticCut = refl
