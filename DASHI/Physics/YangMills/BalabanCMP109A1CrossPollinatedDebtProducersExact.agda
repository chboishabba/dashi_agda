module DASHI.Physics.YangMills.BalabanCMP109A1CrossPollinatedDebtProducersExact where

------------------------------------------------------------------------
-- ROW A1 CROSS-POLLINATION: REUSE EXISTING PHYSICAL DEBT PRODUCERS
--
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Field Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- CROSS-POLLINATION RESULT
--
-- The newest Row-A1 Lean lane introduced generic source numbers (A,K,rho,D).
-- Existing DASHI Yang--Mills owners already provide a strictly sharper route for
-- two of those debts once their literal physical inputs are instantiated:
--
--   1. the five determinant / interaction / chart / gauge / localization
--      channels cancel through cubic order and the existing finite compiler
--      gives
--
--          betaInt >= - C_beta g^4,
--
--      where C_beta is definitionally the finite sum of literal cell/channel
--      fourth-order quotient majorants;
--
--   2. the localized irrelevant-memory owner gives
--
--          memory(count) <= C_H gamma / 2
--
--      uniformly in the number of previous RG steps.  This bound applies only
--      to localized/irrelevant memory at fixed declared marginal data; CMP109
--      explicitly warns that the marginal running coupling itself depends on all
--      preceding couplings and must not be assigned artificial forgetting.
--
-- Therefore the shortest cross-pollinated A1 budget is
--
--      betaZ floor - C_beta gamma^4 - C_H gamma/2,
--
-- not the more generic
--
--      betaZ floor - (A/(1-K gamma)) gamma^rho - D B.
--
-- This does NOT close Row A1.  The literal five-channel Taylor/quotient data,
-- the literal localized-memory influence majorant, and the literal Gaussian
-- background-variation datum remain physical source instantiations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; -_; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaLowerRemainderExact as Beta
import DASHI.Physics.YangMills.BalabanYM4FiveChannelQuarticBetaAdapterExact as Five
import DASHI.Physics.YangMills.BalabanYM4FiveChannelTaylorCancellationToFourthOrderExact as Taylor
import DASHI.Physics.YangMills.BalabanBetaHistoryLocalizedInfluenceExact as History
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanCMP109ReducedMarginSourceCutsetExact as Reduced

------------------------------------------------------------------------
-- Current-step nonlinear debt: existing five-channel quartic compiler
------------------------------------------------------------------------

record A1FiveChannelQuarticProducer (Cell : Set) : Set₁ where
  field
    dataSet : Five.FiveChannelQuarticBetaData Cell
    gamma : ℚ

    couplingNonnegative : 0ℚ ≤ Five.coupling dataSet
    gammaNonnegative : 0ℚ ≤ gamma
    couplingBelowGamma : Five.coupling dataSet ≤ gamma

open A1FiveChannelQuarticProducer public

fiveChannelInteractionCoefficient :
  ∀ {Cell} → A1FiveChannelQuarticProducer Cell → ℚ
fiveChannelInteractionCoefficient producer =
  Five.coefficientTotal (dataSet producer)

fiveChannelInteractionDebtAtGamma :
  ∀ {Cell} → A1FiveChannelQuarticProducer Cell → ℚ
fiveChannelInteractionDebtAtGamma producer =
  fiveChannelInteractionCoefficient producer * Beta.power4 (gamma producer)

fiveChannelInteractionUniformLower :
  ∀ {Cell} (producer : A1FiveChannelQuarticProducer Cell) →
  - fiveChannelInteractionDebtAtGamma producer
  ≤ Five.betaInt (dataSet producer)
fiveChannelInteractionUniformLower producer =
  Beta.quarticUniformInteractionLower
    (Five.asFiniteInteractionAtomEnclosure (dataSet producer))
    (gamma producer)
    (couplingNonnegative producer)
    (gammaNonnegative producer)
    (couplingBelowGamma producer)
    (Five.coefficientTotalNN (dataSet producer))

------------------------------------------------------------------------
-- Irrelevant-memory debt: existing scale-local localization compiler
------------------------------------------------------------------------

irrelevantMemoryDebt : History.LocalizedBetaHistoryInfluence → ℚ
irrelevantMemoryDebt history =
  (History.coefficient history * History.gamma history) * Geo.half

irrelevantMemoryUniform :
  (history : History.LocalizedBetaHistoryInfluence) → ∀ count →
  History.historyDifference history 0 count ≤ irrelevantMemoryDebt history
irrelevantMemoryUniform history count =
  History.historyDifferenceFromPresentScale history count

------------------------------------------------------------------------
-- Same-object physical package for the shortest A1 debt route
------------------------------------------------------------------------

record CMP109CrossPollinatedA1DebtPackage (Cell : Set) : Set₁ where
  field
    -- Gaussian source datum stays the current corner-background target.
    corner : Reduced.CMP109LiteralCornerBubbleScalar Nat ℚ

    -- Current-step nonlinear remainder is the existing five-channel object.
    interaction : A1FiveChannelQuarticProducer Cell

    -- Historical debt is only the source-local irrelevant/polymer memory.
    memory : History.LocalizedBetaHistoryInfluence

    -- Same-trajectory coherence.  The two debt producers must use the same
    -- admissible coupling ceiling rather than unrelated gamma parameters.
    sameGamma : History.gamma memory ≡ gamma interaction

    -- The full physical beta coefficient must be identified with the SAME
    -- CMP109 coefficient whose Gaussian/current-step/memory pieces appear here.
    sameLiteralCMP109BetaDecomposition : Set

    -- Current shortest margin:
    --   v^2/32 - C_beta gamma^4 - C_H gamma/2 > 0.
    crossPollinatedMarginPositive : Set

open CMP109CrossPollinatedA1DebtPackage public

------------------------------------------------------------------------
-- Authority / frontier
------------------------------------------------------------------------

-- The two debt inequalities above are direct reuse of existing Agda theorems.
cmp109FiveChannelQuarticDebtReuseLevel : ProofLevel
cmp109FiveChannelQuarticDebtReuseLevel = machineChecked

cmp109LocalizedIrrelevantMemoryDebtReuseLevel : ProofLevel
cmp109LocalizedIrrelevantMemoryDebtReuseLevel = machineChecked

-- Physical instantiations remain open.
cmp109LiteralFiveChannelTaylorInstantiationLevel : ProofLevel
cmp109LiteralFiveChannelTaylorInstantiationLevel =
  Taylor.physicalFiveChannelTaylorExpansionLevel

cmp109LiteralFiveChannelQuotientMajorantLevel : ProofLevel
cmp109LiteralFiveChannelQuotientMajorantLevel =
  Taylor.physicalFiveChannelFourthOrderQuotientMajorantLevel

cmp109LiteralIrrelevantMemoryInfluenceLevel : ProofLevel
cmp109LiteralIrrelevantMemoryInfluenceLevel =
  History.literalBetaIrrelevantMemoryInfluenceLevel

cmp109CrossPollinatedA1DebtPackageLevel : ProofLevel
cmp109CrossPollinatedA1DebtPackageLevel = conditional

-- The universal 11/12 normalization lane is intentionally NOT consumed here:
-- its `LiteralScalarIntegrandExpression` requires an `infraredCoefficientExact`
-- field equating the supplied scalar coefficient to the convention value.  It is
-- valid downstream plumbing after literal scalar construction, not an
-- independent source derivation of the missing Gaussian coefficient.
