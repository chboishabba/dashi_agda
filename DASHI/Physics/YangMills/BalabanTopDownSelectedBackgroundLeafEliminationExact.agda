module DASHI.Physics.YangMills.BalabanTopDownSelectedBackgroundLeafEliminationExact where

------------------------------------------------------------------------
-- ROUND81: REMOVE SELECTED-BACKGROUND STABILITY AS A NEW CLAY LEAF
--
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- Together with:
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- SOURCE BOUNDARY
--
-- CMP122 Theorem 1 has the small-effective-coupling hypothesis and concludes
-- that the complete effective densities satisfy the full CMP119 Section-2 form
-- and bounds.  The selected-background/minimizer/propagator estimates are
-- internal ingredients of the published proof; they are not an additional
-- theorem hypothesis at this boundary.
--
-- ROUND76 SAME-OBJECT FACT
--
-- `BalabanSourceNativePublishedFlowEntryExact` already indexes the strong state
-- by the literal published flow and transports Section-2 membership/bounds to
-- that SAME density.  Therefore an independent proof of the rational selected
-- G2/background theorem is not required in the shortest compiler which accepts
-- the published CMP122 theorem at its stated boundary.
--
-- This does NOT make the finite selected-background work useless: it remains a
-- valuable independent reconstruction/audit of the source proof.  It simply
-- ceases to be a NEW analytic Clay leaf.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSourceNativePublishedFlowEntryExact as Entry
import DASHI.Physics.YangMills.Balaban1989Theorem1UVStabilityExact as Source

record SourceNativePublishedSection2Entry
    (published : Entry.SourceNativePublishedFlow)
    (scale : Nat) : Set₁ where
  field
    membership : Entry.PublishedSection2Membership published scale

open SourceNativePublishedSection2Entry public

selectedBackgroundFreeSection2Entry :
  (published : Entry.SourceNativePublishedFlow) →
  ∀ scale → SourceNativePublishedSection2Entry published scale
selectedBackgroundFreeSection2Entry published scale = record
  { membership = Entry.sourceNativeStateIsInPublishedSection2Class published scale }

-- The theorem above has no selector/G2/background-stability argument.  The
-- proof is literally projection of the source-native CMP122 membership already
-- established on the same density.
selectedBackgroundIndependentLeafRequiredForPublishedRoute : ProofLevel
selectedBackgroundIndependentLeafRequiredForPublishedRoute = machineChecked

cmp122BackgroundStabilitySourceOwnedLevel : ProofLevel
cmp122BackgroundStabilitySourceOwnedLevel = standardImported

-- The remaining source theorem hypothesis is the small effective coupling.
-- In the top-down frontier this is supplied by LiteralCompactSimplePositiveBeta,
-- not by a selected-background reproof.
smallEffectiveCouplingFromLiteralBetaStillRequiredLevel : ProofLevel
smallEffectiveCouplingFromLiteralBetaStillRequiredLevel = conditional
