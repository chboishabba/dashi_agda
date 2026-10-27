{-# OPTIONS --safe #-}
module DASHI.Physics.CanonicalClayFrontierExact where

------------------------------------------------------------------------
-- UNIFIED CANONICAL CLAY FRONTIER
--
-- DASHI extension.  This module is an authority/obligation ledger over the
-- already-canonical Yang--Mills and Navier--Stokes residual schedulers.  It
-- deliberately does not duplicate their theorem telescopes and carries no
-- field that can manufacture evidence for a live obligation.
--
-- The constructors below identify the exact canonical residual leaves to be
-- scheduled by research tooling.  Mathematical ownership remains in the
-- qualified scheduler modules imported below.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.YangMillsCanonicalClayResidualExact as YM using ()
open import DASHI.Physics.Closure.NSCanonicalClayResidualExact as NS using ()

data ClayDomain : Set where
  yangMills navierStokes : ClayDomain

-- Exact live canonical residual leaves.  These are obligation identifiers,
-- not proofs and not source-authority promotions.
data CanonicalClayLiveObligation : Set where
  cmp109SourceSemantics : CanonicalClayLiveObligation
  physicalTransferGap : CanonicalClayLiveObligation
  cmp116SelectedTermReplay : CanonicalClayLiveObligation
  cmp116TraceEntropyBudget : CanonicalClayLiveObligation

  a1PhysicalPopulation : CanonicalClayLiveObligation
  a2MajorantDomination : CanonicalClayLiveObligation
  a3Continuation : CanonicalClayLiveObligation
  b4PhysicalR440Payment : CanonicalClayLiveObligation
  b123PhysicalProducers : CanonicalClayLiveObligation
  b7IntegratedControl : CanonicalClayLiveObligation
  bContinuationInputs : CanonicalClayLiveObligation
  cdReleasedReconstruction : CanonicalClayLiveObligation

obligationDomain : CanonicalClayLiveObligation → ClayDomain
obligationDomain cmp109SourceSemantics = yangMills
obligationDomain physicalTransferGap = yangMills
obligationDomain cmp116SelectedTermReplay = yangMills
obligationDomain cmp116TraceEntropyBudget = yangMills
obligationDomain a1PhysicalPopulation = navierStokes
obligationDomain a2MajorantDomination = navierStokes
obligationDomain a3Continuation = navierStokes
obligationDomain b4PhysicalR440Payment = navierStokes
obligationDomain b123PhysicalProducers = navierStokes
obligationDomain b7IntegratedControl = navierStokes
obligationDomain bContinuationInputs = navierStokes
obligationDomain cdReleasedReconstruction = navierStokes

------------------------------------------------------------------------
-- Machine-readable accounting coordinates.
------------------------------------------------------------------------

-- Regenerated full-index NS extraction receipt on master a70aae6eb5de... .
-- Historical unresolved packages remain evidence/review work, not discharged
-- canonical proof obligations.
nsUnresolvedPackages : Nat
nsUnresolvedPackages = 13716

unresolvedPackagesDischarged : Bool
unresolvedPackagesDischarged = false

------------------------------------------------------------------------
-- Global fail-closed Clay authority gates.
------------------------------------------------------------------------

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

clayPromotion : Bool
clayPromotion = false

-- The unified ledger is definitionally aligned with the existing canonical
-- schedulers rather than introducing an independent promotion state.
yangMillsSchedulerPromotionAgrees :
  YM.clayYangMillsPromoted ≡ clayYangMillsPromoted
yangMillsSchedulerPromotionAgrees = refl

navierStokesSchedulerPromotionAgrees :
  NS.clayNavierStokesPromoted ≡ clayNavierStokesPromoted
navierStokesSchedulerPromotionAgrees = refl

navierStokesUnresolvedGateAgrees :
  NS.unresolvedPackagesDischarged ≡ unresolvedPackagesDischarged
navierStokesUnresolvedGateAgrees = refl

clayYangMillsPromotedIsFalse : clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse = refl

clayNavierStokesPromotedIsFalse : clayNavierStokesPromoted ≡ false
clayNavierStokesPromotedIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl

unresolvedPackagesDischargedIsFalse : unresolvedPackagesDischarged ≡ false
unresolvedPackagesDischargedIsFalse = refl
