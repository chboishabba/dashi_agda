module DASHI.Physics.Foundations.ScientistFrontierSiblingHandoffExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SCIENTIST-FRONTIER HANDOFF
--
-- The field/geometry/matter programme consumes acquisition results but does
-- not duplicate the missing/deceased-scientist evidence graph. PR #929 owns
-- the current twenty-scientist exact-key acquisition rounds and PR #915 owns
-- the object-first H0/H1/H2/H3 discriminator. Both remain separate from this
-- physics branch while open.
------------------------------------------------------------------------

record ScientistFrontierSiblingReceipt : Set where
  constructor scientist-frontier-sibling-receipt
  field
    acquisitionPR : Nat
    discriminatorPR : Nat
    retainedScientistCount : Nat
    acquisitionRound : Nat
    currentH2PromotionCount : Nat
    currentH3PromotionCount : Nat
    currentBestBroadModel : String
    directPhysicsTheoremImported : Bool
    historicalTargetingInferenceImported : Bool

open ScientistFrontierSiblingReceipt public

canonicalScientistFrontierSiblingReceipt : ScientistFrontierSiblingReceipt
canonicalScientistFrontierSiblingReceipt =
  scientist-frontier-sibling-receipt
    929 915 20 43 0 0
    "distributed high-value technical programmes with thematic/institutional/mission adjacency; exact same-object crossings remain acquisition-gated"
    false false

record ScientistFrontierHandoffBoundary : Set where
  constructor scientist-frontier-handoff-boundary
  field
    exactKeyAcquisitionHasDedicatedOwner : Bool
    causalPromotionHasDedicatedOwner : Bool
    currentH2ZeroPreserved : Bool
    currentH3ZeroPreserved : Bool
    physicsBranchMayConsumeFuturePaidTechnicalObjects : Bool
    technicalAdjacencyDoesNotEstablishTargeting : Bool
    missingRecordsDoNotEstablishConcealment : Bool
    openSiblingDoesNotTransferTheoremAuthority : Bool

open ScientistFrontierHandoffBoundary public

canonicalScientistFrontierHandoffBoundary : ScientistFrontierHandoffBoundary
canonicalScientistFrontierHandoffBoundary =
  scientist-frontier-handoff-boundary true true true true true true true true
