module DASHI.Analysis.RiemannUniversalEvenConeLeanSourceCustodyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal

------------------------------------------------------------------------
-- RH UNIVERSAL-EVEN-CONE LEAN SOURCE CUSTODY
--
-- `RiemannAristotleUniversalEvenConeBidiExact` records two historical Lean
-- theorem names, `literalWeilSameOrdinateEvenCone` and
-- `primeEvenConeUnreachable`.  A fresh check of the connected
-- `chboishabba/dashi_lean4` main/code-search/PR/branch surfaces did not locate
-- those theorem names or a directly fetchable owner carrying them.
--
-- Therefore this file distinguishes:
--   * the Agda-side source claim/provenance record;
--   * actual Lean source custody;
--   * Lean kernel certification;
--   * Agda transport.
--
-- Search miss is not a nonexistence theorem.  If the historical owner remains
-- unavailable, the highest-alpha fallback is a MINIMAL Lean producer probe for
-- exactly the downstream-consumed properties, not a new full RH formalisation.
------------------------------------------------------------------------

universalReturn : Universal.UniversalEvenConeReturn
universalReturn = Universal.canonicalUniversalEvenConeReturn

record MinimalUniversalEvenConeProducerObligation : Set₁ where
  constructor minimal-universal-even-cone-producer-obligation
  field
    Taper Target Carrier : Set
    taperForTarget : Target -> Taper
    taperNonnegative : Set
    targetPoleClassKilledExactly : Set
    sameOrdinateEvenClusterPositive : Set
    exportIdentityToFinalPoleQuotientCarrier : Set
open MinimalUniversalEvenConeProducerObligation public

------------------------------------------------------------------------
-- WrongType / authority firewalls.
------------------------------------------------------------------------

data AgdaSourceClaimCreatesLeanCustody : Set where
data LeanSearchMissProvesTheoremAbsent : Set where
data LeanSourceCreatesAgdaTransport : Set where

dagdaClaimDoesNotCreateLeanCustody : AgdaSourceClaimCreatesLeanCustody -> ⊥
agdaClaimDoesNotCreateLeanCustody ()

searchMissDoesNotProveAbsence : LeanSearchMissProvesTheoremAbsent -> ⊥
searchMissDoesNotProveAbsence ()

leanSourceDoesNotCreateAgdaTransport : LeanSourceCreatesAgdaTransport -> ⊥
leanSourceDoesNotCreateAgdaTransport ()

record UniversalEvenConeLeanSourceCustodyBoundary : Set where
  constructor universal-even-cone-lean-source-custody-boundary
  field
    checkedLeanRepository : String
    checkedLeanMainToolchain : String
    citedHistoricalEvenConeTheorem : String
    citedHistoricalPrimeTheorem : String

    agdaSourceClaimRecorded : Bool
    checkedLeanOwnerLocated : Bool
    checkedLeanKernelReceiptObserved : Bool
    agdaTransportObserved : Bool

    searchMissProvesHistoricalTheoremAbsent : Bool
    sourceClaimCreatesTransportAuthority : Bool

    missingLeanOwnerMayBeReplacedByMinimalReproofProbe : Bool
    minimalProbeMustOwnNonnegativeTaper : Bool
    minimalProbeMustKillTargetPoleClass : Bool
    minimalProbeMustGiveSameOrdinatePositiveResponse : Bool
    minimalProbeMustExportSameObjectCarrierIdentity : Bool
    minimalProbeMaySkipFullRHAnalyticLane : Bool

    nextResidual : String
open UniversalEvenConeLeanSourceCustodyBoundary public

canonicalUniversalEvenConeLeanSourceCustodyBoundary :
  UniversalEvenConeLeanSourceCustodyBoundary
canonicalUniversalEvenConeLeanSourceCustodyBoundary =
  universal-even-cone-lean-source-custody-boundary
    "chboishabba/dashi_lean4"
    "leanprover/lean4:v4.28.0 / mathlib v4.28.0"
    "literalWeilSameOrdinateEvenCone"
    "primeEvenConeUnreachable"
    true
    false
    false
    false
    false
    false
    true
    true
    true
    true
    true
    true
    "either locate the historical Lean owner with a fetchable source and exact kernel receipt, or attempt a small current-Lean producer proving only nonnegativity, exact target-pole annihilation, positive same-ordinate response, and an export identity strong enough for the final pole-quotient transport gate. Abort the Lean route if that requires rebuilding the full RH analytic stack."
