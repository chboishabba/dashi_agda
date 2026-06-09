module DASHI.Physics.QFT.ExactSMMatchToken where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.DHRSectorDecomposition as DHR
import DASHI.Physics.SFGC.NonAbelian.DepthQuotientIsoSU3 as SU3

------------------------------------------------------------------------
-- Cycle-safe exact Standard Model match token.
--
-- This module packages the already-inhabited upstream witnesses that sit at
-- the Gate 1 / Gate 6 frontier: the concrete DHR sector decomposition and the
-- SU(3) route witness.  It does not introduce a new formalism or any extra
-- proof obligations beyond the canonical witness bundle already in the repo.

record ExactSMMatchReceipt : Setω where
  field
    dhrSectorDecomposition :
      DHR.DHRSectorDecomposition

    su3RouteWitness :
      SU3.DepthQuotientIsoSU3Witness

    exactMatchBoundary :
      List String

open ExactSMMatchReceipt public

canonicalExactSMMatchReceipt :
  ExactSMMatchReceipt
canonicalExactSMMatchReceipt =
  record
    { dhrSectorDecomposition =
        DHR.canonicalDHRSectorDecomposition
    ; su3RouteWitness =
        SU3.canonicalDepthQuotientIsoSU3Witness
    ; exactMatchBoundary =
        "The DHR sector decomposition already packages the canonical U(1), SU(2), and SU(3) witnesses"
        ∷ "The SU(3) route witness is consumed directly through the DepthQuotientIsoSU3 bridge"
        ∷ "No parallel hierarchy is introduced; this is a token surface only"
        ∷ []
    }

data ExactSMMatchBlocker : Set where
  blockedByNoGate1Gate6CarrierFunctorEquivalence :
    ExactSMMatchBlocker

  blockedByNoDHRCompactGroupToSMGaugeIsomorphism :
    ExactSMMatchBlocker

  blockedByNoLowEnergySU2RBreakingReceipt :
    ExactSMMatchBlocker

canonicalExactSMMatchBlockers :
  List ExactSMMatchBlocker
canonicalExactSMMatchBlockers =
  blockedByNoGate1Gate6CarrierFunctorEquivalence
  ∷ blockedByNoDHRCompactGroupToSMGaugeIsomorphism
  ∷ blockedByNoLowEnergySU2RBreakingReceipt
  ∷ []

record ExactSMMatchBlockerReceipt : Setω where
  field
    tokenReceipt :
      ExactSMMatchReceipt

    dhrSectorDecomposition :
      DHR.DHRSectorDecomposition

    dhrSectorDecompositionThreadedFromToken :
      Bool

    dhrSectorDecompositionThreadedFromTokenIsTrue :
      dhrSectorDecompositionThreadedFromToken ≡ true

    su3RouteWitness :
      SU3.DepthQuotientIsoSU3Witness

    su3RouteWitnessThreadedFromToken :
      Bool

    su3RouteWitnessThreadedFromTokenIsTrue :
      su3RouteWitnessThreadedFromToken ≡ true

    upstreamFiniteWitnessesPackaged :
      Bool

    upstreamFiniteWitnessesPackagedIsTrue :
      upstreamFiniteWitnessesPackaged ≡ true

    exactCarrierFunctorMatchConstructed :
      Bool

    exactCarrierFunctorMatchConstructedIsFalse :
      exactCarrierFunctorMatchConstructed ≡ false

    dhrCompactGroupSMGaugeIsomorphismConstructed :
      Bool

    dhrCompactGroupSMGaugeIsomorphismConstructedIsFalse :
      dhrCompactGroupSMGaugeIsomorphismConstructed ≡ false

    lowEnergySU2RBreakingReceiptSupplied :
      Bool

    lowEnergySU2RBreakingReceiptSuppliedIsFalse :
      lowEnergySU2RBreakingReceiptSupplied ≡ false

    firstBlocker :
      ExactSMMatchBlocker

    firstBlockerIsCarrierFunctorEquivalence :
      firstBlocker
      ≡
      blockedByNoGate1Gate6CarrierFunctorEquivalence

    blockers :
      List ExactSMMatchBlocker

    blockersAreCanonical :
      blockers ≡ canonicalExactSMMatchBlockers

    exactSMMatchPromoted :
      Bool

    exactSMMatchPromotedIsFalse :
      exactSMMatchPromoted ≡ false

    blockerBoundary :
      List String

open ExactSMMatchBlockerReceipt public

canonicalExactSMMatchBlockerReceipt :
  ExactSMMatchBlockerReceipt
canonicalExactSMMatchBlockerReceipt =
  record
    { tokenReceipt =
        canonicalExactSMMatchReceipt
    ; dhrSectorDecomposition =
        ExactSMMatchReceipt.dhrSectorDecomposition
          canonicalExactSMMatchReceipt
    ; dhrSectorDecompositionThreadedFromToken =
        true
    ; dhrSectorDecompositionThreadedFromTokenIsTrue =
        refl
    ; su3RouteWitness =
        ExactSMMatchReceipt.su3RouteWitness
          canonicalExactSMMatchReceipt
    ; su3RouteWitnessThreadedFromToken =
        true
    ; su3RouteWitnessThreadedFromTokenIsTrue =
        refl
    ; upstreamFiniteWitnessesPackaged =
        true
    ; upstreamFiniteWitnessesPackagedIsTrue =
        refl
    ; exactCarrierFunctorMatchConstructed =
        false
    ; exactCarrierFunctorMatchConstructedIsFalse =
        refl
    ; dhrCompactGroupSMGaugeIsomorphismConstructed =
        false
    ; dhrCompactGroupSMGaugeIsomorphismConstructedIsFalse =
        refl
    ; lowEnergySU2RBreakingReceiptSupplied =
        false
    ; lowEnergySU2RBreakingReceiptSuppliedIsFalse =
        refl
    ; firstBlocker =
        blockedByNoGate1Gate6CarrierFunctorEquivalence
    ; firstBlockerIsCarrierFunctorEquivalence =
        refl
    ; blockers =
        canonicalExactSMMatchBlockers
    ; blockersAreCanonical =
        refl
    ; exactSMMatchPromoted =
        false
    ; exactSMMatchPromotedIsFalse =
        refl
    ; blockerBoundary =
        "The exact SM token packages finite upstream U(1), SU(2), and SU(3) sector witnesses only"
        ∷ "It does not construct the Gate 1/Gate 6 carrier-functor equivalence"
        ∷ "It does not construct an isomorphism from the DHR compact group to SU3 x SU2 x U1"
        ∷ "It does not supply the low-energy SU2R breaking receipt required by the Pati-Salam-side path"
        ∷ "Exact Standard Model matching therefore remains fail-closed"
        ∷ []
    }

record Gate8Term1FiniteGaugeEvidenceBlockerReceipt : Setω where
  field
    finiteSectorDecomposition :
      DHR.DHRSectorDecomposition

    u1FiniteSector :
      DHR.U1SectorObject

    u1FiniteSectorMatchesDecomposition :
      u1FiniteSector
      ≡
      DHR.DHRSectorDecomposition.u1SectorObject
        finiteSectorDecomposition

    su2FiniteSector :
      DHR.SU2SectorObject

    su2FiniteSectorMatchesDecomposition :
      su2FiniteSector
      ≡
      DHR.DHRSectorDecomposition.su2SectorObject
        finiteSectorDecomposition

    su3FiniteFrontier :
      DHR.SU3FrontierObject

    su3FiniteFrontierThreadedFromDecomposition :
      Bool

    su3FiniteFrontierThreadedFromDecompositionIsTrue :
      su3FiniteFrontierThreadedFromDecomposition ≡ true

    exactSMBlockerReceipt :
      ExactSMMatchBlockerReceipt

    exactSMBlockers :
      List ExactSMMatchBlocker

    exactSMBlockersAreCanonical :
      exactSMBlockers ≡ canonicalExactSMMatchBlockers

    finiteEvidencePackaged :
      Bool

    finiteEvidencePackagedIsTrue :
      finiteEvidencePackaged ≡ true

    promotesGDHREqualsGSM :
      Bool

    promotesGDHREqualsGSMIsFalse :
      promotesGDHREqualsGSM ≡ false

    finiteEvidenceBoundary :
      List String

open Gate8Term1FiniteGaugeEvidenceBlockerReceipt public

canonicalGate8Term1FiniteGaugeEvidenceBlockerReceipt :
  Gate8Term1FiniteGaugeEvidenceBlockerReceipt
canonicalGate8Term1FiniteGaugeEvidenceBlockerReceipt =
  record
    { finiteSectorDecomposition =
        DHR.canonicalDHRSectorDecomposition
    ; u1FiniteSector =
        DHR.DHRSectorDecomposition.u1SectorObject
          DHR.canonicalDHRSectorDecomposition
    ; u1FiniteSectorMatchesDecomposition =
        refl
    ; su2FiniteSector =
        DHR.DHRSectorDecomposition.su2SectorObject
          DHR.canonicalDHRSectorDecomposition
    ; su2FiniteSectorMatchesDecomposition =
        refl
    ; su3FiniteFrontier =
        DHR.DHRSectorDecomposition.su3FrontierObject
          DHR.canonicalDHRSectorDecomposition
    ; su3FiniteFrontierThreadedFromDecomposition =
        true
    ; su3FiniteFrontierThreadedFromDecompositionIsTrue =
        refl
    ; exactSMBlockerReceipt =
        canonicalExactSMMatchBlockerReceipt
    ; exactSMBlockers =
        canonicalExactSMMatchBlockers
    ; exactSMBlockersAreCanonical =
        refl
    ; finiteEvidencePackaged =
        true
    ; finiteEvidencePackagedIsTrue =
        refl
    ; promotesGDHREqualsGSM =
        false
    ; promotesGDHREqualsGSMIsFalse =
        refl
    ; finiteEvidenceBoundary =
        "Gate8.term1 finite evidence packages the current U1, SU2, and SU3 sector objects from DHRSectorDecomposition"
        ∷ "The SU3 item is still a finite frontier witness, not an arbitrary-sector DHR reconstruction"
        ∷ "The exact blockers remain the canonical carrier-functor match, DHR compact-group to SM gauge isomorphism, and low-energy SU2R breaking blockers"
        ∷ "This receipt does not promote G_DHR ~= G_SM"
        ∷ []
    }
