module DASHI.Physics.Closure.W2W3W4W5ExternalAuthorityPacketSurface where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.W2W3ExternalAuthorityFormalClosureRequest as W2W3
import DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptRequestPack as W3Pack
import DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptRequestPack as W4Pack
import DASHI.Physics.Closure.W4W5PhiStarToMassAcceptanceBridgeRequest as W4W5Bridge
import DASHI.Physics.Closure.W5CT18ExternalIntakeReceipt as W5Intake

------------------------------------------------------------------------
-- Concise external-authority packet surface for W2/W3/W4/W5.
--
-- This module only aggregates existing provider-facing request surfaces:
-- W2/W3 Option B, W3 accepted-authority intake, W4 physical-calibration
-- external receipt intake, W4/W5 phi-star-to-mass bridge request, and W5
-- PDF/luminosity intake.  It does not add constructors, synthesize tokens,
-- accept a candidate packet, or claim W4/W5 closure.

data ExternalGate : Set where
  W2Gate :
    ExternalGate
  W3Gate :
    ExternalGate
  W4Gate :
    ExternalGate
  W5Gate :
    ExternalGate

data ExternalPacketStatus : Set where
  awaitingExternalAuthorityPacket :
    ExternalPacketStatus

data InternalConstructionAuthorization : Set where
  noInternalConstructionAuthorized :
    InternalConstructionAuthorization

record W2W3W4W5ExternalAuthorityPacketSurface : Setω where
  field
    status :
      ExternalPacketStatus

    gatesCovered :
      List ExternalGate

    w2w3OptionBRequest :
      W2W3.W2W3ExternalAuthorityFormalClosureRequest

    w3AcceptedAuthorityProviderRequest :
      W3Pack.W3AcceptedAuthorityProviderPayloadRequest

    w4PhysicalCalibrationProviderRequest :
      W4Pack.W4PhysicalCalibrationProviderPayloadRequest

    w4w5PhiStarToMassBridgeRequest :
      W4W5Bridge.PhiStarToMassAcceptanceBridgeRequest

    w5ExternalPDFIntakeReceipt :
      W5Intake.W5CT18ExternalIntakeReceipt

    internalConstructionAuthorization :
      InternalConstructionAuthorization

    internalConstructionAuthorized :
      Bool

    internalConstructionAuthorizedIsFalse :
      internalConstructionAuthorized ≡ false

    w2PromotedHere :
      Bool

    w2PromotedHereIsFalse :
      w2PromotedHere ≡ false

    w3PromotedHere :
      Bool

    w3PromotedHereIsFalse :
      w3PromotedHere ≡ false

    w4PromotedHere :
      Bool

    w4PromotedHereIsFalse :
      w4PromotedHere ≡ false

    w5PromotedHere :
      Bool

    w5PromotedHereIsFalse :
      w5PromotedHere ≡ false

    exactExternalLinksAndFieldsNeeded :
      List String

    exactExternalReceiptTypesNeeded :
      List String

    noInternalConstructionBoundary :
      List String

    noW4W5ClosureBoundary :
      List String

    noW2TokenConstructed :
      ⊤

    noW3TokenConstructed :
      ⊤

    noW4TokenConstructed :
      ⊤

    noW5ClosureConstructed :
      ⊤

canonicalW2W3W4W5ExternalAuthorityPacketSurface :
  W2W3W4W5ExternalAuthorityPacketSurface
canonicalW2W3W4W5ExternalAuthorityPacketSurface =
  record
    { status =
        awaitingExternalAuthorityPacket
    ; gatesCovered =
        W2Gate
        ∷ W3Gate
        ∷ W4Gate
        ∷ W5Gate
        ∷ []
    ; w2w3OptionBRequest =
        W2W3.canonicalW2W3ExternalAuthorityFormalClosureRequest
    ; w3AcceptedAuthorityProviderRequest =
        W3Pack.canonicalW3AcceptedAuthorityProviderPayloadRequest
    ; w4PhysicalCalibrationProviderRequest =
        W4Pack.canonicalW4PhysicalCalibrationProviderPayloadRequest
    ; w4w5PhiStarToMassBridgeRequest =
        W4W5Bridge.canonicalW4W5PhiStarToMassAcceptanceBridgeRequest
    ; w5ExternalPDFIntakeReceipt =
        W5Intake.canonicalW5CT18ExternalIntakeReceipt
    ; internalConstructionAuthorization =
        noInternalConstructionAuthorized
    ; internalConstructionAuthorized =
        false
    ; internalConstructionAuthorizedIsFalse =
        refl
    ; w2PromotedHere =
        false
    ; w2PromotedHereIsFalse =
        refl
    ; w3PromotedHere =
        false
    ; w3PromotedHereIsFalse =
        refl
    ; w4PromotedHere =
        false
    ; w4PromotedHereIsFalse =
        refl
    ; w5PromotedHere =
        false
    ; w5PromotedHereIsFalse =
        refl
    ; exactExternalLinksAndFieldsNeeded =
        "W2: external authority value or accepted receipt for DASHI.Physics.Closure.NaturalP2ConvergencePromotionObligation.NaturalP2ConvergencePromotionAuthorityToken"
        ∷ "W2: certified evidence payload binding normalizeAdd sum/p-adic invariance, natural p2 bridge-or-obstruction packaging, carrier transport, and carrier-general convergence"
        ∷ "W3: external DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate.W3AcceptedEvidenceAuthorityToken"
        ∷ "W3: W3AcceptedAuthorityExternalReceipt fields authorityToken, evidenceBackedEmpiricalTarget, evidence-target equality, B4 empirical promotion, origin receipt promotion, bridge obligations, and bridge-target equality"
        ∷ "W4: AcceptedDYLuminosityConventionAuthority, then W4ZAdequacy, then Candidate256PhysicalCalibrationExternalReceipt"
        ∷ "W4: Candidate256 physical unit carrier, Nat-to-unit calibration map, quotient scale map, factorization law, dimensional-preservation law and witness, citation/checksum/validation payload"
        ∷ "W4/W5 bridge link: https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/"
        ∷ "W4/W5 bridge link: https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/SMP-20-003_hepdata/submission.yaml"
        ∷ "W4/W5 bridge link: https://www.hepdata.net/record/ins2079374?format=json"
        ∷ "W4/W5 bridge field: central-value acceptance/efficiency surface A(M, phi*) or accepted observable-conversion law from DSIG/DPHISTAR ratio-table integrals to mass-integrated cross-section/PDF correction ratios"
        ∷ "W5: accepted PDF/luminosity packet carrying PDF set/version, LHAPDF id or equivalent table, grid checksums, factorization scale, rapidity window, mass-bin integration, flavour weights, t45 correction targeting 0.8804486068, tolerance, DOI, provenance, and authority receipt"
        ∷ []
    ; exactExternalReceiptTypesNeeded =
        W3Pack.W3AcceptedAuthorityProviderPayloadRequest.exactExternalReceiptName
          W3Pack.canonicalW3AcceptedAuthorityProviderPayloadRequest
        ∷ W3Pack.W3AcceptedAuthorityProviderPayloadRequest.exactAuthorityTokenName
          W3Pack.canonicalW3AcceptedAuthorityProviderPayloadRequest
        ∷ W4Pack.W4PhysicalCalibrationProviderPayloadRequest.exactReceiptName
          W4Pack.canonicalW4PhysicalCalibrationProviderPayloadRequest
        ∷ W4Pack.W4PhysicalCalibrationProviderPayloadRequest.exactAuthorityTokenName
          W4Pack.canonicalW4PhysicalCalibrationProviderPayloadRequest
        ∷ W4W5Bridge.PhiStarToMassAcceptanceBridgeRequest.neededExternalArtifactName
          W4W5Bridge.canonicalW4W5PhiStarToMassAcceptanceBridgeRequest
        ∷ "DASHI.Physics.Closure.W5CT18ExternalIntakeReceipt.W5CT18ExternalIntakeReceipt accepted external PDF/luminosity authority packet"
        ∷ []
    ; noInternalConstructionBoundary =
        "No NaturalP2ConvergencePromotionAuthorityToken is constructed"
        ∷ "No W3AcceptedEvidenceAuthorityToken is constructed"
        ∷ "No W3AcceptedAuthorityExternalReceipt is constructed"
        ∷ "No Candidate256PhysicalCalibrationAuthorityToken is constructed"
        ∷ "No Candidate256PhysicalCalibrationExternalReceipt is constructed"
        ∷ "No PDF carrier, parton-luminosity authority, phi-star acceptance surface, or t45 promotion is fabricated"
        ∷ "This packet surface is a provider-facing request index only"
        ∷ []
    ; noW4W5ClosureBoundary =
        "W4 remains blocked pending accepted DY authority, W4ZAdequacy, and Candidate256 physical calibration receipt"
        ∷ "W5 remains blocked pending accepted PDF/luminosity convention and authority/provenance packet"
        ∷ "The public CMS-SMP-20-003 phi-star tables do not by themselves supply A(M, phi*) or a mass/PDF correction law"
        ∷ "This module does not claim W4 closure, W5 closure, or W4/W5 shared closure"
        ∷ []
    ; noW2TokenConstructed =
        tt
    ; noW3TokenConstructed =
        tt
    ; noW4TokenConstructed =
        tt
    ; noW5ClosureConstructed =
        tt
    }

canonicalExternalPacketNoInternalConstruction :
  W2W3W4W5ExternalAuthorityPacketSurface.internalConstructionAuthorized
    canonicalW2W3W4W5ExternalAuthorityPacketSurface
  ≡
  false
canonicalExternalPacketNoInternalConstruction =
  refl

canonicalExternalPacketW4NotPromoted :
  W2W3W4W5ExternalAuthorityPacketSurface.w4PromotedHere
    canonicalW2W3W4W5ExternalAuthorityPacketSurface
  ≡
  false
canonicalExternalPacketW4NotPromoted =
  refl

canonicalExternalPacketW5NotPromoted :
  W2W3W4W5ExternalAuthorityPacketSurface.w5PromotedHere
    canonicalW2W3W4W5ExternalAuthorityPacketSurface
  ≡
  false
canonicalExternalPacketW5NotPromoted =
  refl
