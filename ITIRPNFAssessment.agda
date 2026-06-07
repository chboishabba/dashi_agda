module ITIRPNFAssessment where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Agda.Primitive using (Setω)

import Ontology.Hecke.PNFResidualBridge as Hecke
import DASHI.Interop.SenateFormalizationPNFAdapter as Senate

------------------------------------------------------------------------
-- Typed ITIR/PNF assessment surface used by the journey loom.
--
-- This module does not construct runtime parser evidence.
-- It packages current status and a boundary-only promotion posture.

data ITIRPNFAssessmentLane : Set where
  runtimeLane : ITIRPNFAssessmentLane
  heckeBridgeLane : ITIRPNFAssessmentLane
  senateFormalizationLane : ITIRPNFAssessmentLane
  residualLane : ITIRPNFAssessmentLane
  boundaryLane : ITIRPNFAssessmentLane

data ITIRPNFAssessmentPromotion : Set where
  pnfPromotionBlocked : ITIRPNFAssessmentPromotion
  pnfEvidencePending : ITIRPNFAssessmentPromotion

record ITIRPNFAssessment : Setω where
  field
    canonicalThreadLabel :
      String

    lanes :
      List ITIRPNFAssessmentLane

    lanesAreCanonical :
      lanes
      ≡
      runtimeLane
      ∷ heckeBridgeLane
      ∷ senateFormalizationLane
      ∷ residualLane
      ∷ boundaryLane
      ∷ []

    missingReceiptDiagnosticSummary :
      String

    sourceReceiptDiagnosticSummary :
      String

    bridgeSurface :
      Hecke.HeckePNFResidualBridgeSurface

    bridgeSurfaceIsCanonical :
      bridgeSurface ≡ Hecke.heckePNFResidualBridgeSurface

    senateFormalizationSurface :
      Senate.SenateFormalizationPNFAdapterSurface

    senateFormalizationSurfaceIsCanonical :
      senateFormalizationSurface
      ≡
      Senate.canonicalSenateFormalizationPNFAdapterSurface

    senateFormalizationPromotion :
      Bool

    senateFormalizationPromotionIsFalse :
      senateFormalizationPromotion ≡ false

    itirPromotion :
      Bool

    itirPromotionIsFalse :
      itirPromotion ≡ false

    noYangBaxterPromotion :
      Bool

    noYangBaxterPromotionIsTrue :
      noYangBaxterPromotion ≡ true

    noNSYMPromotion :
      Bool

    noNSYMPromotionIsTrue :
      noNSYMPromotion ≡ true

    boundaryStatements :
      List String

open ITIRPNFAssessment public

canonicalITIRPNFAssessment : ITIRPNFAssessment
canonicalITIRPNFAssessment =
  record
    { canonicalThreadLabel =
        "DASHI dialectical-loom canonical Sweetgrass thread"
    ; lanes =
        runtimeLane
        ∷ heckeBridgeLane
        ∷ senateFormalizationLane
        ∷ residualLane
        ∷ boundaryLane
        ∷ []
    ; lanesAreCanonical =
        refl
    ; missingReceiptDiagnosticSummary =
        "ITIR/PNF missing-receipt diagnostics remain boundary conditions"
    ; sourceReceiptDiagnosticSummary =
        "ITIR/PNF source diagnostics remain runtime-required and non-promoted"
    ; bridgeSurface =
        Hecke.heckePNFResidualBridgeSurface
    ; bridgeSurfaceIsCanonical =
        refl
    ; senateFormalizationSurface =
        Senate.canonicalSenateFormalizationPNFAdapterSurface
    ; senateFormalizationSurfaceIsCanonical =
        refl
    ; senateFormalizationPromotion =
        false
    ; senateFormalizationPromotionIsFalse =
        refl
    ; itirPromotion =
        false
    ; itirPromotionIsFalse =
        refl
    ; noYangBaxterPromotion =
        true
    ; noYangBaxterPromotionIsTrue =
        refl
    ; noNSYMPromotion =
        true
    ; noNSYMPromotionIsTrue =
        refl
    ; boundaryStatements =
        "Runtime parser output is required for full PNF emissions and residual residue fields"
        ∷ "Hecke quotient projection equality is a candidate-fibre notion, not final proof authority"
        ∷ "Senate Lean declarations enter as source-side PredicatePNF review evidence, not legal authority"
        ∷ "ITIR/PNF path does not license any Navier-Stokes or Yang-Baxter theorem promotion claim"
        ∷ []
    }
