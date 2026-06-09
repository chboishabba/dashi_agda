module ITIRPNFAssessment where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Agda.Primitive using (Setω)

import Ontology.Hecke.PNFResidualBridge as Hecke
import DASHI.Interop.SenateFormalizationPNFAdapter as Senate
import DASHI.Interop.SweetgrassCarrierSpine as Sweetgrass
import DASHI.Interop.UnifiedMathLanguageSpine as Unified
import DASHI.Interop.UnifiedMathLanguageAssertedProofs as Asserted

------------------------------------------------------------------------
-- Typed ITIR/PNF assessment surface used by the journey loom.
--
-- This module does not construct runtime parser evidence.
-- It packages current status and a boundary-only promotion posture.

data ITIRPNFAssessmentLane : Set where
  runtimeLane : ITIRPNFAssessmentLane
  heckeBridgeLane : ITIRPNFAssessmentLane
  senateFormalizationLane : ITIRPNFAssessmentLane
  sweetgrassCarrierSpineLane : ITIRPNFAssessmentLane
  unifiedMathLanguageLane : ITIRPNFAssessmentLane
  assertedProofLane : ITIRPNFAssessmentLane
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
      ∷ sweetgrassCarrierSpineLane
      ∷ unifiedMathLanguageLane
      ∷ assertedProofLane
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

    sweetgrassCarrierSpine :
      Sweetgrass.SweetgrassCarrierSpineSurface

    sweetgrassCarrierSpineIsCanonical :
      sweetgrassCarrierSpine
      ≡
      Sweetgrass.canonicalSweetgrassCarrierSpineSurface

    sweetgrassCarrierSpinePromotion :
      Bool

    sweetgrassCarrierSpinePromotionIsFalse :
      sweetgrassCarrierSpinePromotion ≡ false

    unifiedMathLanguageSurface :
      Unified.UnifiedMathLanguageSurface

    unifiedMathLanguageSurfaceIsCanonical :
      unifiedMathLanguageSurface
      ≡
      Unified.canonicalUnifiedMathLanguageSurface

    unifiedMathLanguagePromotion :
      Bool

    unifiedMathLanguagePromotionIsFalse :
      unifiedMathLanguagePromotion ≡ false

    assertedProofSurface :
      Asserted.UnifiedMathLanguageAssertedProofSurface

    assertedProofSurfaceIsCanonical :
      assertedProofSurface
      ≡
      Asserted.canonicalUnifiedMathLanguageAssertedProofSurface

    chemistryInternalProofPromoted :
      Bool

    chemistryInternalProofPromotedIsTrue :
      chemistryInternalProofPromoted ≡ true

    pnfHyperfabric369InternalProofPromoted :
      Bool

    pnfHyperfabric369InternalProofPromotedIsTrue :
      pnfHyperfabric369InternalProofPromoted ≡ true

    assertedExternalPromotion :
      Bool

    assertedExternalPromotionIsFalse :
      assertedExternalPromotion ≡ false

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
        ∷ sweetgrassCarrierSpineLane
        ∷ unifiedMathLanguageLane
        ∷ assertedProofLane
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
    ; sweetgrassCarrierSpine =
        Sweetgrass.canonicalSweetgrassCarrierSpineSurface
    ; sweetgrassCarrierSpineIsCanonical =
        refl
    ; sweetgrassCarrierSpinePromotion =
        false
    ; sweetgrassCarrierSpinePromotionIsFalse =
        refl
    ; unifiedMathLanguageSurface =
        Unified.canonicalUnifiedMathLanguageSurface
    ; unifiedMathLanguageSurfaceIsCanonical =
        refl
    ; unifiedMathLanguagePromotion =
        false
    ; unifiedMathLanguagePromotionIsFalse =
        refl
    ; assertedProofSurface =
        Asserted.canonicalUnifiedMathLanguageAssertedProofSurface
    ; assertedProofSurfaceIsCanonical =
        refl
    ; chemistryInternalProofPromoted =
        true
    ; chemistryInternalProofPromotedIsTrue =
        refl
    ; pnfHyperfabric369InternalProofPromoted =
        true
    ; pnfHyperfabric369InternalProofPromotedIsTrue =
        refl
    ; assertedExternalPromotion =
        false
    ; assertedExternalPromotionIsFalse =
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
        ∷ "Sweetgrass is Kimmerer-attributed braid/fabric vocabulary for bounded carrier projection, not authority promotion"
        ∷ "Eigen, Hecke, j-invariant, moonshine, BT-braid, hyperfabric, regular-fabric, Clifford/Bott/spinor, gauge, category/functor/operator/lattice, and high-n prime-carrier motifs enter only as bounded carrier vocabulary"
        ∷ "The unified math language spine inhabits a repo-internal carrier grammar across DNA/genome/chemistry, brain/connectome/semantic transport, biology/sensorimotor, physics/QFT/PDE, language/NLP, PNF/ITIR, claim/Wikidata review, braid/fabric, Sweetgrass, dialectic/Tlurey/triadic/nonary, Hecke/eigen/j-invariant, BT-tree, BT-braid, p-adic/decimal, ultrametric/adelic, wave, and supervoxel lanes"
        ∷ "Chemistry and supervoxel-chemistry are now internally asserted as definitional checked proof surfaces; NS and YM are recorded as approaching closed proof lanes with external theorem promotion still blocked"
        ∷ "The 369 PNF hyperfabric is internally asserted as checked algebra: 3*3=9, 9^2=81 for two woven dialectic interactions, 3*3*3=27 for the discussion atom, and document-time gives the fourth hypervoxel axis with p-adic/decimal valuation and SSP/Monster prime-carrier labels"
        ∷ "ITIR/PNF path does not license any Navier-Stokes or Yang-Baxter theorem promotion claim"
        ∷ []
    }
