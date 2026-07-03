module DASHI.Physics.Closure.NSTriadKNGate2AEP1ExtremizerClassification where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

----------------------------------------------------------------------
-- EP1: Extremizer classification.
--
-- Claim:
--   Gate 1 near-extremizers belong to a controlled anisotropic seam
--   family.  The extremizer direction is determined by the O(4)
--   anisotropic subspace structure of the W₄-scalar lattice (1-dim,
--   spanned by I₁ − (1/4)I₂, per 2602.0087 Thm 3.6).
--
-- Evidence (numerical / audit):
--   • Extremizer is overwhelmingly non-axis (~86% mass on 0-zero
--     coordinate-permutation sector at N=12).
--   • Mass concentrated in shells N-1 and N.
--   • Leading orbit classes (1,7,12) and (0,1,11) at N=12;
--     persistent family (0,1,N-1) across all tested shells.
--   • Extremizer-weighted row ratio ≈ 1.489 (not alone decisive).
--   • Pairwise wavevector dot products show residual anisotropy,
--     not a single equilateral frame.
--   • The O(4) anisotropic quotient is 1-dimensional (2602.0087),
--     which constrains the admissible extremizer directions.
--
-- Status: paperImport / auditTested.
--   The structural observations are numerically robust across
--   N ∈ {6,8,10,12,14,16}.  The O(4) classification is imported.
--   The full proof term linking the O(4) quotient to the Gate 1
--   extremizer is not yet constructed.

data NSTriadKNGate2AExtremizerStructuralProperty : Set where
  nonAxisStructureObserved :
    NSTriadKNGate2AExtremizerStructuralProperty
  topShellMassConcentrationObserved :
    NSTriadKNGate2AExtremizerStructuralProperty
  orbitClassFamilyPersistent :
    NSTriadKNGate2AExtremizerStructuralProperty
  mixedShellSeamIsHardest :
    NSTriadKNGate2AExtremizerStructuralProperty
  o4AnisotropicQuotientImported :
    NSTriadKNGate2AExtremizerStructuralProperty

canonicalStructuralProperties :
  List NSTriadKNGate2AExtremizerStructuralProperty
canonicalStructuralProperties =
  nonAxisStructureObserved
  ∷ topShellMassConcentrationObserved
  ∷ orbitClassFamilyPersistent
  ∷ mixedShellSeamIsHardest
  ∷ o4AnisotropicQuotientImported
  ∷ []

canonicalClaimText : String
canonicalClaimText =
  "Gate 1 near-extremizers belong to a controlled anisotropic seam "
  ++ "family constrained by the 1-dim O(4) anisotropic subspace "
  ++ "(2602.0087 Thm 3.6)."

canonicalEvidenceText : String
canonicalEvidenceText =
  "Evidence across N=6,8,10,12,14,16: non-axis (≈86% 0-zero mass), "
  ++ "top-shell concentration, persistent orbit family (0,1,N-1), "
  ++ "mixed-shell seam hardest. Angular frame shows residual anisotropy."

canonicalLimitationText : String
canonicalLimitationText =
  "The O(4) classification is paperImport (2602.0087).  The extremizer "
  ++ "is numerically robust but the proof linking the O(4) quotient to "
  ++ "the Gate 1 extremizer direction is not yet constructed in Agda."

record NSTriadKNGate2AEP1ExtremizerClassification : Setω where
  constructor mkNSTriadKNGate2AEP1ExtremizerClassification
  field
    claimText : String
    claimTextIsCanonical :
      claimText ≡ canonicalClaimText

    evidenceText : String
    evidenceTextIsCanonical :
      evidenceText ≡ canonicalEvidenceText

    limitationText : String
    limitationTextIsCanonical :
      limitationText ≡ canonicalLimitationText

    structuralProperties :
      List NSTriadKNGate2AExtremizerStructuralProperty
    structuralPropertiesAreCanonical :
      structuralProperties ≡ canonicalStructuralProperties

    ep1ClaimStated : Bool
    ep1ClaimStatedIsTrue :
      ep1ClaimStated ≡ true

    ep1NumericallySupported : Bool
    ep1NumericallySupportedIsTrue :
      ep1NumericallySupported ≡ true

    ep1O4ClassificationImported : Bool
    ep1O4ClassificationImportedIsTrue :
      ep1O4ClassificationImported ≡ true

    ep1ProofConstructed : Bool
    ep1ProofConstructedIsFalse :
      ep1ProofConstructed ≡ false

    ep1Promoted : Bool
    ep1PromotedIsFalse :
      ep1Promoted ≡ false

open NSTriadKNGate2AEP1ExtremizerClassification public

canonicalNSTriadKNGate2AEP1ExtremizerClassification :
  NSTriadKNGate2AEP1ExtremizerClassification
canonicalNSTriadKNGate2AEP1ExtremizerClassification =
  mkNSTriadKNGate2AEP1ExtremizerClassification
    canonicalClaimText
    refl
    canonicalEvidenceText
    refl
    canonicalLimitationText
    refl
    canonicalStructuralProperties
    refl
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl

ep1KeepsClayFalse :
  (r : NSTriadKNGate2AEP1ExtremizerClassification) →
  NSTriadKNGate2AEP1ExtremizerClassification.ep1Promoted r ≡ false
ep1KeepsClayFalse _ = refl

----------------------------------------------------------------------
-- EP1 Paper Import Receipt: O(4) anisotropic classification
-- (external reference 2602.0087 Thm 3.6).
--
-- Purpose: pin the exact external theorem, its hypotheses, and the
-- mapping into the seam setting.  Prevents the citation from
-- functioning as an accidental black box.

data EP1ExternalTheoremLabel : Set where
  thm26020087AnisotropicSubspaceClassification :
    EP1ExternalTheoremLabel

canonicalEP1ExternalTheoremLabel : EP1ExternalTheoremLabel
canonicalEP1ExternalTheoremLabel =
  thm26020087AnisotropicSubspaceClassification

data EP1HypothesisMappingStatus : Set where
  hypothesisDirectlyApplicable :
    EP1HypothesisMappingStatus
  hypothesisRequiresSeamAdaptation :
    EP1HypothesisMappingStatus
  hypothesisReferenceUnavailable :
    EP1HypothesisMappingStatus

record EP1HypothesisMappingEntry : Set where
  constructor mkEP1HypothesisMappingEntry
  field
    sourceHypothesis : String
    targetSeamProperty : String
    mappingStatus : EP1HypothesisMappingStatus
    mappingNote : String

canonicalEP1PaperId : String
canonicalEP1PaperId =
  "2602.0087"

canonicalEP1TheoremClaim : String
canonicalEP1TheoremClaim =
  "O(4) anisotropic subspace of W₄-scalar dimension-6 operators is "
  ++ "1-dimensional, spanned by I₁ − (1/4)I₂. (Thm 3.6)"

canonicalEP1HypothesisMappings :
  List EP1HypothesisMappingEntry
canonicalEP1HypothesisMappings =
  mkEP1HypothesisMappingEntry
    "O(4) acts on the W₄-scalar lattice of dimension-6 operators"
    "The seam shell-pair (N-1,N) breaks full O(4); residual symmetry "
    "group is the stabilizer of the radial shell direction"
    hypothesisRequiresSeamAdaptation
    ("The extremizer concentrates on shells N-1,N; the radial "
     ++ "direction is the one broken by the seam cut, so the "
     ++ "anisotropic quotient constrains the allowed extremizer "
     ++ "configurations on these shells.")
  ∷ mkEP1HypothesisMappingEntry
    "The operator space splits into O(4)-invariant ⊕ anisotropic (1-dim)"
    "Extremizer non-axis mass (~86% at N=12) lies in the anisotropic "
    "component; the 1-dim quotient fixes a unique direction"
    hypothesisDirectlyApplicable
    ("The extremizer's overwhelming non-axis character and "
     ++ "persistent orbit family (0,1,N-1) are consistent with a "
     ++ "single anisotropic mode being selected.")
  ∷ mkEP1HypothesisMappingEntry
    "The anisotropic generator is I₁ − (1/4)I₂"
    "The extremizer wavevector frame shows residual anisotropy (not "
    "equilateral); the pair-mass diagnostics are consistent with an "
    "I₁-like contribution dominating over I₂"
    hypothesisRequiresSeamAdaptation
    ("The exact extremizer in the shell-pair coordinates is not "
     ++ "the continuum operator I₁ − (1/4)I₂; the mapping goes "
     ++ "through the lattice operator representation on the seam "
     ++ "carrier 1_C^⊥.")
  ∷ mkEP1HypothesisMappingEntry
    "Classification is algebraic/representation-theoretic, no clustering needed"
    "The seam extremizer classification similarly depends on the "
    "seam geometry and the Schur complement structure, not on "
    "long-range clustering"
    hypothesisDirectlyApplicable
    ("Both the external theorem and its seam application are "
     ++ "kinematic / single-scale; no cluster expansion is required.")
  ∷ []

record EP1PaperImportReceipt : Setω where
  constructor mkEP1PaperImportReceipt
  field
    paperId : String
    paperIdIsCanonical :
      paperId ≡ canonicalEP1PaperId

    theoremLabel : EP1ExternalTheoremLabel
    theoremLabelIsCanonical :
      theoremLabel ≡
        thm26020087AnisotropicSubspaceClassification

    theoremClaim : String
    theoremClaimIsCanonical :
      theoremClaim ≡ canonicalEP1TheoremClaim

    hypothesisMappings :
      List EP1HypothesisMappingEntry
    hypothesisMappingsAreCanonical :
      hypothesisMappings ≡ canonicalEP1HypothesisMappings

    hypothesesDocumentPaperConditions : Bool
    hypothesesDocumentPaperConditionsIsTrue :
      hypothesesDocumentPaperConditions ≡ true

    mappingDocumentsSeamBridge : Bool
    mappingDocumentsSeamBridgeIsTrue :
      mappingDocumentsSeamBridge ≡ true

    importAsserted : Bool
    importAssertedIsTrue :
      importAsserted ≡ true

    importVerifiedWithinDashi : Bool
    importVerifiedWithinDashiIsFalse :
      importVerifiedWithinDashi ≡ false

    internalProofConstructed : Bool
    internalProofConstructedIsFalse :
      internalProofConstructed ≡ false

open EP1PaperImportReceipt public

canonicalEP1PaperImportReceipt : EP1PaperImportReceipt
canonicalEP1PaperImportReceipt =
  mkEP1PaperImportReceipt
    canonicalEP1PaperId
    refl
    thm26020087AnisotropicSubspaceClassification
    refl
    canonicalEP1TheoremClaim
    refl
    canonicalEP1HypothesisMappings
    refl
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl

receiptKeepsO4AsImport :
  (r : EP1PaperImportReceipt) →
  EP1PaperImportReceipt.importVerifiedWithinDashi r ≡ false
receiptKeepsO4AsImport _ = refl
