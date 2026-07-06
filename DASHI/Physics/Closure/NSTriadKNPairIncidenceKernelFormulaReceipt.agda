module DASHI.Physics.Closure.NSTriadKNPairIncidenceKernelFormulaReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Receipt for the exact scripted repeated-pair kernel formula.
--
-- This surface records the definitional Stage 3 step that is genuinely closed:
-- the finite-to-tail cross-block entry is the negative repeated-pair incidence
-- sum over retained positive-sector triad weights.  This does not prove the
-- profile decomposition, weighted Schur product bound, C/N operator theorem,
-- residue transfer, or any downstream NS/BKM/Clay promotion.

data NSTriadKNPairIncidenceKernelFormulaPromotion : Set where

pairIncidenceKernelFormulaPromotionImpossibleHere :
  NSTriadKNPairIncidenceKernelFormulaPromotion → ⊥
pairIncidenceKernelFormulaPromotionImpossibleHere ()

canonicalReceiptText : String
canonicalReceiptText =
  "Receipt for the exact scripted repeated-pair kernel formula on the finite-to-tail cross block."

canonicalDocPath : String
canonicalDocPath =
  "docs/ns_triad_kn_pair_incidence_kernel_formula.md"

canonicalKernelStatement : String
canonicalKernelStatement =
  "For finite mode k and tail mode p, L_FT,script^N(k,p) = -sum_{tau : {k,p} in P(tau)} m_N(tau)."

canonicalNonnegativeKernelStatement : String
canonicalNonnegativeKernelStatement =
  "Equivalently, K_N(k,p) := -L_FT,script^N(k,p) = sum_{tau : {k,p} in P(tau)} m_N(tau) >= 0."

canonicalTriadWeightDefinition : String
canonicalTriadWeightDefinition =
  "m_N(tau) = (sqrt(pi_i*pi_j*pi_l)/3) * max(cos(phi_i + phi_j - phi_l), 0)."

canonicalProofIdea : String
canonicalProofIdea =
  "Each rank-one Laplacian term m_N(tau) b_e b_e^T contributes -m_N(tau) exactly on its unordered off-diagonal edge and 0 elsewhere, so summing over retained triads gives the repeated-pair incidence formula."

canonicalReadoutText : String
canonicalReadoutText =
  "Kernel-formula status: closed at the definitional level. The exact scripted finite-to-tail cross block is a repeated-pair incidence kernel with nonnegative Schur weights K_N(k,p) = -L_FT,script^N(k,p). The structural four-profile decomposition is now also closed; the next open Stage 3 task is the weighted Schur product bound and its downstream operator/residue consequences. Theorem/full-NS/BKM/Clay promotion remain false."

record NSTriadKNPairIncidenceKernelFormulaReceipt : Setω where
  constructor mkNSTriadKNPairIncidenceKernelFormulaReceipt
  field
    receiptName : String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNPairIncidenceKernelFormulaReceipt"

    receiptText : String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    docPath : String
    docPathIsCanonical :
      docPath ≡ canonicalDocPath

    kernelStatement : String
    kernelStatementIsCanonical :
      kernelStatement ≡ canonicalKernelStatement

    nonnegativeKernelStatement : String
    nonnegativeKernelStatementIsCanonical :
      nonnegativeKernelStatement ≡ canonicalNonnegativeKernelStatement

    triadWeightDefinition : String
    triadWeightDefinitionIsCanonical :
      triadWeightDefinition ≡ canonicalTriadWeightDefinition

    proofIdea : String
    proofIdeaIsCanonical :
      proofIdea ≡ canonicalProofIdea

    readoutText : String
    readoutTextIsCanonical :
      readoutText ≡ canonicalReadoutText

    repeatedPairIncidenceFormulaDerived : Bool
    repeatedPairIncidenceFormulaDerivedIsTrue :
      repeatedPairIncidenceFormulaDerived ≡ true

    nonnegativeSchurKernelDerived : Bool
    nonnegativeSchurKernelDerivedIsTrue :
      nonnegativeSchurKernelDerived ≡ true

    profileDecompositionClosed : Bool
    profileDecompositionClosedIsTrue :
      profileDecompositionClosed ≡ true

    weightedSchurProductBoundClosed : Bool
    weightedSchurProductBoundClosedIsFalse :
      weightedSchurProductBoundClosed ≡ false

    pairIncidenceCNTheoremClosed : Bool
    pairIncidenceCNTheoremClosedIsFalse :
      pairIncidenceCNTheoremClosed ≡ false

    qGapTransferClosed : Bool
    qGapTransferClosedIsFalse :
      qGapTransferClosed ≡ false

    theoremPromoted : Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    fullNSPromoted : Bool
    fullNSPromotedIsFalse :
      fullNSPromoted ≡ false

    bkmExclusionProved : Bool
    bkmExclusionProvedIsFalse :
      bkmExclusionProved ≡ false

    clayPromoted : Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

open NSTriadKNPairIncidenceKernelFormulaReceipt public

canonicalNSTriadKNPairIncidenceKernelFormulaReceipt :
  NSTriadKNPairIncidenceKernelFormulaReceipt
canonicalNSTriadKNPairIncidenceKernelFormulaReceipt =
  mkNSTriadKNPairIncidenceKernelFormulaReceipt
    "NSTriadKNPairIncidenceKernelFormulaReceipt"
    refl
    canonicalReceiptText
    refl
    canonicalDocPath
    refl
    canonicalKernelStatement
    refl
    canonicalNonnegativeKernelStatement
    refl
    canonicalTriadWeightDefinition
    refl
    canonicalProofIdea
    refl
    canonicalReadoutText
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
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
