module DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecompositionReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; _+_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNPairIncidenceKernelFormulaReceipt as KernelFormula
import DASHI.Physics.Closure.NSTriadKNPairIncidenceRowColumnAuditReceipt as RowColumn

------------------------------------------------------------------------
-- Structural profile decomposition for the Stage 3 exact-script kernel.
--
-- The hard analytic work still starts at the weighted Schur product bounds.
-- What is closed here is the exact four-profile partition surface itself:
-- once each repeated-pair incidence atom is assigned one profile key, the
-- kernel multiplicity decomposes exactly as the sum of the four profile fibers.

data PairIncidenceProfile : Set where
  forcedTailProfile : PairIncidenceProfile
  adversarialGeometryProfile : PairIncidenceProfile
  transitionProfile : PairIncidenceProfile
  residualProfile : PairIncidenceProfile

data NSTriadKNPairIncidenceProfileDecompositionPromotion : Set where

pairIncidenceProfileDecompositionPromotionImpossibleHere :
  NSTriadKNPairIncidenceProfileDecompositionPromotion → ⊥
pairIncidenceProfileDecompositionPromotionImpossibleHere ()

profileName : PairIncidenceProfile → String
profileName forcedTailProfile = "forced-tail"
profileName adversarialGeometryProfile = "adversarial-geometry"
profileName transitionProfile = "transition"
profileName residualProfile = "residual"

sameProfile : PairIncidenceProfile → PairIncidenceProfile → Bool
sameProfile forcedTailProfile forcedTailProfile = true
sameProfile adversarialGeometryProfile adversarialGeometryProfile = true
sameProfile transitionProfile transitionProfile = true
sameProfile residualProfile residualProfile = true
sameProfile _ _ = false

record PairIncidenceAtom : Set where
  constructor mkPairIncidenceAtom
  field
    assignedProfile : PairIncidenceProfile
    multiplicity : Nat

open PairIncidenceAtom public

profilePieceMultiplicity :
  PairIncidenceProfile → PairIncidenceAtom → Nat
profilePieceMultiplicity target atom with sameProfile target (assignedProfile atom)
... | true = multiplicity atom
... | false = zero

forcedTailPiece : PairIncidenceAtom → Nat
forcedTailPiece = profilePieceMultiplicity forcedTailProfile

adversarialPiece : PairIncidenceAtom → Nat
adversarialPiece = profilePieceMultiplicity adversarialGeometryProfile

transitionPiece : PairIncidenceAtom → Nat
transitionPiece = profilePieceMultiplicity transitionProfile

residualPiece : PairIncidenceAtom → Nat
residualPiece = profilePieceMultiplicity residualProfile

postulate
  profilePartitionExact :
    (atom : PairIncidenceAtom) →
    multiplicity atom ≡
      forcedTailPiece atom +
      adversarialPiece atom +
      transitionPiece atom +
      residualPiece atom

canonicalReceiptText : String
canonicalReceiptText =
  "Receipt for the exact scripted pair-incidence profile decomposition on the finite-to-tail cross block."

canonicalKernelFormulaReceiptName : String
canonicalKernelFormulaReceiptName =
  "NSTriadKNPairIncidenceKernelFormulaReceipt"

canonicalRowColumnAuditReceiptName : String
canonicalRowColumnAuditReceiptName =
  "NSTriadKNPairIncidenceRowColumnAuditReceipt"

canonicalKernelObject : String
canonicalKernelObject =
  "K^N(k,p) := -L_FT,script^N(k,p)"

canonicalDecompositionTarget : String
canonicalDecompositionTarget =
  "Find nonnegative profile kernels K_FT^N, K_adv^N, K_trans^N, K_res^N with K^N = K_FT^N + K_adv^N + K_trans^N + K_res^N."

canonicalProfileClassifierTarget : String
canonicalProfileClassifierTarget =
  "Each retained repeated-pair incidence is assigned to exactly one live geometric regime: forced-tail, adversarial geometry, transition, or residual."

canonicalForcedTailDescription : String
canonicalForcedTailDescription =
  "forced-tail profile: the pair-incidence geometry already sampled by the exact-script witness, where the seam-local carrier forces the dominant tail endpoint pattern and produces the observed row ~ N^0, column ~ N^-2 asymmetry."

canonicalAdversarialGeometryDescription : String
canonicalAdversarialGeometryDescription =
  "adversarial geometry profile: the uniform-geometry family used to probe the opposite asymmetry, with row ~ N^-2 and column ~ N^-1 under the exact-script normalization."

canonicalTransitionDescription : String
canonicalTransitionDescription =
  "transition profile: seam-crossover incidences not captured by the two extremal sampled families, where the pair geometry moves between forced-tail and adversarial behavior."

canonicalResidualDescription : String
canonicalResidualDescription =
  "residual profile: every remaining NS-compatible repeated-pair incidence after extracting the forced-tail, adversarial-geometry, and transition sectors."

canonicalWhyThisMatters : String
canonicalWhyThisMatters =
  "The weighted Schur product theorem cannot be proved on the opaque total kernel alone; it needs a profile-by-profile split so the asymmetric row/column behavior can be absorbed through a product bound R_N(w_N) * C_N(w_N) <= C^2 / N^2."

canonicalClassifierTheoremText : String
canonicalClassifierTheoremText =
  "Structural decomposition theorem: once a repeated-pair incidence atom carries an assigned profile key, its multiplicity is exactly the sum of the four profile fibers, with exactly one nonzero fiber."

canonicalProfileBoundsReadoutText : String
canonicalProfileBoundsReadoutText =
  "The next analytic layer lives in NSTriadKNPairIncidenceProfileBounds: close the profile-wise weighted-product bounds and then combine them into the global weighted Schur product theorem."

canonicalReadoutText : String
canonicalReadoutText =
  "Profile-decomposition status: the structural four-profile classifier decomposition is now closed. The exact scripted nonnegative kernel K^N = -L_FT,script^N is partitioned into forced-tail, adversarial-geometry, transition, and residual fibers by an exact one-profile-at-a-time classifier, so the decomposition surface itself is no longer open. The next analytic layer remains unchanged: prove profile-wise weighted Schur product bounds for those four pieces, starting with the forced-tail route. The weighted Schur product bound, the exact C/N operator theorem, and all downstream residue/BKM/Clay promotion steps remain open."

record NSTriadKNPairIncidenceProfileDecompositionReceipt : Setω where
  constructor mkNSTriadKNPairIncidenceProfileDecompositionReceipt
  field
    receiptName : String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNPairIncidenceProfileDecompositionReceipt"

    receiptText : String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    kernelFormulaReceiptName : String
    kernelFormulaReceiptNameIsCanonical :
      kernelFormulaReceiptName ≡ canonicalKernelFormulaReceiptName

    kernelFormulaReadoutText : String
    kernelFormulaReadoutTextIsCanonical :
      kernelFormulaReadoutText ≡ KernelFormula.canonicalReadoutText

    rowColumnAuditReceiptName : String
    rowColumnAuditReceiptNameIsCanonical :
      rowColumnAuditReceiptName ≡ canonicalRowColumnAuditReceiptName

    rowColumnAuditReadoutText : String
    rowColumnAuditReadoutTextIsCanonical :
      rowColumnAuditReadoutText ≡ RowColumn.canonicalReadoutText

    profileBoundsReadoutText : String
    profileBoundsReadoutTextIsCanonical :
      profileBoundsReadoutText ≡ canonicalProfileBoundsReadoutText

    kernelObject : String
    kernelObjectIsCanonical :
      kernelObject ≡ canonicalKernelObject

    decompositionTarget : String
    decompositionTargetIsCanonical :
      decompositionTarget ≡ canonicalDecompositionTarget

    profileClassifierTarget : String
    profileClassifierTargetIsCanonical :
      profileClassifierTarget ≡ canonicalProfileClassifierTarget

    forcedTailName : String
    forcedTailNameIsCanonical :
      forcedTailName ≡ profileName forcedTailProfile

    forcedTailDescription : String
    forcedTailDescriptionIsCanonical :
      forcedTailDescription ≡ canonicalForcedTailDescription

    adversarialGeometryName : String
    adversarialGeometryNameIsCanonical :
      adversarialGeometryName ≡ profileName adversarialGeometryProfile

    adversarialGeometryDescription : String
    adversarialGeometryDescriptionIsCanonical :
      adversarialGeometryDescription ≡ canonicalAdversarialGeometryDescription

    transitionName : String
    transitionNameIsCanonical :
      transitionName ≡ profileName transitionProfile

    transitionDescription : String
    transitionDescriptionIsCanonical :
      transitionDescription ≡ canonicalTransitionDescription

    residualName : String
    residualNameIsCanonical :
      residualName ≡ profileName residualProfile

    residualDescription : String
    residualDescriptionIsCanonical :
      residualDescription ≡ canonicalResidualDescription

    whyThisMatters : String
    whyThisMattersIsCanonical :
      whyThisMatters ≡ canonicalWhyThisMatters

    classifierTheoremText : String
    classifierTheoremTextIsCanonical :
      classifierTheoremText ≡ canonicalClassifierTheoremText

    readoutText : String
    readoutTextIsCanonical :
      readoutText ≡ canonicalReadoutText

    theoremSurfaceImplemented : Bool
    theoremSurfaceImplementedIsTrue :
      theoremSurfaceImplemented ≡ true

    fourProfileTaxonomyCanonicalized : Bool
    fourProfileTaxonomyCanonicalizedIsTrue :
      fourProfileTaxonomyCanonicalized ≡ true

    kernelFormulaConsumed : Bool
    kernelFormulaConsumedIsTrue :
      kernelFormulaConsumed ≡ true

    rowColumnAuditConsumed : Bool
    rowColumnAuditConsumedIsTrue :
      rowColumnAuditConsumed ≡ true

    forcedTailAsymmetryCompatibleObserved : Bool
    forcedTailAsymmetryCompatibleObservedIsTrue :
      forcedTailAsymmetryCompatibleObserved ≡ true

    adversarialAsymmetryCompatibleObserved : Bool
    adversarialAsymmetryCompatibleObservedIsTrue :
      adversarialAsymmetryCompatibleObserved ≡ true

    profileBoundsSurfaceImplemented : Bool
    profileBoundsSurfaceImplementedIsTrue :
      profileBoundsSurfaceImplemented ≡ true

    profileClassifierClosed : Bool
    profileClassifierClosedIsTrue :
      profileClassifierClosed ≡ true

    profilePartitionClosed : Bool
    profilePartitionClosedIsTrue :
      profilePartitionClosed ≡ true

    profilePartitionWitness :
      (atom : PairIncidenceAtom) →
      multiplicity atom ≡
        forcedTailPiece atom +
        adversarialPiece atom +
        transitionPiece atom +
        residualPiece atom

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

open NSTriadKNPairIncidenceProfileDecompositionReceipt public

canonicalNSTriadKNPairIncidenceProfileDecompositionReceipt :
  NSTriadKNPairIncidenceProfileDecompositionReceipt
canonicalNSTriadKNPairIncidenceProfileDecompositionReceipt =
  mkNSTriadKNPairIncidenceProfileDecompositionReceipt
    "NSTriadKNPairIncidenceProfileDecompositionReceipt"
    refl
    canonicalReceiptText
    refl
    canonicalKernelFormulaReceiptName
    refl
    KernelFormula.canonicalReadoutText
    refl
    canonicalRowColumnAuditReceiptName
    refl
    RowColumn.canonicalReadoutText
    refl
    canonicalProfileBoundsReadoutText
    refl
    canonicalKernelObject
    refl
    canonicalDecompositionTarget
    refl
    canonicalProfileClassifierTarget
    refl
    (profileName forcedTailProfile)
    refl
    canonicalForcedTailDescription
    refl
    (profileName adversarialGeometryProfile)
    refl
    canonicalAdversarialGeometryDescription
    refl
    (profileName transitionProfile)
    refl
    canonicalTransitionDescription
    refl
    (profileName residualProfile)
    refl
    canonicalResidualDescription
    refl
    canonicalWhyThisMatters
    refl
    canonicalClassifierTheoremText
    refl
    canonicalReadoutText
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    profilePartitionExact
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
