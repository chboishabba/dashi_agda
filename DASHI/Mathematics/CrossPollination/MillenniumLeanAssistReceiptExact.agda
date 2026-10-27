module DASHI.Mathematics.CrossPollination.MillenniumLeanAssistReceiptExact where

------------------------------------------------------------------------
-- SIBLING LEAN PRODUCER CUSTODY FOR THE THREE-LANE MILLENNIUM CONTINUATION
--
-- This owner records source-level provenance only.
--
-- dashi_lean4 PR #10 carries two focused producers:
--
--   Synthesis/MillenniumHodgeCP1Quotient.lean
--     mathlib Projectivization quotient + lift/induction + CP1 chart overlap
--
--   Synthesis/MillenniumBSDRationalSquareBits.lean
--     rational sign-square invariance + padicValRat v2 parity-square invariance
--
--   Synthesis/MillenniumBSDCMPrimeWitness.lean
--     p = 1 mod 4 prime -> p = u^2 + v^2 via mathlib Nat.Prime.sq_add_sq
--
-- The files are rooted in Synthesis.lean on the sibling branch.
--
-- IMPORTANT:
--   * GitHub Actions had not produced a Lean Action run at the observed head.
--   * No local Lean executable/build receipt was available in this environment.
--   * Therefore this receipt does NOT promote either producer to kernel-observed.
--   * Agda/Lean same-object transport is also separate and remains unpaid.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Mathematics.Complexity.PNotEqualsNPQ1TerminalSemanticsDecisionFailureExact as PNPQ1
import DASHI.Physics.Closure.NSClayFourAlternativeReleasedProofBidiExact as NSReleased

record MillenniumLeanAssistReceipt : Set where
  constructor millennium-lean-assist-receipt
  field
    repository :
      String

    branch :
      String

    pullRequest :
      String

    observedHead :
      String

    toolchain :
      String

    mathlibRevision :
      String

    hodgeSource :
      String

    bsdSource :
      String

    bsdCMSource :
      String

    hodgeCP1NormalFormSource :
      String

    hodgeCP1SphereSource :
      String

    bsdSquareClassQuotientSource :
      String

    bsdKummerQuotientSource :
      String

    bsdCMClassificationSource :
      String

    bsdCMInertCharacterSumSource :
      String

    bsdLocalSquareClassSource :
      String

    bsdFrobeniusPointCountSource :
      String

    bsdTotalLocalKummerSource :
      String

    bsdMathlibLFunctionSource :
      String

    hodgeCP1CellularH2Source :
      String

    hodgeCP1QuotientSourcePresent :
      Bool

    hodgeMathlibProjectivizationReused :
      Bool

    bsdSquareBitsSourcePresent :
      Bool

    bsdMathlibPadicValRatReused :
      Bool

    bsdCMSplitPrimeSourcePresent :
      Bool

    bsdMathlibTwoSquaresReused :
      Bool

    hodgeCP1NormalFormSourcePresent :
      Bool

    hodgeCP1SphereHomeomorphismSourcePresent :
      Bool

    bsdLiteralSquareClassQuotientSourcePresent :
      Bool

    bsdLiteralKummerQuotientSourcePresent :
      Bool

    bsdAllPrimeCMCaseSplitSourcePresent :
      Bool

    bsdInertCharacterSumZeroSourcePresent :
      Bool

    bsdLocalQpSquareClassSourcePresent :
      Bool

    bsdRationalToLocalKummerSourcePresent :
      Bool

    bsdLiteralFrobeniusPointCountSourcePresent :
      Bool

    bsdInertSignedFrobeniusZeroSourcePresent :
      Bool

    bsdTotalLocalKummerImageSourcePresent :
      Bool

    bsdMathlibGlobalLFunctionSourcePresent :
      Bool

    bsdAllNCoefficientFamilySourcePresent :
      Bool

    bsdAllNCoprimeMultiplicativitySourcePresent :
      Bool

    hodgeCP1CellularH2SourcePresent :
      Bool

    hodgePointCellularGeneratorSourcePresent :
      Bool

    sourcesRootedInSynthesis :
      Bool

    sourceEscapeAuditClean :
      Bool

    leanKernelReceiptObserved :
      Bool

    agdaSameObjectImportPaid :
      Bool

open MillenniumLeanAssistReceipt public

currentMillenniumLeanAssistReceipt :
  MillenniumLeanAssistReceipt
currentMillenniumLeanAssistReceipt =
  millennium-lean-assist-receipt
    "chboishabba/dashi_lean4"
    "agent/millennium-three-lane-lean-assist"
    "#10"
    "196c1041eea4f5a62c4d99d8f6d0fd149a6c86b5"
    "leanprover/lean4:v4.28.0"
    "mathlib v4.28.0"
    "Synthesis/MillenniumHodgeCP1Quotient.lean"
    "Synthesis/MillenniumBSDRationalSquareBits.lean"
    "Synthesis/MillenniumBSDCMPrimeWitness.lean"
    "Synthesis/MillenniumHodgeCP1NormalForm.lean"
    "Synthesis/MillenniumHodgeCP1TopologicalSphere.lean"
    "Synthesis/MillenniumBSDRationalSquareClassQuotient.lean"
    "Synthesis/MillenniumBSDRationalKummerQuotient.lean"
    "Synthesis/MillenniumBSDCMPrimeClassification.lean"
    "Synthesis/MillenniumBSDCMInertCharacterSum.lean"
    "Synthesis/MillenniumBSDLocalSquareClass.lean"
    "Synthesis/MillenniumBSDFrobeniusPointCount.lean"
    "Synthesis/MillenniumBSDTotalLocalKummer.lean"
    "Synthesis/MillenniumBSDMathlibLFunctionWeld.lean"
    "Synthesis/MillenniumHodgeCP1CellularH2.lean"
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    false
    false


------------------------------------------------------------------------
-- CURRENT LEAN MILLENNIUM EXTERNAL-ACCEPTANCE CUSTODY
--
-- This receipt updates external target custody without replacing the older
-- theorem-source receipt above. It records the exact independent target pin,
-- the existing DASHI same-object weld reuse rule, and the fail-closed status
-- of targets that LeanDojo marks as incomplete.
--
-- Attribution:
--   * LeanDojo and its contributors own the external Lean statements.
--   * Existing DASHI Lean/Agda theorem owners retain proof ownership.
--   * This Agda owner records custody and non-promotion only.
------------------------------------------------------------------------

record MillenniumExternalAcceptanceReceipt : Set where
  constructor millennium-external-acceptance-receipt
  field
    leanRepository : String
    leanPullRequest : String
    leanBranch : String
    leanObservedHead : String
    leanDojoRepository : String
    leanDojoCommit : String
    leanDojoVendorPath : String
    riemannExternalTarget : String
    navierStokesExternalTargets : String
    bsdExternalTarget : String
    hodgeExternalTarget : String
    yangMillsExternalTarget : String
    riemannExistingTerminalSource : String
    navierStokesLiteralTerminalSource : String
    bsdExistingRankWeldSource : String
    yangMillsExistingPhysicalWeldSource : String
    exactExternalDeclarationsPinned : Bool
    existingSameObjectWeldsReused : Bool
    hodgeExternalTargetValid : Bool
    yangMillsExternalTargetValid : Bool
    directCrossToolchainAdapterKernelChecked : Bool
    receiptCreatesPrizeProof : Bool

open MillenniumExternalAcceptanceReceipt public

currentMillenniumExternalAcceptanceReceipt :
  MillenniumExternalAcceptanceReceipt
currentMillenniumExternalAcceptanceReceipt =
  millennium-external-acceptance-receipt
    "chboishabba/dashi_lean4"
    "#45"
    "agent/millennium-external-target-adapters-20261006"
    "9ab3f6a852af95061cd7ba5a890767ba7c1a1817"
    "lean-dojo/LeanMillenniumPrizeProblems"
    "603053dc267cf3efe422f438eb78098c0ececd6f"
    "vendor/LeanMillenniumPrizeProblems"
    "Millennium.ClayRiemannHypothesis"
    "MillenniumNavierStokes.FeffermanA|B|C|D"
    "MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer"
    "MillenniumHodge.ClayHodge"
    "MillenniumYangMills.ClayYangMills"
    "Synthesis.RiemannSelectedRHMaxCutFrontier"
    "ExternalClayNS/LiteralABCD.lean"
    "Synthesis/MillenniumBSDUniversalRankWeld.lean"
    "Welds/YMClayAssembly.lean"
    true
    true
    false
    false
    false
    false

millenniumExternalDeclarationsPinned :
  exactExternalDeclarationsPinned currentMillenniumExternalAcceptanceReceipt ≡ true
millenniumExternalDeclarationsPinned = refl

millenniumExistingSameObjectWeldsReused :
  existingSameObjectWeldsReused currentMillenniumExternalAcceptanceReceipt ≡ true
millenniumExistingSameObjectWeldsReused = refl

millenniumHodgeExternalTargetInvalid :
  hodgeExternalTargetValid currentMillenniumExternalAcceptanceReceipt ≡ false
millenniumHodgeExternalTargetInvalid = refl

millenniumYangMillsExternalTargetInvalid :
  yangMillsExternalTargetValid currentMillenniumExternalAcceptanceReceipt ≡ false
millenniumYangMillsExternalTargetInvalid = refl

millenniumCrossToolchainAdapterStillNotKernelChecked :
  directCrossToolchainAdapterKernelChecked currentMillenniumExternalAcceptanceReceipt ≡ false
millenniumCrossToolchainAdapterStillNotKernelChecked = refl

millenniumExternalReceiptDoesNotCreatePrizeProof :
  receiptCreatesPrizeProof currentMillenniumExternalAcceptanceReceipt ≡ false
millenniumExternalReceiptDoesNotCreatePrizeProof = refl


------------------------------------------------------------------------
-- Current PR #45 max-cut details.
--
-- These are derived custody facts. They do not create Lean or Agda proof
-- authority. Existing same-object and physical-object theorem owners remain
-- authoritative.
------------------------------------------------------------------------

leanMillenniumRHExactStatementWeldSourceWritten : Bool
leanMillenniumRHExactStatementWeldSourceWritten = true

leanMillenniumRHExactStatementWeldSourceWrittenIsTrue :
  leanMillenniumRHExactStatementWeldSourceWritten ≡ true
leanMillenniumRHExactStatementWeldSourceWrittenIsTrue = refl

leanMillenniumNSFeffermanCExactTermSourceWritten : Bool
leanMillenniumNSFeffermanCExactTermSourceWritten = true

leanMillenniumNSFeffermanCExactTermSourceWrittenIsTrue :
  leanMillenniumNSFeffermanCExactTermSourceWritten ≡ true
leanMillenniumNSFeffermanCExactTermSourceWrittenIsTrue = refl

leanMillenniumNSFeffermanDExactTermSourceWritten : Bool
leanMillenniumNSFeffermanDExactTermSourceWritten = true

leanMillenniumNSFeffermanDExactTermSourceWrittenIsTrue :
  leanMillenniumNSFeffermanDExactTermSourceWritten ≡ true
leanMillenniumNSFeffermanDExactTermSourceWrittenIsTrue = refl

leanMillenniumNSAdapterRequiresNewMathematics : Bool
leanMillenniumNSAdapterRequiresNewMathematics = false

leanMillenniumNSAdapterRequiresNoNewMathematics :
  leanMillenniumNSAdapterRequiresNewMathematics ≡ false
leanMillenniumNSAdapterRequiresNoNewMathematics = refl

leanMillenniumBSDProjectiveAffineRankWeldSourceWritten : Bool
leanMillenniumBSDProjectiveAffineRankWeldSourceWritten = true

leanMillenniumBSDProjectiveAffineRankWeldSourceWrittenIsTrue :
  leanMillenniumBSDProjectiveAffineRankWeldSourceWritten ≡ true
leanMillenniumBSDProjectiveAffineRankWeldSourceWrittenIsTrue = refl

leanMillenniumPNPTerminalFailureBidiAgdaOwned : Bool
leanMillenniumPNPTerminalFailureBidiAgdaOwned = true

leanMillenniumPNPTerminalFailureBidiAgdaOwnedIsTrue :
  leanMillenniumPNPTerminalFailureBidiAgdaOwned ≡ true
leanMillenniumPNPTerminalFailureBidiAgdaOwnedIsTrue = refl

leanMillenniumNSReleasedMetadataReportsNoSorry : Bool
leanMillenniumNSReleasedMetadataReportsNoSorry =
  NSReleased.releasedLeanMetadataReportsNoSorry4

leanMillenniumNSReleasedMetadataReportsNoSorryIsTrue :
  leanMillenniumNSReleasedMetadataReportsNoSorry ≡ true
leanMillenniumNSReleasedMetadataReportsNoSorryIsTrue = refl

leanMillenniumHodgeFaithfulPrizeTarget : Bool
leanMillenniumHodgeFaithfulPrizeTarget =
  hodgeExternalTargetValid currentMillenniumExternalAcceptanceReceipt

leanMillenniumHodgeFaithfulPrizeTargetIsFalse :
  leanMillenniumHodgeFaithfulPrizeTarget ≡ false
leanMillenniumHodgeFaithfulPrizeTargetIsFalse =
  millenniumHodgeExternalTargetInvalid

LeanMillenniumHodgePrizePromotion : Set
LeanMillenniumHodgePrizePromotion =
  leanMillenniumHodgeFaithfulPrizeTarget ≡ true

leanMillenniumHodgePrizePromotionImpossible :
  LeanMillenniumHodgePrizePromotion → ⊥
leanMillenniumHodgePrizePromotionImpossible ()

leanMillenniumYangMillsFaithfulPrizeTarget : Bool
leanMillenniumYangMillsFaithfulPrizeTarget =
  yangMillsExternalTargetValid currentMillenniumExternalAcceptanceReceipt

leanMillenniumYangMillsFaithfulPrizeTargetIsFalse :
  leanMillenniumYangMillsFaithfulPrizeTarget ≡ false
leanMillenniumYangMillsFaithfulPrizeTargetIsFalse =
  millenniumYangMillsExternalTargetInvalid

LeanMillenniumYangMillsPrizePromotion : Set
LeanMillenniumYangMillsPrizePromotion =
  leanMillenniumYangMillsFaithfulPrizeTarget ≡ true

leanMillenniumYangMillsPrizePromotionImpossible :
  LeanMillenniumYangMillsPrizePromotion → ⊥
leanMillenniumYangMillsPrizePromotionImpossible ()

leanMillenniumExactHeadKernelReceiptObserved : Bool
leanMillenniumExactHeadKernelReceiptObserved =
  directCrossToolchainAdapterKernelChecked
    currentMillenniumExternalAcceptanceReceipt

leanMillenniumExactHeadKernelReceiptStillUnobserved :
  leanMillenniumExactHeadKernelReceiptObserved ≡ false
leanMillenniumExactHeadKernelReceiptStillUnobserved =
  millenniumCrossToolchainAdapterStillNotKernelChecked

LeanMillenniumSourceWrittenKernelPromotion : Set
LeanMillenniumSourceWrittenKernelPromotion =
  leanMillenniumExactHeadKernelReceiptObserved ≡ true

leanMillenniumSourceWrittenKernelPromotionImpossible :
  LeanMillenniumSourceWrittenKernelPromotion → ⊥
leanMillenniumSourceWrittenKernelPromotionImpossible ()
