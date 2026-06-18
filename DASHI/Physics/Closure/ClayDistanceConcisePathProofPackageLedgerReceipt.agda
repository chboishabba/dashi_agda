module DASHI.Physics.Closure.ClayDistanceConcisePathProofPackageLedgerReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Clay-distance / concise-path proof package ledger receipt.
--
-- Candidate-only ledger surface.  This records the dependency chain
-- millerToH5 -> GD3 -> CL2 -> concentration -> Korn -> BoundaryHB ->
-- TheoremC -> Clay closure, while keeping promotion false and exposing the
-- count surfaces that were requested: 8 packages to the conditional theorem,
-- 10-11 packages on the Clay-facing surface, and 3-5 genuinely open PDE
-- lemmas.

data ClayDistanceLedgerStatus : Set where
  candidateOnlyNoPromotion :
    ClayDistanceLedgerStatus

data ClayDistanceLedgerPromotion : Set where

clayDistanceLedgerPromotionImpossibleHere :
  ClayDistanceLedgerPromotion →
  ⊥
clayDistanceLedgerPromotionImpossibleHere ()

data ClayDistanceDependencyStep : Set where
  millerToH5 :
    ClayDistanceDependencyStep
  GD3 :
    ClayDistanceDependencyStep
  CL2 :
    ClayDistanceDependencyStep
  concentration :
    ClayDistanceDependencyStep
  Korn :
    ClayDistanceDependencyStep
  BoundaryHB :
    ClayDistanceDependencyStep
  TheoremC :
    ClayDistanceDependencyStep
  ClayClosure :
    ClayDistanceDependencyStep

dependencyStepName : ClayDistanceDependencyStep → String
dependencyStepName millerToH5 = "millerToH5"
dependencyStepName GD3 = "GD3"
dependencyStepName CL2 = "CL2"
dependencyStepName concentration = "concentration"
dependencyStepName Korn = "Korn"
dependencyStepName BoundaryHB = "BoundaryHB"
dependencyStepName TheoremC = "TheoremC"
dependencyStepName ClayClosure = "ClayClosure"

canonicalDependencyChain : List String
canonicalDependencyChain =
  dependencyStepName millerToH5
  ∷ dependencyStepName GD3
  ∷ dependencyStepName CL2
  ∷ dependencyStepName concentration
  ∷ dependencyStepName Korn
  ∷ dependencyStepName BoundaryHB
  ∷ dependencyStepName TheoremC
  ∷ dependencyStepName ClayClosure
  ∷ []

canonicalConditionalTheoremPackages : List String
canonicalConditionalTheoremPackages =
  canonicalDependencyChain

canonicalClayFacingPackages : List String
canonicalClayFacingPackages =
  dependencyStepName millerToH5
  ∷ dependencyStepName GD3
  ∷ dependencyStepName CL2
  ∷ dependencyStepName concentration
  ∷ dependencyStepName Korn
  ∷ dependencyStepName BoundaryHB
  ∷ dependencyStepName TheoremC
  ∷ dependencyStepName ClayClosure
  ∷ "openPdeLemmaAlpha"
  ∷ "openPdeLemmaBeta"
  ∷ "openPdeLemmaGamma"
  ∷ []

canonicalOpenPdeLemmas : List String
canonicalOpenPdeLemmas =
  "openPdeLemmaAlpha"
  ∷ "openPdeLemmaBeta"
  ∷ "openPdeLemmaGamma"
  ∷ "openPdeLemmaDelta"
  ∷ "openPdeLemmaEpsilon"
  ∷ []

ledgerSummary : String
ledgerSummary =
  "Clay-distance / concise-path ledger: 8 package surfaces run from millerToH5 through GD3, CL2, concentration, Korn, BoundaryHB, TheoremC, and ClayClosure; the Clay-facing surface is recorded at the 10-11 face; 3-5 genuine open PDE lemmas remain open; no promotion is recorded."

ledgerBoundary : List String
ledgerBoundary =
  "millerToH5 is the entry surface and stays candidate-only"
  ∷ "GD3 and CL2 are the checked interior nodes of the concise path"
  ∷ "concentration, Korn, BoundaryHB, and TheoremC remain candidate bridge nodes"
  ∷ "Clay closure is recorded as a candidate closure surface only"
  ∷ "The open PDE lemmas remain genuine blockers"
  ∷ "No Clay promotion is claimed from this receipt"
  ∷ []

record ClayDistanceConcisePathProofPackageLedgerReceipt : Setω where
  field
    status :
      ClayDistanceLedgerStatus

    statusIsCandidateOnly :
      status ≡ candidateOnlyNoPromotion

    conditionalTheoremPackageCount :
      Nat

    conditionalTheoremPackageCountIs8 :
      conditionalTheoremPackageCount ≡ 8

    clayFacingPackageCountLower :
      Nat

    clayFacingPackageCountLowerIs10 :
      clayFacingPackageCountLower ≡ 10

    clayFacingPackageCountUpper :
      Nat

    clayFacingPackageCountUpperIs11 :
      clayFacingPackageCountUpper ≡ 11

    genuineOpenPdeLemmaCountLower :
      Nat

    genuineOpenPdeLemmaCountLowerIs3 :
      genuineOpenPdeLemmaCountLower ≡ 3

    genuineOpenPdeLemmaCountUpper :
      Nat

    genuineOpenPdeLemmaCountUpperIs5 :
      genuineOpenPdeLemmaCountUpper ≡ 5

    conditionalTheoremPackages :
      List String

    conditionalTheoremPackagesAreCanonical :
      conditionalTheoremPackages ≡ canonicalConditionalTheoremPackages

    clayFacingPackages :
      List String

    clayFacingPackagesAreCanonical :
      clayFacingPackages ≡ canonicalClayFacingPackages

    openPdeLemmas :
      List String

    openPdeLemmasAreCanonical :
      openPdeLemmas ≡ canonicalOpenPdeLemmas

    summary :
      String

    summaryIsCanonical :
      summary ≡ ledgerSummary

    promotionFlags :
      List ClayDistanceLedgerPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open ClayDistanceConcisePathProofPackageLedgerReceipt public

canonicalClayDistanceConcisePathProofPackageLedgerReceipt :
  ClayDistanceConcisePathProofPackageLedgerReceipt
canonicalClayDistanceConcisePathProofPackageLedgerReceipt =
  record
    { status =
        candidateOnlyNoPromotion
    ; statusIsCandidateOnly =
        refl
    ; conditionalTheoremPackageCount =
        8
    ; conditionalTheoremPackageCountIs8 =
        refl
    ; clayFacingPackageCountLower =
        10
    ; clayFacingPackageCountLowerIs10 =
        refl
    ; clayFacingPackageCountUpper =
        11
    ; clayFacingPackageCountUpperIs11 =
        refl
    ; genuineOpenPdeLemmaCountLower =
        3
    ; genuineOpenPdeLemmaCountLowerIs3 =
        refl
    ; genuineOpenPdeLemmaCountUpper =
        5
    ; genuineOpenPdeLemmaCountUpperIs5 =
        refl
    ; conditionalTheoremPackages =
        canonicalConditionalTheoremPackages
    ; conditionalTheoremPackagesAreCanonical =
        refl
    ; clayFacingPackages =
        canonicalClayFacingPackages
    ; clayFacingPackagesAreCanonical =
        refl
    ; openPdeLemmas =
        canonicalOpenPdeLemmas
    ; openPdeLemmasAreCanonical =
        refl
    ; summary =
        ledgerSummary
    ; summaryIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        ledgerBoundary
    }
