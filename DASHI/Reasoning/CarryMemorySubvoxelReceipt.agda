module DASHI.Reasoning.CarryMemorySubvoxelReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Carry memory / subvoxel receipt.
--
-- This receipt records the narrow arithmetic-discourse invariant:
--
--   +1_k + +1_k = -1_k with a +1 carry at depth k+1.
--
-- Looking only at depth k sees apparent reversal.  Keeping the carry records
-- the synthesis/elevation at k+1.  The lower-level -1_k residue is not
-- discarded; it is kept as memory/subvoxel history of the crisis point.
--
-- This is a reasoning/codec bookkeeping receipt.  It is not psychology,
-- sociology, ethics, continuum physics, or a terminal theorem.

data CarryMemoryStatus : Set where
  carryMemorySubvoxelRecorded :
    CarryMemoryStatus

data BalancedTernaryLocalSum : Set where
  plusOnePlusPlusOneReadsNegativeLocally :
    BalancedTernaryLocalSum

data CarryAtNextDepth : Set where
  plusOneCarryAtKPlusOne :
    CarryAtNextDepth

data CarryReading : Set where
  dropCarryPerceivedRegression :
    CarryReading

  keepCarryDialecticalElevation :
    CarryReading

data SubvoxelMemoryStatus : Set where
  lowerResiduePersistsAsMemory :
    SubvoxelMemoryStatus

data DepthEvaluationBoundary : Set where
  evaluateJAndJPlusOneTogether :
    DepthEvaluationBoundary

data CarryMemoryOpenObligation : Set where
  proveRuntimeCarryPersistenceForConcreteCodec :
    CarryMemoryOpenObligation

  connectSubvoxelMemoryToObserverModel :
    CarryMemoryOpenObligation

  proveAnyClaimedPsychologicalReadingSeparately :
    CarryMemoryOpenObligation

canonicalCarryMemoryOpenObligations :
  List CarryMemoryOpenObligation
canonicalCarryMemoryOpenObligations =
  proveRuntimeCarryPersistenceForConcreteCodec
  ∷ connectSubvoxelMemoryToObserverModel
  ∷ proveAnyClaimedPsychologicalReadingSeparately
  ∷ []

data CarryMemoryNonClaim : Set where
  noPsychologyTheorem :
    CarryMemoryNonClaim

  noSociologyTheorem :
    CarryMemoryNonClaim

  noEthicalTheorem :
    CarryMemoryNonClaim

  noRuntimeCodecTheorem :
    CarryMemoryNonClaim

  noContinuumPhysicsClaim :
    CarryMemoryNonClaim

  noTerminalPromotion :
    CarryMemoryNonClaim

canonicalCarryMemoryNonClaims :
  List CarryMemoryNonClaim
canonicalCarryMemoryNonClaims =
  noPsychologyTheorem
  ∷ noSociologyTheorem
  ∷ noEthicalTheorem
  ∷ noRuntimeCodecTheorem
  ∷ noContinuumPhysicsClaim
  ∷ noTerminalPromotion
  ∷ []

data CarryMemoryPromotion : Set where

carryMemoryPromotionImpossibleHere :
  CarryMemoryPromotion →
  ⊥
carryMemoryPromotionImpossibleHere ()

localDepth :
  Nat
localDepth =
  3

friendshipDepth :
  Nat
friendshipDepth =
  6

dialecticalDepth :
  Nat
dialecticalDepth =
  9

carryLawSummary :
  String
carryLawSummary =
  "Balanced ternary carry reading: +1 at depth k plus +1 at depth k reads -1 locally and carries +1 to depth k+1."

memorySummary :
  String
memorySummary =
  "The local -1 residue persists as subvoxel memory; dropping it loses the crisis history, while keeping it records synthesis."

jAndJPlusOneSummary :
  String
jAndJPlusOneSummary =
  "The safe evaluator reads depth j and depth j+1 together; j-only mod3 evaluation is the carry-dropping trap."

record CarryMemorySubvoxelReceipt : Setω where
  field
    status :
      CarryMemoryStatus

    statusIsCanonical :
      status ≡ carryMemorySubvoxelRecorded

    localSum :
      BalancedTernaryLocalSum

    localSumIsNegative :
      localSum ≡ plusOnePlusPlusOneReadsNegativeLocally

    carry :
      CarryAtNextDepth

    carryIsNextDepthPositive :
      carry ≡ plusOneCarryAtKPlusOne

    dropCarryReading :
      CarryReading

    dropCarryReadingIsRegression :
      dropCarryReading ≡ dropCarryPerceivedRegression

    keepCarryReading :
      CarryReading

    keepCarryReadingIsElevation :
      keepCarryReading ≡ keepCarryDialecticalElevation

    subvoxelMemory :
      SubvoxelMemoryStatus

    subvoxelMemoryPersists :
      subvoxelMemory ≡ lowerResiduePersistsAsMemory

    depthEvaluationBoundary :
      DepthEvaluationBoundary

    depthEvaluationBoundaryIsJAndJPlusOne :
      depthEvaluationBoundary ≡ evaluateJAndJPlusOneTogether

    localDepthRecorded :
      Nat

    localDepthRecordedIsThree :
      localDepthRecorded ≡ localDepth

    friendshipDepthRecorded :
      Nat

    friendshipDepthRecordedIsSix :
      friendshipDepthRecorded ≡ friendshipDepth

    dialecticalDepthRecorded :
      Nat

    dialecticalDepthRecordedIsNine :
      dialecticalDepthRecorded ≡ dialecticalDepth

    runtimeCarryPersistenceProved :
      Bool

    runtimeCarryPersistenceProvedIsFalse :
      runtimeCarryPersistenceProved ≡ false

    psychologyTheoremProved :
      Bool

    psychologyTheoremProvedIsFalse :
      psychologyTheoremProved ≡ false

    openObligations :
      List CarryMemoryOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalCarryMemoryOpenObligations

    nonClaims :
      List CarryMemoryNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalCarryMemoryNonClaims

    promotionFlags :
      List CarryMemoryPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    carryLawReading :
      String

    carryLawReadingIsCanonical :
      carryLawReading ≡ carryLawSummary

    memoryReading :
      String

    memoryReadingIsCanonical :
      memoryReading ≡ memorySummary

    jAndJPlusOneReading :
      String

    jAndJPlusOneReadingIsCanonical :
      jAndJPlusOneReading ≡ jAndJPlusOneSummary

    receiptBoundary :
      List String

open CarryMemorySubvoxelReceipt public

canonicalCarryMemorySubvoxelReceipt :
  CarryMemorySubvoxelReceipt
canonicalCarryMemorySubvoxelReceipt =
  record
    { status =
        carryMemorySubvoxelRecorded
    ; statusIsCanonical =
        refl
    ; localSum =
        plusOnePlusPlusOneReadsNegativeLocally
    ; localSumIsNegative =
        refl
    ; carry =
        plusOneCarryAtKPlusOne
    ; carryIsNextDepthPositive =
        refl
    ; dropCarryReading =
        dropCarryPerceivedRegression
    ; dropCarryReadingIsRegression =
        refl
    ; keepCarryReading =
        keepCarryDialecticalElevation
    ; keepCarryReadingIsElevation =
        refl
    ; subvoxelMemory =
        lowerResiduePersistsAsMemory
    ; subvoxelMemoryPersists =
        refl
    ; depthEvaluationBoundary =
        evaluateJAndJPlusOneTogether
    ; depthEvaluationBoundaryIsJAndJPlusOne =
        refl
    ; localDepthRecorded =
        localDepth
    ; localDepthRecordedIsThree =
        refl
    ; friendshipDepthRecorded =
        friendshipDepth
    ; friendshipDepthRecordedIsSix =
        refl
    ; dialecticalDepthRecorded =
        dialecticalDepth
    ; dialecticalDepthRecordedIsNine =
        refl
    ; runtimeCarryPersistenceProved =
        false
    ; runtimeCarryPersistenceProvedIsFalse =
        refl
    ; psychologyTheoremProved =
        false
    ; psychologyTheoremProvedIsFalse =
        refl
    ; openObligations =
        canonicalCarryMemoryOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; nonClaims =
        canonicalCarryMemoryNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; carryLawReading =
        carryLawSummary
    ; carryLawReadingIsCanonical =
        refl
    ; memoryReading =
        memorySummary
    ; memoryReadingIsCanonical =
        refl
    ; jAndJPlusOneReading =
        jAndJPlusOneSummary
    ; jAndJPlusOneReadingIsCanonical =
        refl
    ; receiptBoundary =
        "Records local balanced-ternary agreement as apparent -1 plus a positive carry to the next depth"
        ∷ "Records carry persistence as memory/deeper history, not discarded noise"
        ∷ "Rejects j-only mod3 evaluation as a carry-dropping trap"
        ∷ "Keeps j and j+1 evaluation as the safe synthesis-preserving reading"
        ∷ "No psychology, sociology, ethics, runtime codec, continuum physics, or terminal theorem follows"
        ∷ []
    }

canonicalCarryKeepsRuntimeOpen :
  runtimeCarryPersistenceProved canonicalCarryMemorySubvoxelReceipt ≡ false
canonicalCarryKeepsRuntimeOpen =
  refl

canonicalCarryNoPsychologyTheorem :
  psychologyTheoremProved canonicalCarryMemorySubvoxelReceipt ≡ false
canonicalCarryNoPsychologyTheorem =
  refl

canonicalCarryNoPromotion :
  promotionFlags canonicalCarryMemorySubvoxelReceipt ≡ []
canonicalCarryNoPromotion =
  refl
