module DASHI.Physics.Closure.UnificationScaleInvariantCrossTermHypothesisBoundary where

-- Fail-closed boundary for the corrected U-1a-H premise:
--
--   G(s1+s2) - G(s1) - G(s2) = 2 B(s1,s2)
--
-- with B an explicit symmetric bilinear form.  This module records that
-- precondition so downstream four-point, parallelogram, Jordan-von Neumann,
-- quadratic, Clifford, and spinor consumers cannot silently rely on
-- 2-homogeneity alone.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Local utility.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Explicit U-1a-H socket.

record ScaleInvariantCrossTermSurface : Setω where
  field
    Carrier :
      Set

    Value :
      Set

    _+s_ :
      Carrier → Carrier → Carrier

    G :
      Carrier → Value

    B :
      Carrier → Carrier → Value

    _+v_ :
      Value → Value → Value

    -v_ :
      Value → Value

    twice :
      Value → Value

open ScaleInvariantCrossTermSurface public

crossTerm :
  (surface : ScaleInvariantCrossTermSurface) →
  Carrier surface →
  Carrier surface →
  Value surface
crossTerm surface s1 s2 =
  _+v_ surface
    (_+v_ surface
      (G surface (_+s_ surface s1 s2))
      (-v_ surface (G surface s1)))
    (-v_ surface (G surface s2))

record ScaleInvariantCrossTermHypothesis
  (surface : ScaleInvariantCrossTermSurface) : Setω where
  field
    symmetric :
      (s1 s2 : Carrier surface) →
      B surface s1 s2 ≡ B surface s2 s1

    bilinearLeftAdditive :
      (s1 s2 s3 : Carrier surface) →
      B surface (_+s_ surface s1 s2) s3
      ≡ _+v_ surface
          (B surface s1 s3)
          (B surface s2 s3)

    bilinearRightAdditive :
      (s1 s2 s3 : Carrier surface) →
      B surface s1 (_+s_ surface s2 s3)
      ≡ _+v_ surface
          (B surface s1 s2)
          (B surface s1 s3)

    decompositionTarget :
      (s1 s2 : Carrier surface) →
      crossTerm surface s1 s2
      ≡ twice surface (B surface s1 s2)

    decompositionText :
      String

    decompositionTextIsCanonical :
      decompositionText
      ≡ "G(s1+s2)-G(s1)-G(s2)=2B(s1,s2) with symmetric bilinear B"

    hypothesisLabel :
      String

    hypothesisLabelIsCanonical :
      hypothesisLabel ≡ "Hypothesis U-1a-H"

open ScaleInvariantCrossTermHypothesis public

------------------------------------------------------------------------
-- Recorded clauses, stages, blockers.

data U1aHClause : Set where
  correctedCounterexampleRecorded :
    U1aHClause
  crossTermDecompositionRecorded :
    U1aHClause
  symmetricBilinearWitnessRecorded :
    U1aHClause
  fourPointConsumerRecorded :
    U1aHClause
  parallelogramConsumerRecorded :
    U1aHClause
  jordanVonNeumannConsumerRecorded :
    U1aHClause
  quadraticConsumerRecorded :
    U1aHClause
  cliffordConsumerRecorded :
    U1aHClause
  spinorConsumerRecorded :
    U1aHClause

canonicalU1aHClauses : List U1aHClause
canonicalU1aHClauses =
  correctedCounterexampleRecorded
  ∷ crossTermDecompositionRecorded
  ∷ symmetricBilinearWitnessRecorded
  ∷ fourPointConsumerRecorded
  ∷ parallelogramConsumerRecorded
  ∷ jordanVonNeumannConsumerRecorded
  ∷ quadraticConsumerRecorded
  ∷ cliffordConsumerRecorded
  ∷ spinorConsumerRecorded
  ∷ []

u1aHClauseCount : Nat
u1aHClauseCount =
  listLength canonicalU1aHClauses

u1aHClauseCountIs9 : u1aHClauseCount ≡ 9
u1aHClauseCountIs9 =
  refl

data U1aHStage : Set where
  rejectTwoHomogeneityAlone :
    U1aHStage
  exposeCrossTermDecomposition :
    U1aHStage
  exposeSymmetricBilinearWitness :
    U1aHStage
  handoffToFourPoint :
    U1aHStage
  handoffToParallelogram :
    U1aHStage
  handoffToJordanVonNeumann :
    U1aHStage
  handoffToQuadratic :
    U1aHStage
  handoffToClifford :
    U1aHStage
  handoffToSpinor :
    U1aHStage
  promotionGate :
    U1aHStage

canonicalU1aHStages : List U1aHStage
canonicalU1aHStages =
  rejectTwoHomogeneityAlone
  ∷ exposeCrossTermDecomposition
  ∷ exposeSymmetricBilinearWitness
  ∷ handoffToFourPoint
  ∷ handoffToParallelogram
  ∷ handoffToJordanVonNeumann
  ∷ handoffToQuadratic
  ∷ handoffToClifford
  ∷ handoffToSpinor
  ∷ promotionGate
  ∷ []

u1aHStageCount : Nat
u1aHStageCount =
  listLength canonicalU1aHStages

u1aHStageCountIs10 : u1aHStageCount ≡ 10
u1aHStageCountIs10 =
  refl

data U1aHBlocker : Set where
  blocker-two-homogeneity-alone-insufficient :
    U1aHBlocker
  blocker-cross-term-decomposition-unproved :
    U1aHBlocker
  blocker-bilinearity-unproved :
    U1aHBlocker
  blocker-symmetry-unproved :
    U1aHBlocker
  blocker-four-point-unproved :
    U1aHBlocker
  blocker-parallelogram-unproved :
    U1aHBlocker
  blocker-jordan-von-neumann-unproved :
    U1aHBlocker
  blocker-clifford-unproved :
    U1aHBlocker
  blocker-spinor-unproved :
    U1aHBlocker
  blocker-terminal-promotion-forbidden :
    U1aHBlocker

canonicalU1aHBlockers : List U1aHBlocker
canonicalU1aHBlockers =
  blocker-two-homogeneity-alone-insufficient
  ∷ blocker-cross-term-decomposition-unproved
  ∷ blocker-bilinearity-unproved
  ∷ blocker-symmetry-unproved
  ∷ blocker-four-point-unproved
  ∷ blocker-parallelogram-unproved
  ∷ blocker-jordan-von-neumann-unproved
  ∷ blocker-clifford-unproved
  ∷ blocker-spinor-unproved
  ∷ blocker-terminal-promotion-forbidden
  ∷ []

u1aHBlockerCount : Nat
u1aHBlockerCount =
  listLength canonicalU1aHBlockers

u1aHBlockerCountIs10 : u1aHBlockerCount ≡ 10
u1aHBlockerCountIs10 =
  refl

------------------------------------------------------------------------
-- Canonical text.

correctiveStatement : String
correctiveStatement =
  "2-homogeneity alone does not imply cross-term nullity or quadraticity"

correctiveStatementIsCanonical :
  correctiveStatement
  ≡ "2-homogeneity alone does not imply cross-term nullity or quadraticity"
correctiveStatementIsCanonical =
  refl

scaleInvariantCrossTermText : String
scaleInvariantCrossTermText =
  "G(s1+s2)-G(s1)-G(s2)=2B(s1,s2)"

scaleInvariantCrossTermTextIsCanonical :
  scaleInvariantCrossTermText
  ≡ "G(s1+s2)-G(s1)-G(s2)=2B(s1,s2)"
scaleInvariantCrossTermTextIsCanonical =
  refl

------------------------------------------------------------------------
-- Fail-closed governance flags.

scaleInvariantCrossTermHypothesisRecorded : Bool
scaleInvariantCrossTermHypothesisRecorded =
  true

scaleInvariantCrossTermHypothesisRecordedIsTrue :
  scaleInvariantCrossTermHypothesisRecorded ≡ true
scaleInvariantCrossTermHypothesisRecordedIsTrue =
  refl

twoHomogeneityAloneAccepted : Bool
twoHomogeneityAloneAccepted =
  false

twoHomogeneityAloneAcceptedIsFalse :
  twoHomogeneityAloneAccepted ≡ false
twoHomogeneityAloneAcceptedIsFalse =
  refl

scaleInvariantCrossTermDecompositionProved : Bool
scaleInvariantCrossTermDecompositionProved =
  false

scaleInvariantCrossTermDecompositionProvedIsFalse :
  scaleInvariantCrossTermDecompositionProved ≡ false
scaleInvariantCrossTermDecompositionProvedIsFalse =
  refl

symmetricBilinearityProved : Bool
symmetricBilinearityProved =
  false

symmetricBilinearityProvedIsFalse :
  symmetricBilinearityProved ≡ false
symmetricBilinearityProvedIsFalse =
  refl

fourPointCancellationProved : Bool
fourPointCancellationProved =
  false

fourPointCancellationProvedIsFalse :
  fourPointCancellationProved ≡ false
fourPointCancellationProvedIsFalse =
  refl

parallelogramLawProved : Bool
parallelogramLawProved =
  false

parallelogramLawProvedIsFalse :
  parallelogramLawProved ≡ false
parallelogramLawProvedIsFalse =
  refl

jordanVonNeumannAdapterProved : Bool
jordanVonNeumannAdapterProved =
  false

jordanVonNeumannAdapterProvedIsFalse :
  jordanVonNeumannAdapterProved ≡ false
jordanVonNeumannAdapterProvedIsFalse =
  refl

quadraticConsumerProved : Bool
quadraticConsumerProved =
  false

quadraticConsumerProvedIsFalse :
  quadraticConsumerProved ≡ false
quadraticConsumerProvedIsFalse =
  refl

cliffordConsumerProved : Bool
cliffordConsumerProved =
  false

cliffordConsumerProvedIsFalse :
  cliffordConsumerProved ≡ false
cliffordConsumerProvedIsFalse =
  refl

spinorConsumerProved : Bool
spinorConsumerProved =
  false

spinorConsumerProvedIsFalse :
  spinorConsumerProved ≡ false
spinorConsumerProvedIsFalse =
  refl

promotion : Bool
promotion =
  false

promotionIsFalse : promotion ≡ false
promotionIsFalse =
  refl

------------------------------------------------------------------------
-- Canonical boundary surface.

record UnificationScaleInvariantCrossTermHypothesisBoundary : Set where
  field
    clauseCount :
      Nat

    stageCount :
      Nat

    blockerCount :
      Nat

    hypothesisRecorded :
      Bool

    twoHomogeneityRejected :
      Bool

    decompositionDerived :
      Bool

    bilinearityDerived :
      Bool

    fourPointDerived :
      Bool

    parallelogramDerived :
      Bool

    jordanVonNeumannDerived :
      Bool

    quadraticDerived :
      Bool

    cliffordDerived :
      Bool

    spinorDerived :
      Bool

    promotionFlag :
      Bool

open UnificationScaleInvariantCrossTermHypothesisBoundary public

canonicalUnificationScaleInvariantCrossTermHypothesisBoundary :
  UnificationScaleInvariantCrossTermHypothesisBoundary
canonicalUnificationScaleInvariantCrossTermHypothesisBoundary =
  record
    { clauseCount =
        u1aHClauseCount
    ; stageCount =
        u1aHStageCount
    ; blockerCount =
        u1aHBlockerCount
    ; hypothesisRecorded =
        scaleInvariantCrossTermHypothesisRecorded
    ; twoHomogeneityRejected =
        twoHomogeneityAloneAccepted
    ; decompositionDerived =
        scaleInvariantCrossTermDecompositionProved
    ; bilinearityDerived =
        symmetricBilinearityProved
    ; fourPointDerived =
        fourPointCancellationProved
    ; parallelogramDerived =
        parallelogramLawProved
    ; jordanVonNeumannDerived =
        jordanVonNeumannAdapterProved
    ; quadraticDerived =
        quadraticConsumerProved
    ; cliffordDerived =
        cliffordConsumerProved
    ; spinorDerived =
        spinorConsumerProved
    ; promotionFlag =
        promotion
    }

canonicalScaleInvariantCrossTermHypothesisRecorded :
  hypothesisRecorded
    canonicalUnificationScaleInvariantCrossTermHypothesisBoundary
  ≡ true
canonicalScaleInvariantCrossTermHypothesisRecorded =
  refl

canonicalTwoHomogeneityRejected :
  twoHomogeneityRejected
    canonicalUnificationScaleInvariantCrossTermHypothesisBoundary
  ≡ false
canonicalTwoHomogeneityRejected =
  refl

canonicalScaleInvariantCrossTermDecompositionStillOpen :
  decompositionDerived
    canonicalUnificationScaleInvariantCrossTermHypothesisBoundary
  ≡ false
canonicalScaleInvariantCrossTermDecompositionStillOpen =
  refl

canonicalSymmetricBilinearityStillOpen :
  bilinearityDerived
    canonicalUnificationScaleInvariantCrossTermHypothesisBoundary
  ≡ false
canonicalSymmetricBilinearityStillOpen =
  refl

canonicalU1aHFourPointStillOpen :
  fourPointDerived
    canonicalUnificationScaleInvariantCrossTermHypothesisBoundary
  ≡ false
canonicalU1aHFourPointStillOpen =
  refl

canonicalU1aHParallelogramStillOpen :
  parallelogramDerived
    canonicalUnificationScaleInvariantCrossTermHypothesisBoundary
  ≡ false
canonicalU1aHParallelogramStillOpen =
  refl

canonicalU1aHJordanVonNeumannStillOpen :
  jordanVonNeumannDerived
    canonicalUnificationScaleInvariantCrossTermHypothesisBoundary
  ≡ false
canonicalU1aHJordanVonNeumannStillOpen =
  refl

canonicalU1aHQuadraticStillOpen :
  quadraticDerived
    canonicalUnificationScaleInvariantCrossTermHypothesisBoundary
  ≡ false
canonicalU1aHQuadraticStillOpen =
  refl

canonicalU1aHCliffordStillOpen :
  cliffordDerived
    canonicalUnificationScaleInvariantCrossTermHypothesisBoundary
  ≡ false
canonicalU1aHCliffordStillOpen =
  refl

canonicalU1aHSpinorStillOpen :
  spinorDerived
    canonicalUnificationScaleInvariantCrossTermHypothesisBoundary
  ≡ false
canonicalU1aHSpinorStillOpen =
  refl

canonicalU1aHPromotionFalse :
  promotionFlag
    canonicalUnificationScaleInvariantCrossTermHypothesisBoundary
  ≡ false
canonicalU1aHPromotionFalse =
  refl
