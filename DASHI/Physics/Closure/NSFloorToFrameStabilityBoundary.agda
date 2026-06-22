module DASHI.Physics.Closure.NSFloorToFrameStabilityBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- NS floor-to-frame stability boundary.
--
-- This module is a fail-closed receipt for the active NS triad route that
-- separates a scalar cocycle frustration floor from the stronger frame-gap
-- target K_N < 1.  The floor alone does not imply the frame gap.  The extra
-- stratum-distributed curvature requirement is isolated explicitly, the target
-- theorem chain is exposed as canonical ledger data, and all promotions stay
-- false.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data NSFloorToFrameStabilityBoundaryRowKey : Set where
  scalarCocycleFrustrationFloorRecorded :
    NSFloorToFrameStabilityBoundaryRowKey
  floorAloneDoesNotImplyFrameGapRecorded :
    NSFloorToFrameStabilityBoundaryRowKey
  frameGapTargetKLessThanOneRecorded :
    NSFloorToFrameStabilityBoundaryRowKey
  additionalStratumDistributedCurvatureRequirementRecorded :
    NSFloorToFrameStabilityBoundaryRowKey
  theoremChainSurfaceExposedRecorded :
    NSFloorToFrameStabilityBoundaryRowKey
  failClosedPromotionWallRecorded :
    NSFloorToFrameStabilityBoundaryRowKey

rowStatement :
  NSFloorToFrameStabilityBoundaryRowKey → String
rowStatement scalarCocycleFrustrationFloorRecorded =
  "Target: record the scalar cocycle frustration floor as a diagnostic input only."
rowStatement floorAloneDoesNotImplyFrameGapRecorded =
  "Target: state that the scalar floor alone does not imply a K_N < 1 frame gap."
rowStatement frameGapTargetKLessThanOneRecorded =
  "Target: keep the K_N < 1 frame-gap objective visible as an open boundary."
rowStatement additionalStratumDistributedCurvatureRequirementRecorded =
  "Target: isolate the additional stratum-distributed curvature requirement."
rowStatement theoremChainSurfaceExposedRecorded =
  "Target: expose the theorem chain from floor to frame gap to curvature to stability."
rowStatement failClosedPromotionWallRecorded =
  "Target: keep theorem, full-NS, and Clay promotion walls closed."

record NSFloorToFrameStabilityBoundaryRow : Set where
  field
    key :
      NSFloorToFrameStabilityBoundaryRowKey
    statement :
      String
    statementIsCanonical :
      statement ≡ rowStatement key

canonicalNSFloorToFrameStabilityBoundaryRows :
  List NSFloorToFrameStabilityBoundaryRow
canonicalNSFloorToFrameStabilityBoundaryRows =
  record
    { key =
        scalarCocycleFrustrationFloorRecorded
    ; statement =
        rowStatement scalarCocycleFrustrationFloorRecorded
    ; statementIsCanonical =
        refl
    }
  ∷ record
    { key =
        floorAloneDoesNotImplyFrameGapRecorded
    ; statement =
        rowStatement floorAloneDoesNotImplyFrameGapRecorded
    ; statementIsCanonical =
        refl
    }
  ∷ record
    { key =
        frameGapTargetKLessThanOneRecorded
    ; statement =
        rowStatement frameGapTargetKLessThanOneRecorded
    ; statementIsCanonical =
        refl
    }
  ∷ record
    { key =
        additionalStratumDistributedCurvatureRequirementRecorded
    ; statement =
        rowStatement additionalStratumDistributedCurvatureRequirementRecorded
    ; statementIsCanonical =
        refl
    }
  ∷ record
    { key =
        theoremChainSurfaceExposedRecorded
    ; statement =
        rowStatement theoremChainSurfaceExposedRecorded
    ; statementIsCanonical =
        refl
    }
  ∷ record
    { key =
        failClosedPromotionWallRecorded
    ; statement =
        rowStatement failClosedPromotionWallRecorded
    ; statementIsCanonical =
        refl
    }
  ∷ []

nSFloorToFrameStabilityBoundaryRowCount : Nat
nSFloorToFrameStabilityBoundaryRowCount =
  listLength canonicalNSFloorToFrameStabilityBoundaryRows

nSFloorToFrameStabilityBoundaryRowCountIs6 :
  nSFloorToFrameStabilityBoundaryRowCount ≡ 6
nSFloorToFrameStabilityBoundaryRowCountIs6 =
  refl

data NSFloorToFrameStabilityTheoremChainStep : Set where
  scalarCocycleFrustrationFloorStep :
    NSFloorToFrameStabilityTheoremChainStep
  frameGapTargetStep :
    NSFloorToFrameStabilityTheoremChainStep
  stratumDistributedCurvatureStep :
    NSFloorToFrameStabilityTheoremChainStep
  targetStabilityTheoremStep :
    NSFloorToFrameStabilityTheoremChainStep
  failClosedPromotionGateStep :
    NSFloorToFrameStabilityTheoremChainStep

theoremChainStatement :
  NSFloorToFrameStabilityTheoremChainStep → String
theoremChainStatement scalarCocycleFrustrationFloorStep =
  "Chain step: begin with the scalar cocycle frustration floor ledger."
theoremChainStatement frameGapTargetStep =
  "Chain step: carry the open K_N < 1 frame-gap target forward."
theoremChainStatement stratumDistributedCurvatureStep =
  "Chain step: add the extra stratum-distributed curvature requirement."
theoremChainStatement targetStabilityTheoremStep =
  "Chain step: expose the stability theorem target only as a target."
theoremChainStatement failClosedPromotionGateStep =
  "Chain step: keep theorem, full-NS, and Clay promotion gates closed."

record NSFloorToFrameStabilityTheoremChainRow : Set where
  field
    step :
      NSFloorToFrameStabilityTheoremChainStep
    statement :
      String
    statementIsCanonical :
      statement ≡ theoremChainStatement step

canonicalNSFloorToFrameStabilityTheoremChainRows :
  List NSFloorToFrameStabilityTheoremChainRow
canonicalNSFloorToFrameStabilityTheoremChainRows =
  record
    { step =
        scalarCocycleFrustrationFloorStep
    ; statement =
        theoremChainStatement scalarCocycleFrustrationFloorStep
    ; statementIsCanonical =
        refl
    }
  ∷ record
    { step =
        frameGapTargetStep
    ; statement =
        theoremChainStatement frameGapTargetStep
    ; statementIsCanonical =
        refl
    }
  ∷ record
    { step =
        stratumDistributedCurvatureStep
    ; statement =
        theoremChainStatement stratumDistributedCurvatureStep
    ; statementIsCanonical =
        refl
    }
  ∷ record
    { step =
        targetStabilityTheoremStep
    ; statement =
        theoremChainStatement targetStabilityTheoremStep
    ; statementIsCanonical =
        refl
    }
  ∷ record
    { step =
        failClosedPromotionGateStep
    ; statement =
        theoremChainStatement failClosedPromotionGateStep
    ; statementIsCanonical =
        refl
    }
  ∷ []

nSFloorToFrameStabilityTheoremChainRowCount : Nat
nSFloorToFrameStabilityTheoremChainRowCount =
  listLength canonicalNSFloorToFrameStabilityTheoremChainRows

nSFloorToFrameStabilityTheoremChainRowCountIs5 :
  nSFloorToFrameStabilityTheoremChainRowCount ≡ 5
nSFloorToFrameStabilityTheoremChainRowCountIs5 =
  refl

data NSFloorToFrameStabilityBoundaryGap : Set where
  scalarFloorDoesNotForceFrameGap :
    NSFloorToFrameStabilityBoundaryGap
  additionalCurvatureRequirementUnproved :
    NSFloorToFrameStabilityBoundaryGap
  frameGapTargetStillOpen :
    NSFloorToFrameStabilityBoundaryGap
  theoremChainClosureStillOpen :
    NSFloorToFrameStabilityBoundaryGap
  theoremFullNSClayPromotionClosed :
    NSFloorToFrameStabilityBoundaryGap

canonicalNSFloorToFrameStabilityBoundaryGaps :
  List NSFloorToFrameStabilityBoundaryGap
canonicalNSFloorToFrameStabilityBoundaryGaps =
  scalarFloorDoesNotForceFrameGap
  ∷ additionalCurvatureRequirementUnproved
  ∷ frameGapTargetStillOpen
  ∷ theoremChainClosureStillOpen
  ∷ theoremFullNSClayPromotionClosed
  ∷ []

nSFloorToFrameStabilityBoundaryGapCount : Nat
nSFloorToFrameStabilityBoundaryGapCount =
  listLength canonicalNSFloorToFrameStabilityBoundaryGaps

nSFloorToFrameStabilityBoundaryGapCountIs5 :
  nSFloorToFrameStabilityBoundaryGapCount ≡ 5
nSFloorToFrameStabilityBoundaryGapCountIs5 =
  refl

canonicalWitnessTerm : String
canonicalWitnessTerm =
  "candidate-only receipt: the scalar cocycle frustration floor is recorded, but it does not imply K_N < 1; the extra stratum-distributed curvature requirement remains open."

organizationString : String
organizationString =
  "O: record the active NS triad floor-to-frame stability boundary as a fail-closed receipt."

requirementString : String
requirementString =
  "R: record that a scalar cocycle frustration floor alone does not imply a K_N < 1 frame gap, and isolate the extra stratum-distributed curvature requirement."

codeArtifactString : String
codeArtifactString =
  "C: export canonical rows, theorem-chain rows, gaps, and a compact ORCSLPGF surface with explicit false promotion gates."

stateString : String
stateString =
  "S: the floor is recorded, the frame gap remains open, the extra curvature layer is isolated, and theorem/full-NS/Clay promotions stay false."

latticeString : String
latticeString =
  "L: scalar cocycle frustration floor -> open K_N < 1 frame gap -> stratum-distributed curvature requirement -> target theorem chain -> fail-closed boundary."

proposalString : String
proposalString =
  "P: keep the floor as a diagnostic input only and promote nothing until the curvature layer is genuinely discharged."

governanceString : String
governanceString =
  "G: theorem, full-NS, and Clay promotion remain false throughout this boundary."

failString : String
failString =
  "F: the missing evidence is the stratum-distributed curvature control that would bridge the floor to the frame gap."

record NSFloorToFrameStabilityBoundaryORCSLPGF : Set where
  constructor mkNSFloorToFrameStabilityBoundaryORCSLPGF
  field
    O : String
    OIsCanonical : O ≡ organizationString
    R : String
    RIsCanonical : R ≡ requirementString
    C : String
    CIsCanonical : C ≡ codeArtifactString
    S : String
    SIsCanonical : S ≡ stateString
    L : String
    LIsCanonical : L ≡ latticeString
    P : String
    PIsCanonical : P ≡ proposalString
    G : String
    GIsCanonical : G ≡ governanceString
    F : String
    FIsCanonical : F ≡ failString

open NSFloorToFrameStabilityBoundaryORCSLPGF public

canonicalNSFloorToFrameStabilityBoundaryORCSLPGF :
  NSFloorToFrameStabilityBoundaryORCSLPGF
canonicalNSFloorToFrameStabilityBoundaryORCSLPGF =
  mkNSFloorToFrameStabilityBoundaryORCSLPGF
    organizationString
    refl
    requirementString
    refl
    codeArtifactString
    refl
    stateString
    refl
    latticeString
    refl
    proposalString
    refl
    governanceString
    refl
    failString
    refl

record NSFloorToFrameStabilityBoundary : Setω where
  constructor mkNSFloorToFrameStabilityBoundary
  field
    receiptName :
      String
    receiptNameIsCanonical :
      receiptName ≡ "NSFloorToFrameStabilityBoundary"

    witnessTerm :
      String
    witnessTermIsCanonical :
      witnessTerm ≡ canonicalWitnessTerm

    candidateOnly :
      Bool
    candidateOnlyIsTrue :
      candidateOnly ≡ true

    failClosed :
      Bool
    failClosedIsTrue :
      failClosed ≡ true

    scalarCocycleFrustrationFloorFlag :
      Bool
    scalarCocycleFrustrationFloorFlagIsTrue :
      scalarCocycleFrustrationFloorFlag ≡ true

    floorAloneImpliesFrameGap :
      Bool
    floorAloneImpliesFrameGapIsFalse :
      floorAloneImpliesFrameGap ≡ false

    frameGapTargetRecorded :
      Bool
    frameGapTargetRecordedIsTrue :
      frameGapTargetRecorded ≡ true

    additionalStratumDistributedCurvatureRequirementFlag :
      Bool
    additionalStratumDistributedCurvatureRequirementFlagIsTrue :
      additionalStratumDistributedCurvatureRequirementFlag ≡ true

    additionalStratumDistributedCurvatureRequirementDischarged :
      Bool
    additionalStratumDistributedCurvatureRequirementDischargedIsFalse :
      additionalStratumDistributedCurvatureRequirementDischarged ≡ false

    targetTheoremChainExposed :
      Bool
    targetTheoremChainExposedIsTrue :
      targetTheoremChainExposed ≡ true

    theoremPromoted :
      Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    fullNSPromoted :
      Bool
    fullNSPromotedIsFalse :
      fullNSPromoted ≡ false

    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

    orcslpgf :
      NSFloorToFrameStabilityBoundaryORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSFloorToFrameStabilityBoundaryORCSLPGF

    rows :
      List NSFloorToFrameStabilityBoundaryRow
    rowsAreCanonical :
      rows ≡ canonicalNSFloorToFrameStabilityBoundaryRows
    rowCount :
      Nat
    rowCountIsCanonical :
      rowCount ≡ nSFloorToFrameStabilityBoundaryRowCount

    theoremChainRows :
      List NSFloorToFrameStabilityTheoremChainRow
    theoremChainRowsAreCanonical :
      theoremChainRows ≡ canonicalNSFloorToFrameStabilityTheoremChainRows
    theoremChainRowCount :
      Nat
    theoremChainRowCountIsCanonical :
      theoremChainRowCount ≡ nSFloorToFrameStabilityTheoremChainRowCount

    gaps :
      List NSFloorToFrameStabilityBoundaryGap
    gapsAreCanonical :
      gaps ≡ canonicalNSFloorToFrameStabilityBoundaryGaps
    gapCount :
      Nat
    gapCountIsCanonical :
      gapCount ≡ nSFloorToFrameStabilityBoundaryGapCount

    statement :
      String
    statementIsCanonical :
      statement ≡
      "Candidate-only floor-to-frame stability boundary: the scalar cocycle frustration floor is recorded, but it does not imply K_N < 1; the extra stratum-distributed curvature requirement remains open and theorem/full-NS/Clay flags stay false."

open NSFloorToFrameStabilityBoundary public

canonicalNSFloorToFrameStabilityBoundary :
  NSFloorToFrameStabilityBoundary
canonicalNSFloorToFrameStabilityBoundary =
  mkNSFloorToFrameStabilityBoundary
    "NSFloorToFrameStabilityBoundary"
    refl
    canonicalWitnessTerm
    refl
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    true
    refl
    true
    refl
    false
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    canonicalNSFloorToFrameStabilityBoundaryORCSLPGF
    refl
    canonicalNSFloorToFrameStabilityBoundaryRows
    refl
    nSFloorToFrameStabilityBoundaryRowCount
    refl
    canonicalNSFloorToFrameStabilityTheoremChainRows
    refl
    nSFloorToFrameStabilityTheoremChainRowCount
    refl
    canonicalNSFloorToFrameStabilityBoundaryGaps
    refl
    nSFloorToFrameStabilityBoundaryGapCount
    refl
    "Candidate-only floor-to-frame stability boundary: the scalar cocycle frustration floor is recorded, but it does not imply K_N < 1; the extra stratum-distributed curvature requirement remains open and theorem/full-NS/Clay flags stay false."
    refl

scalarFloorDoesNotImplyFrameGap :
  floorAloneImpliesFrameGap canonicalNSFloorToFrameStabilityBoundary ≡ false
scalarFloorDoesNotImplyFrameGap =
  refl

additionalCurvatureRequirementStillOpen :
  additionalStratumDistributedCurvatureRequirementDischarged canonicalNSFloorToFrameStabilityBoundary
  ≡ false
additionalCurvatureRequirementStillOpen =
  refl

allPromotionsFalse :
  theoremPromoted canonicalNSFloorToFrameStabilityBoundary ≡ false
allPromotionsFalse =
  refl
