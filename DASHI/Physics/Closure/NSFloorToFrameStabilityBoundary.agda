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
-- separates a quantitative cocycle lower-bound input from the stronger
-- frame-gap target K_N < 1.  The floor alone does not imply the frame gap.
-- The distributed-residual/stratum-curvature bridge is isolated explicitly,
-- the Wall 1 theorem chain is exposed as canonical ledger data, and all
-- promotions stay false.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data NSFloorToFrameStabilityBoundaryRowKey : Set where
  quantitativeCocycleLowerBoundInputRecorded :
    NSFloorToFrameStabilityBoundaryRowKey
  scalarCocycleFrustrationFloorRecorded :
    NSFloorToFrameStabilityBoundaryRowKey
  floorAloneDoesNotImplyFrameGapRecorded :
    NSFloorToFrameStabilityBoundaryRowKey
  frameGapTargetKLessThanOneRecorded :
    NSFloorToFrameStabilityBoundaryRowKey
  distributedResidualStratumCurvatureBridgeRecorded :
    NSFloorToFrameStabilityBoundaryRowKey
  theoremChainSurfaceExposedRecorded :
    NSFloorToFrameStabilityBoundaryRowKey
  failClosedPromotionWallRecorded :
    NSFloorToFrameStabilityBoundaryRowKey

rowStatement :
  NSFloorToFrameStabilityBoundaryRowKey → String
rowStatement quantitativeCocycleLowerBoundInputRecorded =
  "Target: record the quantitative cocycle lower-bound input as the Wall 1 seed."
rowStatement scalarCocycleFrustrationFloorRecorded =
  "Target: record the scalar cocycle frustration floor as a diagnostic input only."
rowStatement floorAloneDoesNotImplyFrameGapRecorded =
  "Target: state that the scalar floor alone does not imply a K_N < 1 frame gap."
rowStatement frameGapTargetKLessThanOneRecorded =
  "Target: keep the K_N < 1 frame-gap objective visible as an open boundary."
rowStatement distributedResidualStratumCurvatureBridgeRecorded =
  "Target: isolate the distributed-residual / stratum-curvature bridge."
rowStatement theoremChainSurfaceExposedRecorded =
  "Target: expose the Wall 1 theorem chain from input to floor to bridge to stability."
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
        quantitativeCocycleLowerBoundInputRecorded
    ; statement =
        rowStatement quantitativeCocycleLowerBoundInputRecorded
    ; statementIsCanonical =
        refl
    }
  ∷ record
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
        distributedResidualStratumCurvatureBridgeRecorded
    ; statement =
        rowStatement distributedResidualStratumCurvatureBridgeRecorded
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

nSFloorToFrameStabilityBoundaryRowCountIs7 :
  nSFloorToFrameStabilityBoundaryRowCount ≡ 7
nSFloorToFrameStabilityBoundaryRowCountIs7 =
  refl

data NSFloorToFrameStabilityTheoremChainStep : Set where
  quantitativeCocycleLowerBoundInputStep :
    NSFloorToFrameStabilityTheoremChainStep
  scalarCocycleFrustrationFloorStep :
    NSFloorToFrameStabilityTheoremChainStep
  frameGapTargetStep :
    NSFloorToFrameStabilityTheoremChainStep
  distributedResidualStratumCurvatureBridgeStep :
    NSFloorToFrameStabilityTheoremChainStep
  targetStabilityTheoremStep :
    NSFloorToFrameStabilityTheoremChainStep
  failClosedPromotionGateStep :
    NSFloorToFrameStabilityTheoremChainStep

theoremChainStatement :
  NSFloorToFrameStabilityTheoremChainStep → String
theoremChainStatement quantitativeCocycleLowerBoundInputStep =
  "Chain step: begin with the quantitative cocycle lower-bound input."
theoremChainStatement scalarCocycleFrustrationFloorStep =
  "Chain step: record the scalar cocycle frustration floor ledger."
theoremChainStatement frameGapTargetStep =
  "Chain step: carry the open K_N < 1 frame-gap target forward."
theoremChainStatement distributedResidualStratumCurvatureBridgeStep =
  "Chain step: add the distributed-residual / stratum-curvature bridge."
theoremChainStatement targetStabilityTheoremStep =
  "Chain step: expose the Wall 1 stability theorem target only as a target."
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
        quantitativeCocycleLowerBoundInputStep
    ; statement =
        theoremChainStatement quantitativeCocycleLowerBoundInputStep
    ; statementIsCanonical =
        refl
    }
  ∷ record
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
        distributedResidualStratumCurvatureBridgeStep
    ; statement =
        theoremChainStatement distributedResidualStratumCurvatureBridgeStep
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

nSFloorToFrameStabilityTheoremChainRowCountIs6 :
  nSFloorToFrameStabilityTheoremChainRowCount ≡ 6
nSFloorToFrameStabilityTheoremChainRowCountIs6 =
  refl

data NSFloorToFrameStabilityBoundaryGap : Set where
  quantitativeCocycleLowerBoundBridgeMissing :
    NSFloorToFrameStabilityBoundaryGap
  scalarFloorDoesNotForceFrameGap :
    NSFloorToFrameStabilityBoundaryGap
  distributedResidualStratumCurvatureBridgeUnproved :
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
  quantitativeCocycleLowerBoundBridgeMissing
  scalarFloorDoesNotForceFrameGap
  ∷ distributedResidualStratumCurvatureBridgeUnproved
  ∷ frameGapTargetStillOpen
  ∷ theoremChainClosureStillOpen
  ∷ theoremFullNSClayPromotionClosed
  ∷ []

nSFloorToFrameStabilityBoundaryGapCount : Nat
nSFloorToFrameStabilityBoundaryGapCount =
  listLength canonicalNSFloorToFrameStabilityBoundaryGaps

nSFloorToFrameStabilityBoundaryGapCountIs6 :
  nSFloorToFrameStabilityBoundaryGapCount ≡ 6
nSFloorToFrameStabilityBoundaryGapCountIs6 =
  refl

canonicalWitnessTerm : String
canonicalWitnessTerm =
  "candidate-only receipt: the quantitative cocycle lower-bound input and scalar floor are recorded, but they do not imply K_N < 1; the distributed-residual / stratum-curvature bridge remains open."

organizationString : String
organizationString =
  "O: record the active NS triad floor-to-frame stability boundary as a fail-closed receipt."

requirementString : String
requirementString =
  "R: record that the quantitative cocycle lower-bound input and scalar floor still do not imply a K_N < 1 frame gap, and isolate the distributed-residual / stratum-curvature bridge."

codeArtifactString : String
codeArtifactString =
  "C: export canonical rows, theorem-chain rows, gaps, and a compact ORCSLPGF surface with explicit false promotion gates."

stateString : String
stateString =
  "S: the quantitative input and floor are recorded, the frame gap remains open, the distributed-residual / stratum-curvature bridge is isolated, and theorem/full-NS/Clay promotions stay false."

latticeString : String
latticeString =
  "L: quantitative cocycle lower-bound input -> scalar cocycle frustration floor -> open K_N < 1 frame gap -> distributed-residual / stratum-curvature bridge -> target theorem chain -> fail-closed boundary."

proposalString : String
proposalString =
  "P: keep the quantitative input and floor as diagnostic inputs only and promote nothing until the bridge and curvature layer are genuinely discharged."

governanceString : String
governanceString =
  "G: theorem, full-NS, and Clay promotion remain false throughout this boundary."

failString : String
failString =
  "F: the missing evidence is the quantitative cocycle lower-bound proof chain and the distributed-residual / stratum-curvature control that would bridge the floor to the frame gap."

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

    quantitativeCocycleLowerBoundInputFlag :
      Bool
    quantitativeCocycleLowerBoundInputFlagIsTrue :
      quantitativeCocycleLowerBoundInputFlag ≡ true

    floorAloneImpliesFrameGap :
      Bool
    floorAloneImpliesFrameGapIsFalse :
      floorAloneImpliesFrameGap ≡ false

    frameGapTargetRecorded :
      Bool
    frameGapTargetRecordedIsTrue :
      frameGapTargetRecorded ≡ true

    distributedResidualStratumCurvatureBridgeRecorded :
      Bool
    distributedResidualStratumCurvatureBridgeRecordedIsTrue :
      distributedResidualStratumCurvatureBridgeRecorded ≡ true

    distributedResidualStratumCurvatureBridgeProved :
      Bool
    distributedResidualStratumCurvatureBridgeProvedIsFalse :
      distributedResidualStratumCurvatureBridgeProved ≡ false

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
      "Candidate-only floor-to-frame stability boundary: the quantitative cocycle lower-bound input and scalar cocycle frustration floor are recorded, but they do not imply K_N < 1; the distributed-residual / stratum-curvature bridge remains open and theorem/full-NS/Clay flags stay false."

open NSFloorToFrameStabilityBoundary public

canonicalNSFloorToFrameStabilityBoundary :
  NSFloorToFrameStabilityBoundary
canonicalNSFloorToFrameStabilityBoundary =
  record
    { receiptName =
        "NSFloorToFrameStabilityBoundary"
    ; receiptNameIsCanonical =
        refl
    ; witnessTerm =
        canonicalWitnessTerm
    ; witnessTermIsCanonical =
        refl
    ; candidateOnly =
        true
    ; candidateOnlyIsTrue =
        refl
    ; failClosed =
        true
    ; failClosedIsTrue =
        refl
    ; scalarCocycleFrustrationFloorFlag =
        true
    ; scalarCocycleFrustrationFloorFlagIsTrue =
        refl
    ; quantitativeCocycleLowerBoundInputFlag =
        true
    ; quantitativeCocycleLowerBoundInputFlagIsTrue =
        refl
    ; floorAloneImpliesFrameGap =
        false
    ; floorAloneImpliesFrameGapIsFalse =
        refl
    ; frameGapTargetRecorded =
        true
    ; frameGapTargetRecordedIsTrue =
        refl
    ; distributedResidualStratumCurvatureBridgeRecorded =
        true
    ; distributedResidualStratumCurvatureBridgeRecordedIsTrue =
        refl
    ; distributedResidualStratumCurvatureBridgeProved =
        false
    ; distributedResidualStratumCurvatureBridgeProvedIsFalse =
        refl
    ; targetTheoremChainExposed =
        true
    ; targetTheoremChainExposedIsTrue =
        refl
    ; theoremPromoted =
        false
    ; theoremPromotedIsFalse =
        refl
    ; fullNSPromoted =
        false
    ; fullNSPromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; orcslpgf =
        canonicalNSFloorToFrameStabilityBoundaryORCSLPGF
    ; orcslpgfIsCanonical =
        refl
    ; rows =
        canonicalNSFloorToFrameStabilityBoundaryRows
    ; rowsAreCanonical =
        refl
    ; rowCount =
        nSFloorToFrameStabilityBoundaryRowCount
    ; rowCountIsCanonical =
        refl
    ; theoremChainRows =
        canonicalNSFloorToFrameStabilityTheoremChainRows
    ; theoremChainRowsAreCanonical =
        refl
    ; theoremChainRowCount =
        nSFloorToFrameStabilityTheoremChainRowCount
    ; theoremChainRowCountIsCanonical =
        refl
    ; gaps =
        canonicalNSFloorToFrameStabilityBoundaryGaps
    ; gapsAreCanonical =
        refl
    ; gapCount =
        nSFloorToFrameStabilityBoundaryGapCount
    ; gapCountIsCanonical =
        refl
    ; statement =
        "Candidate-only floor-to-frame stability boundary: the quantitative cocycle lower-bound input and scalar cocycle frustration floor are recorded, but they do not imply K_N < 1; the distributed-residual / stratum-curvature bridge remains open and theorem/full-NS/Clay flags stay false."
    ; statementIsCanonical =
        refl
    }

scalarFloorDoesNotImplyFrameGap :
  floorAloneImpliesFrameGap canonicalNSFloorToFrameStabilityBoundary ≡ false
scalarFloorDoesNotImplyFrameGap =
  refl

distributedResidualStratumCurvatureBridgeStillOpen :
  distributedResidualStratumCurvatureBridgeProved canonicalNSFloorToFrameStabilityBoundary
  ≡ false
distributedResidualStratumCurvatureBridgeStillOpen =
  refl

allPromotionsFalse :
  theoremPromoted canonicalNSFloorToFrameStabilityBoundary ≡ false
allPromotionsFalse =
  refl
