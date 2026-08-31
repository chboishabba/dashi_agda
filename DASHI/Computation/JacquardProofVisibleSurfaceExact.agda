module DASHI.Computation.JacquardProofVisibleSurfaceExact where

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.List using (_++_)

import DASHI.Algebra.Trit as Trit
import DASHI.Computation.JacquardOperationalSemanticsExact as Jacquard
import DASHI.Combinatorics.ProofFabricCompilerExact as ProofFabric
import DASHI.Combinatorics.TextileFibreHyperfabricExact as TextileHyper
import DASHI.Reasoning.TypedHyperfabricCore as Hyper
import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.LoomEncoding as Loom
import DASHI.Core.ProjectionCategory as PC
import DASHI.Core.ProjectionFibre as PF

------------------------------------------------------------------------
-- JACQUARD -> VISIBLE OUTPUT
--
-- The existing Jacquard owner stops at executed crossing rows.  This owner
-- adds the physically visible face projection and welds the proof-fabric codec
-- to the repo's actual Jacquard operational semantics, FibreRestrictionCore,
-- TypedHyperfabric trace and legacy LoomEncoding vocabulary.
--
-- For the first exact backend we use two warp ends per proof symbol because
-- VerifiedFiniteTritCoder already uses two bits per trit.  A visible Bool says
-- whether the warp is on the visible face at that crossing.
------------------------------------------------------------------------

VisibleCell : Set
VisibleCell = Bool

VisibleRow2 : Set
VisibleRow2 = Bool × Bool

VisiblePattern2 : Set
VisiblePattern2 = List VisibleRow2

visibleCrossing : Jacquard.Crossing → VisibleCell
visibleCrossing Jacquard.warpOver = true
visibleCrossing Jacquard.weftOver = false

visibleRow2 : Jacquard.CrossingRow 2 → VisibleRow2
visibleRow2 row =
  visibleCrossing (row Fin.zero) ,
  visibleCrossing (row (Fin.suc Fin.zero))

visibleWovenRows2 : Jacquard.WovenRows 2 → VisiblePattern2
visibleWovenRows2 [] = []
visibleWovenRows2 (row ∷ rows) =
  visibleRow2 row ∷ visibleWovenRows2 rows

visibleProgram2 : Jacquard.JacquardProgram 2 → VisiblePattern2
visibleProgram2 program = visibleWovenRows2 (Jacquard.executeProgram program)

visibleSchedule2 : Jacquard.LiftSchedule 2 → VisiblePattern2
visibleSchedule2 schedule = visibleWovenRows2 (Jacquard.executeSchedule schedule)

visibleCompilationCorrect :
  (program : Jacquard.JacquardProgram 2) →
  visibleSchedule2 (Jacquard.compile program) ≡ visibleProgram2 program
visibleCompilationCorrect program =
  cong visibleWovenRows2 (Jacquard.compilePreservesExecution program)

------------------------------------------------------------------------
-- Exact two-warp Jacquard masks for the four proof tiles.
------------------------------------------------------------------------

tileMask : ProofFabric.ProofWeaveTile → Jacquard.LiftMask 2
tileMask ProofFabric.tile00 Fin.zero = false
tileMask ProofFabric.tile00 (Fin.suc Fin.zero) = false
tileMask ProofFabric.tile01 Fin.zero = false
tileMask ProofFabric.tile01 (Fin.suc Fin.zero) = true
tileMask ProofFabric.tile10 Fin.zero = true
tileMask ProofFabric.tile10 (Fin.suc Fin.zero) = false
tileMask ProofFabric.tile11 Fin.zero = true
tileMask ProofFabric.tile11 (Fin.suc Fin.zero) = true

tileInstruction : ProofFabric.ProofWeaveTile → Jacquard.JacquardInstruction 2
tileInstruction tile = Jacquard.liftMask (tileMask tile)

compileTilesToJacquard :
  List ProofFabric.ProofWeaveTile →
  Jacquard.JacquardProgram 2
compileTilesToJacquard [] = []
compileTilesToJacquard (tile ∷ tiles) =
  tileInstruction tile ∷ compileTilesToJacquard tiles

------------------------------------------------------------------------
-- Visible face semantics of the four code tiles.
------------------------------------------------------------------------

visibleTile : ProofFabric.ProofWeaveTile → VisibleRow2
visibleTile ProofFabric.tile00 = false , false
visibleTile ProofFabric.tile01 = false , true
visibleTile ProofFabric.tile10 = true , false
visibleTile ProofFabric.tile11 = true , true

visibleTileExecutionExact :
  (tile : ProofFabric.ProofWeaveTile) →
  visibleRow2 (Jacquard.weaveRow (tileMask tile)) ≡ visibleTile tile
visibleTileExecutionExact ProofFabric.tile00 = refl
visibleTileExecutionExact ProofFabric.tile01 = refl
visibleTileExecutionExact ProofFabric.tile10 = refl
visibleTileExecutionExact ProofFabric.tile11 = refl

visiblePatternOfTiles : List ProofFabric.ProofWeaveTile → VisiblePattern2
visiblePatternOfTiles [] = []
visiblePatternOfTiles (tile ∷ tiles) =
  visibleTile tile ∷ visiblePatternOfTiles tiles

jacquardTilesProduceVisiblePattern :
  (tiles : List ProofFabric.ProofWeaveTile) →
  visibleProgram2 (compileTilesToJacquard tiles)
  ≡ visiblePatternOfTiles tiles
jacquardTilesProduceVisiblePattern [] = refl
jacquardTilesProduceVisiblePattern (tile ∷ tiles)
  rewrite visibleTileExecutionExact tile
        | jacquardTilesProduceVisiblePattern tiles = refl

------------------------------------------------------------------------
-- Visible-output decoder.
--
-- This is the key step beyond "program execution": the visible face itself is
-- sufficient to recover the neutral proof-code stream.  The 11 face remains
-- the already-reserved malformed tile and therefore decodes to nothing.
------------------------------------------------------------------------

visibleRowToTile : VisibleRow2 → ProofFabric.ProofWeaveTile
visibleRowToTile (false , false) = ProofFabric.tile00
visibleRowToTile (false , true) = ProofFabric.tile01
visibleRowToTile (true , false) = ProofFabric.tile10
visibleRowToTile (true , true) = ProofFabric.tile11

visibleTileRoundtrip :
  (tile : ProofFabric.ProofWeaveTile) →
  visibleRowToTile (visibleTile tile) ≡ tile
visibleTileRoundtrip ProofFabric.tile00 = refl
visibleTileRoundtrip ProofFabric.tile01 = refl
visibleTileRoundtrip ProofFabric.tile10 = refl
visibleTileRoundtrip ProofFabric.tile11 = refl

readVisiblePattern : VisiblePattern2 → List (Maybe Trit.Trit)
readVisiblePattern [] = []
readVisiblePattern (row ∷ rows) =
  ProofFabric.tileToTrit (visibleRowToTile row) ∷ readVisiblePattern rows

readVisibleCompiledTritStream :
  (stream : List Trit.Trit) →
  readVisiblePattern
    (visiblePatternOfTiles (ProofFabric.compileTritStream stream))
  ≡ ProofFabric.justTritStream stream
readVisibleCompiledTritStream [] = refl
readVisibleCompiledTritStream (Trit.neg ∷ stream)
  rewrite readVisibleCompiledTritStream stream = refl
readVisibleCompiledTritStream (Trit.zer ∷ stream)
  rewrite readVisibleCompiledTritStream stream = refl
readVisibleCompiledTritStream (Trit.pos ∷ stream)
  rewrite readVisibleCompiledTritStream stream = refl

------------------------------------------------------------------------
-- Proof -> actual Jacquard program -> executed cloth -> visible face.
------------------------------------------------------------------------

proofTiles :
  {Proof : Set} →
  ProofFabric.ProofTritCodec Proof →
  Proof →
  List ProofFabric.ProofWeaveTile
proofTiles codec proof =
  ProofFabric.compileTritStream (ProofFabric.serializeProof codec proof)

proofToJacquard :
  {Proof : Set} →
  ProofFabric.ProofTritCodec Proof →
  Proof →
  Jacquard.JacquardProgram 2
proofToJacquard codec proof = compileTilesToJacquard (proofTiles codec proof)

proofVisiblePattern :
  {Proof : Set} →
  ProofFabric.ProofTritCodec Proof →
  Proof →
  VisiblePattern2
proofVisiblePattern codec proof = visibleProgram2 (proofToJacquard codec proof)

proofVisiblePatternExact :
  {Proof : Set} →
  (codec : ProofFabric.ProofTritCodec Proof) →
  (proof : Proof) →
  proofVisiblePattern codec proof ≡ visiblePatternOfTiles (proofTiles codec proof)
proofVisiblePatternExact codec proof =
  jacquardTilesProduceVisiblePattern (proofTiles codec proof)

proofVisibleCodeReadable :
  {Proof : Set} →
  (codec : ProofFabric.ProofTritCodec Proof) →
  (proof : Proof) →
  readVisiblePattern (proofVisiblePattern codec proof)
  ≡ ProofFabric.justTritStream (ProofFabric.serializeProof codec proof)
proofVisibleCodeReadable codec proof
  rewrite proofVisiblePatternExact codec proof =
  readVisibleCompiledTritStream (ProofFabric.serializeProof codec proof)

------------------------------------------------------------------------
-- Canonical FibreRestrictionCore over the same physical-program carrier.
--
-- The carrier is the hidden Jacquard control program; the surface is the
-- visible cloth face.  The fibre intentionally retains possible hidden program
-- histories instead of asserting that visible appearance uniquely determines
-- loom construction.
------------------------------------------------------------------------

data JacquardVisibleEvidence : Set where
  inspectedVisibleFace : JacquardVisibleEvidence

jacquardVisibleFibreCore : Fibre.FibreRestrictionCore
jacquardVisibleFibreCore =
  Fibre.fibreRestrictionCore
    (Jacquard.JacquardProgram 2)
    VisiblePattern2
    JacquardVisibleEvidence
    visibleProgram2
    (λ surface → Jacquard.JacquardProgram 2)
    (λ evidence surface → Jacquard.JacquardProgram 2)
    true
    false

------------------------------------------------------------------------
-- Same proof tiles -> same actual TypedHyperfabric edge trace.
------------------------------------------------------------------------

proofJacquardHyperfabricTrace :
  {Proof : Set} →
  ProofFabric.ProofTritCodec Proof →
  Proof →
  Hyper.HyperfabricTrace (TextileHyper.TextileEdge 2)
proofJacquardHyperfabricTrace codec proof =
  ProofFabric.proofFabricHyperfabricTrace (proofTiles codec proof)

record JacquardProofFabricWitness (Proof : Set) : Set where
  constructor jacquard-proof-fabric-witness
  field
    sourceProof : Proof
    tiles : List ProofFabric.ProofWeaveTile
    program : Jacquard.JacquardProgram 2
    visiblePattern : VisiblePattern2
    hyperfabricTrace : Hyper.HyperfabricTrace (TextileHyper.TextileEdge 2)
    programExact : program ≡ compileTilesToJacquard tiles
    visibleExact : visiblePattern ≡ visiblePatternOfTiles tiles
    traceExact : hyperfabricTrace ≡ ProofFabric.proofFabricHyperfabricTrace tiles

open JacquardProofFabricWitness public

compileProofToJacquardWitness :
  {Proof : Set} →
  (codec : ProofFabric.ProofTritCodec Proof) →
  (proof : Proof) →
  JacquardProofFabricWitness Proof
compileProofToJacquardWitness codec proof =
  jacquard-proof-fabric-witness
    proof
    (proofTiles codec proof)
    (proofToJacquard codec proof)
    (visiblePatternOfTiles (proofTiles codec proof))
    (proofJacquardHyperfabricTrace codec proof)
    refl
    refl
    refl

------------------------------------------------------------------------
-- Actual legacy LoomEncoding instance over the same Jacquard program carrier.
--
-- Strand = hidden Jacquard program.
-- Weave  = program fragment / sequential instruction stream.
-- ProjectionSurface = visible cloth face.
-- Fibre-equivalence = equality after visible projection.
--
-- This does not replace FibreRestrictionCore or TypedHyperfabric; it connects
-- the textile tranche back to the repo's pre-existing loom vocabulary.
------------------------------------------------------------------------

jacquardVisibleLoomEncoding :
  Loom.LoomEncoding PC.canonicalProjectionCategory PF.canonicalProjectionFibre
jacquardVisibleLoomEncoding = record
  { Loom.Strand = Jacquard.JacquardProgram 2
  ; Loom.Weave = Jacquard.JacquardProgram 2
  ; Loom.weaveId = λ program → []
  ; Loom.weaveSeq = _++_
  ; Loom.ProjectionSurface = VisiblePattern2
  ; Loom.project = visibleProgram2
  ; Loom.fibreEquivalent =
      λ first second → visibleProgram2 first ≡ visibleProgram2 second
  ; Loom.residual = λ first second → first ≡ second
  ; Loom.closed = λ first second → visibleProgram2 first ≡ visibleProgram2 second
  ; Loom.loomReading =
      "Jacquard proof loom: hidden program projects to visible warp/weft face pattern."
  }

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data VisibleFaceDeterminesAllConstructionHistory : Set where
data JacquardExecutionEqualsMaterialMechanics : Set where
data VisibleProofCodeCreatesProofValidity : Set where

visibleFaceDoesNotDetermineAllConstructionHistory :
  VisibleFaceDeterminesAllConstructionHistory → ⊥
visibleFaceDoesNotDetermineAllConstructionHistory ()

jacquardExecutionDoesNotClaimMaterialMechanics :
  JacquardExecutionEqualsMaterialMechanics → ⊥
jacquardExecutionDoesNotClaimMaterialMechanics ()

visibleCodeDoesNotCreateProofValidity :
  VisibleProofCodeCreatesProofValidity → ⊥
visibleCodeDoesNotCreateProofValidity ()
