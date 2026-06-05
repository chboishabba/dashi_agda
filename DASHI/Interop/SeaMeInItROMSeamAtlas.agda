module DASHI.Interop.SeaMeInItROMSeamAtlas where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Maybe using (Maybe)

import DASHI.Interop.SeaMeInItROMKernelFormalism as ROM
import DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Core as UC
import DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Methods as UM
import DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Benchmark as UB
import DASHI.Interop.SeaMeInIt.Unwrap.Competitor.GarmentGate as UG

------------------------------------------------------------------------
-- Adaptive body atlas layer
------------------------------------------------------------------------

record ROMSeamAtlasReceipt
    (base : ROM.SeaMeInItROMKernelSurface) : Set₁ where
  field
    AtlasCell : Set
    FabricSpec : Set
    SeamPatch : Set

    atlasCellToVertex :
      AtlasCell →
      ROM.Vertex (ROM.body base)

    atlasCellFabric :
      AtlasCell →
      FabricSpec

    projectedFieldAtlas :
      List
        (ROM.ProjectedField
          (ROM.body base)
          (ROM.basis base)
          (ROM.rom base))

    seamPatchEdges :
      SeamPatch →
      List (ROM.Edge (ROM.seamGraph base))

    seamPatchGate :
      SeamPatch →
      ROM.TriGate

    fabricGate :
      FabricSpec →
      ROM.TriGate

    fieldAtlasGate : ROM.TriGate
    romSeamCompatibilityGate : ROM.TriGate
    fabricSeamCompatibilityGate : ROM.TriGate

    unwrapRun : UB.CompetitorRunReceipt
    unwrapBoundary : UC.ClaimBoundary

    unwrapBoundaryMatchesRun :
      unwrapBoundary ≡ UM.claimBoundary (UB.method unwrapRun)

    noUnwrapGlobalOptimality :
      UC.claimsGlobalOptimality unwrapBoundary ≡ false

    noUnwrapTrueInverse :
      UC.claimsTrueInverse unwrapBoundary ≡ false

    noUnwrapManufacturingAuthority :
      UC.claimsManufacturingAuthority unwrapBoundary ≡ false

    garmentPattern :
      Maybe UG.GarmentPatternReceipt

    atlasReceipt : String
    plainReading : String

open ROMSeamAtlasReceipt public

record ROMSeamAtlasTheoremSurface : Set₁ where
  field
    baseSurface : ROM.SeaMeInItROMKernelSurface
    atlasLayer : ROMSeamAtlasReceipt baseSurface
    pipelineOrder : ROM.PipelineOrderWitness baseSurface

    bodyAtlasGate : ROM.TriGate
    fieldAtlasGateAll : ROM.TriGate
    seamAtlasGate : ROM.TriGate
    unwrapRunGate : ROM.TriGate
    garmentPatternGate : ROM.TriGate

    nonPromotionBoundary :
      List ROM.ClaimBoundary

    exportedPatternIsSerializationOnly : Set
    noBodyAtlasGlobalOptimumClaim : Set
    noPatternManufacturingWithoutGate : Set
    theoremThinBoundary : Set
    plainReading : String

  strictAtlasGates : List ROM.TriGate
  strictAtlasGates =
    bodyAtlasGate
    ∷ fieldAtlasGateAll
    ∷ seamAtlasGate
    ∷ unwrapRunGate
    ∷ garmentPatternGate
    ∷ []

  atlasPromotionState : ROM.PromotionState
  atlasPromotionState =
    ROM.promotionFromGates strictAtlasGates

open ROMSeamAtlasTheoremSurface public

record ROMSeamAtlasPromoted
    (surface : ROMSeamAtlasTheoremSurface) : Set₁ where
  field
    basePromoted :
      ROM.PromotionCertificate (baseSurface surface)

    atlasGatesClear :
      ROM.allAdmissible (strictAtlasGates surface) ≡ true

    noGlobalOptimalityClaim :
      UC.claimsGlobalOptimality
        (unwrapBoundary (atlasLayer surface))
      ≡ false

    noInverseClaim :
      UC.claimsTrueInverse
        (unwrapBoundary (atlasLayer surface))
      ≡ false

    noManufacturingAuthorityClaim :
      UC.claimsManufacturingAuthority
        (unwrapBoundary (atlasLayer surface))
      ≡ false

    garmentEvidence : Set

open ROMSeamAtlasPromoted public
