module DASHI.JacquardProofVisibleSurfaceValidation where

open import DASHI.Core.Prelude

import DASHI.Computation.JacquardOperationalSemanticsExact as Jacquard
import DASHI.Computation.JacquardProofVisibleSurfaceExact as Visible
import DASHI.Combinatorics.ProofFabricCompilerExact as ProofFabric
import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.LoomEncoding as Loom
import DASHI.Core.ProjectionCategory as PC
import DASHI.Core.ProjectionFibre as PF

visibleCompilerRegression :
  (program : Jacquard.JacquardProgram 2) →
  Visible.visibleSchedule2 (Jacquard.compile program)
  ≡ Visible.visibleProgram2 program
visibleCompilerRegression = Visible.visibleCompilationCorrect

visibleTileRegression :
  (tile : ProofFabric.ProofWeaveTile) →
  Visible.visibleRow2 (Jacquard.weaveRow (Visible.tileMask tile))
  ≡ Visible.visibleTile tile
visibleTileRegression = Visible.visibleTileExecutionExact

visibleProofReadbackRegression :
  {Proof : Set} →
  (codec : ProofFabric.ProofTritCodec Proof) →
  (proof : Proof) →
  Visible.readVisiblePattern (Visible.proofVisiblePattern codec proof)
  ≡ ProofFabric.justTritStream (ProofFabric.serializeProof codec proof)
visibleProofReadbackRegression = Visible.proofVisibleCodeReadable

jacquardVisibleFibreRegression : Fibre.FibreRestrictionCore
jacquardVisibleFibreRegression = Visible.jacquardVisibleFibreCore

jacquardVisibleLoomRegression :
  Loom.LoomEncoding PC.canonicalProjectionCategory PF.canonicalProjectionFibre
jacquardVisibleLoomRegression = Visible.jacquardVisibleLoomEncoding
