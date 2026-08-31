module DASHI.JacquardProofVisibleSurfaceValidation where

open import DASHI.Core.Prelude

import DASHI.Computation.JacquardOperationalSemanticsExact as Jacquard
import DASHI.Computation.JacquardProofVisibleSurfaceExact as Visible
import DASHI.Combinatorics.ProofFabricCompilerExact as ProofFabric

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

jacquardVisibleFibreRegression : DASHI.Core.FibreRestrictionCore.FibreRestrictionCore
jacquardVisibleFibreRegression = Visible.jacquardVisibleFibreCore

jacquardVisibleLoomRegression :
  DASHI.Core.LoomEncoding.LoomEncoding
    DASHI.Core.ProjectionCategory.canonicalProjectionCategory
    DASHI.Core.ProjectionFibre.canonicalProjectionFibre
jacquardVisibleLoomRegression = Visible.jacquardVisibleLoomEncoding
