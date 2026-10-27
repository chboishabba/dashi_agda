module DASHI.Unified.IITExactNonPromotion where

-- ZKP O: Reuse original proof owners without changing their statements.
-- ZKP R: The selected pairwise observation is the complete input.
-- ZKP C: Arbitrary deterministic consumers may read only that input.
-- ZKP S: A hidden triadic face is not a function of that input.
-- ZKP L: An explicitly selected trinification shear is not a cube-graph symmetry.
-- ZKP P: Proofs below are source-written compositions, not numerical receipts.
-- ZKP G: No physical, Monster, or phenomenal identity follows.
-- ZKP F: The required causal-state and action intertwiners remain independent.
--
-- Attribution: the trialectic non-descent, exact cube witness, and the
-- first-Tits/trinification formula retain their original module/PR owners.

open import DASHI.Core.Prelude

import DASHI.Biology.IITFullStructureHigherFaceNonDescentExact as Face
import DASHI.Biology.IITPointedTernary27TriadicNonDescentExact as Triadic
import DASHI.Biology.IITCubeTrinificationSymmetryBreakingExact as Cube
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

pairwiseObservationCannotDetermineHiddenFace :
  {Output : Set} →
  (observe : Triadic.ThreeSelectedCubies → Output) →
  Descent.FactorsThrough (Face.pairwiseIITObservation observe)
                         Triadic.triadicFaceConsumer → ⊥
pairwiseObservationCannotDetermineHiddenFace =
  Face.pairwiseIITOutputDoesNotDetermineTriadicFace

pairwiseObservationCannotBeConsumerSufficient :
  {Output : Set} →
  (observe : Triadic.ThreeSelectedCubies → Output) →
  Descent.ConsumerSufficient (Face.pairwiseIITObservation observe)
                             Triadic.triadicFaceConsumer → ⊥
pairwiseObservationCannotBeConsumerSufficient =
  Face.pairwiseIITOutputIsNotConsumerSufficient

selectedTrinificationActionDoesNotPreserveCubeGraph :
  Cube.sectorZ Cube.transformedState ≡ Cube.requiredTransformedThird → ⊥
selectedTrinificationActionDoesNotPreserveCubeGraph =
  Cube.selectedTrinificationShearBreaksCubeGraph

selectedShearHasDeterminantOne :
  Cube.det3 Cube.selectedC ≡ Cube.f1
selectedShearHasDeterminantOne = Cube.selectedCDeterminantOne

selectedShearHasRightInverse :
  Cube.matMul Cube.selectedC Cube.selectedCInv ≡ Cube.identityM
selectedShearHasRightInverse = Cube.selectedCInverseRight

selectedShearHasLeftInverse :
  Cube.matMul Cube.selectedCInv Cube.selectedC ≡ Cube.identityM
selectedShearHasLeftInverse = Cube.selectedCInverseLeft
