module DASHI.Biology.IITFullStructureHigherFaceNonDescentExact where

------------------------------------------------------------------------
-- FULL-IIT HIDDEN-FACE NON-DESCENT
--
-- The mature trialectic fixture already contains two structured worlds with
-- exactly the same selected/pairwise boundary and different irreducible
-- triadic faces.  Consequently ANY deterministic IIT construction whose
-- complete causal input (TPM + current observed state + version/configuration)
-- is itself a function only of that shared boundary must return the same IIT
-- output on those two worlds.
--
-- This is stronger than checking scalar system-phi numerically.  It applies to
-- an arbitrary output type, so it covers system phi, the distinction set, the
-- relation set, a complete cause-effect structure and big-Phi whenever those
-- objects are computed solely from the declared shared IIT input surface.
--
-- It does NOT say that IIT can never see a triadic face.  If the face is
-- promoted into the actual causal state/TPM then the IIT input is different and
-- a new comparison must be evaluated.  The theorem says hidden structure cannot
-- be recovered from an observation through which it provably does not descend.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.IITPointedTernary27TriadicNonDescentExact as Triadic
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Trialectic

------------------------------------------------------------------------
-- 1. Any IIT result computed only from the selected/pairwise boundary.
------------------------------------------------------------------------

pairwiseIITObservation :
  {IITOutput : Set} →
  (Triadic.ThreeSelectedCubies → IITOutput) →
  Trialectic.StructuredTrialecticState → IITOutput
pairwiseIITObservation observe state =
  observe (Triadic.selectedCubiesObserver state)

samePairwiseInputGivesSameIITOutput :
  {IITOutput : Set} →
  (observe : Triadic.ThreeSelectedCubies → IITOutput) →
  pairwiseIITObservation observe Trialectic.structuredReciprocal
  ≡ pairwiseIITObservation observe Trialectic.structuredUnderdetermined
samePairwiseInputGivesSameIITOutput observe =
  cong observe Triadic.sameSelectedCubies

------------------------------------------------------------------------
-- 2. Therefore no such IIT output can be sufficient for the hidden face.
------------------------------------------------------------------------

pairwiseIITOutputDoesNotDetermineTriadicFace :
  {IITOutput : Set} →
  (observe : Triadic.ThreeSelectedCubies → IITOutput) →
  Descent.FactorsThrough
    (pairwiseIITObservation observe)
    Triadic.triadicFaceConsumer →
  ⊥
pairwiseIITOutputDoesNotDetermineTriadicFace observe =
  Descent.nonDescentWitnessBlocksFactorization
    (Descent.consumerNonDescentWitness
      Trialectic.structuredReciprocal
      Trialectic.structuredUnderdetermined
      (samePairwiseInputGivesSameIITOutput observe)
      Triadic.differentTriadicFace)

pairwiseIITOutputIsNotConsumerSufficient :
  {IITOutput : Set} →
  (observe : Triadic.ThreeSelectedCubies → IITOutput) →
  Descent.ConsumerSufficient
    (pairwiseIITObservation observe)
    Triadic.triadicFaceConsumer →
  ⊥
pairwiseIITOutputIsNotConsumerSufficient observe =
  Descent.nonDescentWitnessBlocksSufficiency
    (Descent.consumerNonDescentWitness
      Trialectic.structuredReciprocal
      Trialectic.structuredUnderdetermined
      (samePairwiseInputGivesSameIITOutput observe)
      Triadic.differentTriadicFace)

------------------------------------------------------------------------
-- 3. Modelling boundary.
------------------------------------------------------------------------

record FullStructureHigherFaceBoundary : Set where
  constructor full-structure-higher-face-boundary
  field
    sameDeclaredPairwiseInputForWitnessPair : Bool
    arbitraryFunctionOfPairwiseInputAlsoSame : Bool
    scalarSystemPhiCanRecoverHiddenFaceByItself : Bool
    fullCESCanRecoverHiddenFaceIfItsEntireInputFactorsThroughPairwiseSurface : Bool
    promotingTriadicFaceIntoTPMChangesTheModel : Bool
    promotedFaceModelStillRequiresIndependentIITEvaluation : Bool

canonicalFullStructureHigherFaceBoundary : FullStructureHigherFaceBoundary
canonicalFullStructureHigherFaceBoundary =
  full-structure-higher-face-boundary
    true true false false true true
