module DASHI.ComputerScience.RSA260BidiSignedResidualAStarSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Biology.FRACTRANSSPTransitionExact as Fractran
import DASHI.Computation.AStarPlateauFibreExact as AStar
import DASHI.ComputerScience.RSA260BidiAStarCoefficientResidualReopeningExact as Reopening

------------------------------------------------------------------------
-- RSA-260 SIGNED RESIDUAL / A* SEARCH CROSS-POLLINATION
--
-- The RSA coefficient-residual lane now has a coarse packet plus a retained
-- generator-sensitive residual.  This owner imports two already-existing DASHI
-- structures to organise the NEXT compression search without identifying their
-- source domains with Block-Wiedemann algebra:
--
--   * SIGNED/SSP/FRACTRAN contributes oriented add/remove/mediate edits and the
--     distinction between description length, execution length, normal-form /
--     residual-witness cost, plus a typed first-enabled priority donor;
--   * A* contributes an equal-f plateau whose hidden tie/open-tail state may be
--     residual, under an explicit heuristic/correctness contract.
--
-- This is a structural adapter only.  SSP prime geometry is not generator
-- algebra; FRACTRAN execution is not lingen; path-search A* is not CADO's A*
-- Krylov artifact; and no admissible RSA search heuristic is claimed here.
------------------------------------------------------------------------

reopeningBoundary : Reopening.CoefficientResidualReopeningBoundary
reopeningBoundary = Reopening.canonicalCoefficientResidualReopeningBoundary

signedBoundary : Signed.SignedSSPWeaveBoundary
signedBoundary = Signed.canonicalSignedSSPWeaveBoundary

fractranBoundary : Fractran.FRACTRANSSPBoundary
fractranBoundary = Fractran.canonicalFRACTRANSSPBoundary

aStarBoundary : AStar.AStarFibreBoundary
aStarBoundary = AStar.canonicalAStarFibreBoundary

------------------------------------------------------------------------
-- Signed edit orientation.
--
-- Positive/negative/zero multiplicity is used only as an edit-orientation
-- carrier.  Magnitude is retained, while coarse polarity may forget it just as
-- in the donor.  No SSP prime is identified with a coefficient coordinate.
------------------------------------------------------------------------

data ResidualEdit : Set where
  addResidual : Nat → ResidualEdit
  mediateResidual : ResidualEdit
  removeResidual : Nat → ResidualEdit

residualEditMultiplicity : ResidualEdit → Signed.SignedMultiplicity
residualEditMultiplicity (addResidual n) = Signed.positiveMultiplicity n
residualEditMultiplicity mediateResidual = Signed.zeroMultiplicity
residualEditMultiplicity (removeResidual n) = Signed.negativeMultiplicity n

residualEditOrientation : ResidualEdit → Signed.FibreOrientation
residualEditOrientation edit =
  Signed.orientationOfMultiplicity (residualEditMultiplicity edit)

addOneIsForward :
  residualEditOrientation (addResidual 1) ≡ Signed.forwardOrientation
addOneIsForward = refl

removeOneIsInverse :
  residualEditOrientation (removeResidual 1) ≡ Signed.inverseOrientation
removeOneIsInverse = refl

mediateIsMediated :
  residualEditOrientation mediateResidual ≡ Signed.mediatedOrientation
mediateIsMediated = refl

------------------------------------------------------------------------
-- FRACTRAN first-enabled scheduling is retained as a donor function, not
-- silently reinterpreted as an RSA rewrite machine.
------------------------------------------------------------------------

fractranFirstEnabledDonor :
  Fractran.PrimeValuationState → Fractran.PrimeValuationState
fractranFirstEnabledDonor = Fractran.firstEnabledStep

------------------------------------------------------------------------
-- Structured residual-compression search state.
--
-- Crucially, description cost, execution cost, residual-witness cost and
-- unresolved consumer defects are separate coordinates.  The score below is a
-- candidate scheduling score only.  Until an admissible lower-bound theorem is
-- supplied, it is NOT an A* optimality certificate.
------------------------------------------------------------------------

data ResidualRepresentation : Set where
  fullCoefficientResidual : ResidualRepresentation
  candidateCoefficientSketch : ResidualRepresentation

record ResidualSearchState : Set where
  constructor residual-search-state
  field
    coarsePacket : Reopening.RelationAugmentedCoarse
    targetResidual : Reopening.GeneratorCoefficientResidual
    representation : ResidualRepresentation
    descriptionLength : Nat
    executionLength : Nat
    residualWitnessLength : Nat
    unresolvedConsumerDefects : Nat
    searchSteps : Nat
    plateauTieCode : Bool
    openTailCode : Nat
open ResidualSearchState public

searchScore : ResidualSearchState → Nat
searchScore state =
  descriptionLength state
  + residualWitnessLength state
  + unresolvedConsumerDefects state

typedReplayDescriptionLength : ResidualSearchState → Nat
typedReplayDescriptionLength state =
  descriptionLength state + residualWitnessLength state

fullResidualSearchState : ResidualSearchState
fullResidualSearchState =
  residual-search-state
    Reopening.degree17ZeroExtensionRank128Rel16Shift120
    Reopening.rotate3CoefficientResidual
    fullCoefficientResidual
    4
    8
    1
    0
    2
    false
    1

sketchResidualSearchState : ResidualSearchState
sketchResidualSearchState =
  residual-search-state
    Reopening.degree17ZeroExtensionRank128Rel16Shift120
    Reopening.rotate3CoefficientResidual
    candidateCoefficientSketch
    3
    5
    1
    1
    2
    true
    2

fullTypedDescriptionLengthIsFive :
  typedReplayDescriptionLength fullResidualSearchState ≡ 5
fullTypedDescriptionLengthIsFive = refl

sketchTypedDescriptionLengthIsFour :
  typedReplayDescriptionLength sketchResidualSearchState ≡ 4
sketchTypedDescriptionLengthIsFour = refl

fullExecutionLengthIsEight :
  executionLength fullResidualSearchState ≡ 8
fullExecutionLengthIsEight = refl

sketchExecutionLengthIsFive :
  executionLength sketchResidualSearchState ≡ 5
sketchExecutionLengthIsFive = refl

fullSearchScoreIsFive : searchScore fullResidualSearchState ≡ 5
fullSearchScoreIsFive = refl

sketchSearchScoreIsFive : searchScore sketchResidualSearchState ≡ 5
sketchSearchScoreIsFive = refl

------------------------------------------------------------------------
-- A* plateau adapter.
--
-- Equal scheduling score and equal expanded/search-step count deliberately
-- leave tie/open-tail coordinates hidden by the donor observation.  This makes
-- the residual ordering visible rather than pretending equal-f candidates are
-- identical.
------------------------------------------------------------------------

asAStarFineState : ResidualSearchState → AStar.AStarFineState
asAStarFineState state =
  AStar.aStarFineState
    (searchSteps state)
    (searchScore state)
    (plateauTieCode state)
    (openTailCode state)

aStarObserve : ResidualSearchState → AStar.AStarObservation
aStarObserve state = AStar.observeAStar (asAStarFineState state)

fullAndSketchShareAStarObservation :
  aStarObserve fullResidualSearchState
  ≡ aStarObserve sketchResidualSearchState
fullAndSketchShareAStarObservation = refl

-- The donor contract type is reused, but heuristic admissibility is deliberately
-- left false.  The plateau residual law is paid by the concrete equal-observation
-- witness above; optimality is not.
currentResidualSearchAStarContract : AStar.AStarCorrectnessContract
currentResidualSearchAStarContract =
  AStar.aStarCorrectnessContract false true

------------------------------------------------------------------------
-- Interpretation / roadmap boundary.
------------------------------------------------------------------------

record SignedResidualAStarSearchBoundary : Set where
  constructor signed-residual-astar-search-boundary
  field
    coefficientResidualReopeningInherited : Bool
    signedAddRemoveMediateOrientationPaid : Bool
    descriptionLengthSeparatedFromExecutionLength : Bool
    residualWitnessLengthRetainedSeparately : Bool
    unresolvedConsumerDefectRetainedInSearchScore : Bool
    equalFPlateauCanRetainResidualOrder : Bool
    fractranFirstEnabledDonorAvailable : Bool
    rsaFirstEnabledRewriteFamilyInstantiated : Bool
    residualSearchHeuristicAdmissibilityPaid : Bool
    residualSearchOptimalityPaid : Bool
    pathSearchAStarIsCADOAStarArtifact : Bool
    signedSSPPrimeGeometryIsGeneratorCoefficientAlgebra : Bool
    finiteSearchCostIsKolmogorovComplexityTheorem : Bool
    fullCoefficientResidualProvedGloballyMinimal : Bool
    productionAStarOrFSolsAcquired : Bool
open SignedResidualAStarSearchBoundary public

canonicalSignedResidualAStarSearchBoundary : SignedResidualAStarSearchBoundary
canonicalSignedResidualAStarSearchBoundary =
  signed-residual-astar-search-boundary
    true
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false
    false
    false

------------------------------------------------------------------------
-- Live residuals.
--
-- The first task is NOT to claim A* optimality.  It is to instantiate a small
-- consumer-safe residual rewrite family, execute it against the existing
-- generator-identity collision portfolio, and only then ask whether a useful
-- admissible lower bound exists for search ordering.
------------------------------------------------------------------------

data SignedResidualAStarSearchResidual : Set where
  instantiateConsumerSafeResidualRewriteFamily : SignedResidualAStarSearchResidual
  executeBoundedStructuredCompressionSearch : SignedResidualAStarSearchResidual
  compareSurvivorsAgainstGeneratorIdentityCollisionPortfolio : SignedResidualAStarSearchResidual
  proveAdmissibleLowerBoundForResidualSearchHeuristic : SignedResidualAStarSearchResidual
  compileWinningResidualIntoProductionReplayPacket : SignedResidualAStarSearchResidual
  acquireSameObjectAStarOrFSols : SignedResidualAStarSearchResidual

firstSignedResidualAStarSearchResidual : SignedResidualAStarSearchResidual
firstSignedResidualAStarSearchResidual =
  instantiateConsumerSafeResidualRewriteFamily

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data PathSearchAStarMeansCADOAStar : Set where
data SignedSSPMeansGeneratorAlgebra : Set where
data EqualFMeansEquivalentResidual : Set where
data ShortDescriptionMeansShortExecution : Set where
data CandidateScoreMeansAdmissibleHeuristic : Set where

aStarNameDoesNotIdentifyArtifact : PathSearchAStarMeansCADOAStar → ⊥
aStarNameDoesNotIdentifyArtifact ()

signedSSPDoesNotIdentifyGeneratorAlgebra : SignedSSPMeansGeneratorAlgebra → ⊥
signedSSPDoesNotIdentifyGeneratorAlgebra ()

equalFDoesNotEraseResidual : EqualFMeansEquivalentResidual → ⊥
equalFDoesNotEraseResidual ()

shortDescriptionDoesNotMeanShortExecution : ShortDescriptionMeansShortExecution → ⊥
shortDescriptionDoesNotMeanShortExecution ()

candidateScoreDoesNotCreateAdmissibility : CandidateScoreMeansAdmissibleHeuristic → ⊥
candidateScoreDoesNotCreateAdmissibility ()
