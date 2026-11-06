module DASHI.Biology.Physical.BiologicalHistoryFutureQuotientExact where

------------------------------------------------------------------------
-- BIOLOGICAL HISTORY / FUTURE OBSERVATION / SPATIAL FIELD WELD
--
-- Finite abstract regression, NOT a calibrated biological transition law.
-- Genome-competence, memory, junction, environment and morphology are
-- distinct variables.  Chromatin marker is an intentionally inert coordinate
-- in this SELECTED fixture, not a claim that chromatin is biologically inert.
--
-- A coarse code that retains the causal coordinates is future-language safe,
-- although it forgets the inert marker.  Current morphology and the
-- memory-blind code are not future-language safe.  A pointwise spatial lift
-- uses the real nonperiodic ternary 3x3x3 geometry owner.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.GenericFuturePartitionRefinementExact as Refinement
import DASHI.Core.StablePartitionCanonicalFutureBridgeExact as Bridge
import DASHI.Biology.Physical.DynamicTopologyFutureDefectExact as Topology
import DASHI.Biology.Physical.FiniteMorphogeneticBasinControlExact as Basin
import DASHI.Biology.Physical.PlanarianControlCalibrationExact as Planarian
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

false≢true : false ≢ true
false≢true ()

andB : Bool → Bool → Bool
andB true b = b
andB false b = false

record BiologicalState : Set where
  constructor biologicalState
  field
    genomeCompetence : Bool
    chromatinMarker : Bool
    retainedMemory : Bool
    junctionPresent : Bool
    environmentalSupport : Bool
    visibleMorphology : Bool

open BiologicalState public

data Intervention : Set where
  signal : Intervention
  wound : Intervention
  connect : Intervention
  restoreMemory : Intervention
  provideEnvironment : Intervention

actionLabel : Intervention → String
actionLabel signal = "signal"
actionLabel wound = "wound"
actionLabel connect = "connect"
actionLabel restoreMemory = "restore-memory"
actionLabel provideEnvironment = "provide-environment"

-- Every intervention acts on a local/system state.  No inferred continuous
-- time, stochastic probability or biochemical parameter is asserted.
step : Intervention → BiologicalState → BiologicalState
step signal (biologicalState g c h j e p) =
  biologicalState g c h j e (andB g (andB h (andB j e)))
step wound (biologicalState g c h j e p) =
  biologicalState g c h j e false
step connect (biologicalState g c h j e p) =
  biologicalState g c h true e p
step restoreMemory (biologicalState g c h j e p) =
  biologicalState g c true j e p
step provideEnvironment (biologicalState g c h j e p) =
  biologicalState g c h j true p

observe : BiologicalState → Bool
observe = visibleMorphology

-- This is a strict but noninjective improvement over observing morphology
-- alone.  The omitted marker is provably irrelevant only for the fixture.
record FutureSufficientCode : Set where
  constructor futureSufficientCode
  field
    codeGenome : Bool
    codeMemory : Bool
    codeJunction : Bool
    codeEnvironment : Bool
    codeMorphology : Bool

open FutureSufficientCode public

project : BiologicalState → FutureSufficientCode
project (biologicalState g c h j e p) =
  futureSufficientCode g h j e p

coarseObserve : FutureSufficientCode → Bool
coarseObserve = codeMorphology

coarseStep : Intervention → FutureSufficientCode → FutureSufficientCode
coarseStep signal (futureSufficientCode g h j e p) =
  futureSufficientCode g h j e (andB g (andB h (andB j e)))
coarseStep wound (futureSufficientCode g h j e p) =
  futureSufficientCode g h j e false
coarseStep connect (futureSufficientCode g h j e p) =
  futureSufficientCode g h true e p
coarseStep restoreMemory (futureSufficientCode g h j e p) =
  futureSufficientCode g true j e p
coarseStep provideEnvironment (futureSufficientCode g h j e p) =
  futureSufficientCode g h j true p

projectionCommutes :
  (a : Intervention) (x : BiologicalState) →
  project (step a x) ≡ coarseStep a (project x)
projectionCommutes signal (biologicalState g c h j e p) = refl
projectionCommutes wound (biologicalState g c h j e p) = refl
projectionCommutes connect (biologicalState g c h j e p) = refl
projectionCommutes restoreMemory (biologicalState g c h j e p) = refl
projectionCommutes provideEnvironment (biologicalState g c h j e p) = refl

projectionAfterTrace :
  (actions : List Intervention) (x : BiologicalState) →
  project (Refinement.run step actions x)
  ≡ Refinement.run coarseStep actions (project x)
projectionAfterTrace [] x = refl
projectionAfterTrace (a ∷ rest) x =
  trans
    (projectionAfterTrace rest (step a x))
    (cong (Refinement.run coarseStep rest) (projectionCommutes a x))

traceAgreementFromCoarse :
  ∀ {left right} →
  project left ≡ project right →
  Bridge.TraceEquivalent observe step left right
traceAgreementFromCoarse {left} {right} same actions =
  trans
    (cong coarseObserve (projectionAfterTrace actions left))
    (trans
      (cong
        (λ code → coarseObserve (Refinement.run coarseStep actions code))
        same)
      (sym (cong coarseObserve (projectionAfterTrace actions right))))

futureSufficientCodeIsSafe :
  Future.FutureLanguageSafeProjection
    (Bridge.deterministicSystem step actionLabel)
    observe project
futureSufficientCodeIsSafe =
  Future.futureLanguageSafeProjection λ same →
    Bridge.traceEquivalentImpliesCanonicalFutureEquivalent
      (traceAgreementFromCoarse same)

-- Same genome and same present morphology, different retained state.
withoutMemory withMemory : BiologicalState
withoutMemory = biologicalState true false false true true false
withMemory = biologicalState true false true true true false

sameGenome :
  genomeCompetence withoutMemory ≡ genomeCompetence withMemory
sameGenome = refl

samePresentPhenotype : observe withoutMemory ≡ observe withMemory
samePresentPhenotype = refl

memoryDifference :
  retainedMemory withoutMemory ≢ retainedMemory withMemory
memoryDifference = false≢true

sameSignalDistinguishesFuture :
  observe (step signal withoutMemory)
  ≢ observe (step signal withMemory)
sameSignalDistinguishesFuture = false≢true

-- The proof excludes every future-safe projection which identifies these two
-- states, not merely one hand-selected implementation of the coarse code.
collisionNotFutureSafe :
  ∀ {Coarse : Set} →
  (coarsen : BiologicalState → Coarse) →
  coarsen withoutMemory ≡ coarsen withMemory →
  Future.FutureLanguageSafeProjection
    (Bridge.deterministicSystem step actionLabel)
    observe coarsen →
  ⊥
collisionNotFutureSafe coarsen same claimedSafe =
  sameSignalDistinguishesFuture
    (Bridge.canonicalFutureEquivalentImpliesTraceEquivalent
      (Future.kernelContainedInFutureEquivalence claimedSafe same)
      (signal ∷ []))

morphologyOnlyNotFutureSafe :
  Future.FutureLanguageSafeProjection
    (Bridge.deterministicSystem step actionLabel)
    observe observe →
  ⊥
morphologyOnlyNotFutureSafe =
  collisionNotFutureSafe observe samePresentPhenotype

forgetMemory :
  BiologicalState → Bool × (Bool × (Bool × Bool))
forgetMemory x =
  genomeCompetence x ,
    (junctionPresent x , (environmentalSupport x , visibleMorphology x))

memoryBlindCollision :
  forgetMemory withoutMemory ≡ forgetMemory withMemory
memoryBlindCollision = refl

memoryBlindProjectionNotFutureSafe :
  Future.FutureLanguageSafeProjection
    (Bridge.deterministicSystem step actionLabel)
    observe forgetMemory →
  ⊥
memoryBlindProjectionNotFutureSafe =
  collisionNotFutureSafe forgetMemory memoryBlindCollision

-- A genuine nontrivial safe collapse: chromatinMarker differs but every
-- admitted future morphology response is identical for this selected model.
differentMarker : BiologicalState
differentMarker = biologicalState true true false true true false

markerActuallyDiffers :
  withoutMemory ≢ differentMarker
markerActuallyDiffers same =
  false≢true (cong chromatinMarker same)

markerDoesNotChangeFutureCode :
  project withoutMemory ≡ project differentMarker
markerDoesNotChangeFutureCode = refl

markerStatesAreFutureEquivalent :
  Future.FutureObservationEquivalent
    (Bridge.deterministicSystem step actionLabel)
    observe withoutMemory differentMarker
markerStatesAreFutureEquivalent =
  Future.kernelContainedInFutureEquivalence
    futureSufficientCodeIsSafe markerDoesNotChangeFutureCode

-- Real 3 x 3 x 3 point carrier, not 27 unrelated labels.  This is a
-- pointwise lift; spatial cross-point coupling remains a separate obligation.
TissueField : Set
TissueField = Cube.Ternary27Point → BiologicalState

CoarseTissueField : Set
CoarseTissueField = Cube.Ternary27Point → FutureSufficientCode

spatialProject : TissueField → CoarseTissueField
spatialProject field point = project (field point)

pointwiseStep : Intervention → TissueField → TissueField
pointwiseStep a field point = step a (field point)

coarsePointwiseStep : Intervention → CoarseTissueField → CoarseTissueField
coarsePointwiseStep a field point = coarseStep a (field point)

spatialProjectionCommutes :
  (a : Intervention) (field : TissueField) (point : Cube.Ternary27Point) →
  spatialProject (pointwiseStep a field) point
  ≡ coarsePointwiseStep a (spatialProject field) point
spatialProjectionCommutes a field point =
  projectionCommutes a (field point)

originRetainsCubeLocation :
  (field : TissueField) →
  spatialProject field Cube.origin ≡ project (field Cube.origin)
originRetainsCubeLocation field = refl

-- General history-indexed phenotype *contract*, not an empirical inhabitant.
-- Fibres can differ at the same time under different admissible histories;
-- this does not replace the established temporal/reopenable evidence owners.
record IndexedBiologicalPhenotype : Set₁ where
  field
    Genotype Context Time History : Set
    Fibre : Genotype → Context → History → Time → Set
    Phenotype : Genotype → Context → History → Time → Set
    InterventionAt : Set
    nextHistory : History → InterventionAt → History
    nextTime : Time → Time
    observeAt :
      ∀ {g c h t} → Fibre g c h t → Phenotype g c h t
    updateAt :
      ∀ {g c h t} →
      (a : InterventionAt) →
      Fibre g c h t →
      Fibre g c (nextHistory h a) (nextTime t)

-- Exact existing donor boundaries are retained, not promoted into physical
-- measurements by the synthetic regression above.
priorTopologyCollision :
  Topology.morphologyProjection Topology.withoutJunction
  ≡ Topology.morphologyProjection Topology.withJunction
priorTopologyCollision = Topology.sameVisibleMorphology

priorBasinTwoStep :
  Basin.repair2 Basin.far ≡ Basin.target
priorBasinTwoStep = Basin.farInTwoStepBasin

priorPlanarianCount : Planarian.CountObservation
priorPlanarianCount = Planarian.hybridModelParameterSweep

record BiologicalFutureAuthorityBoundary : Set where
  constructor biologicalFutureAuthorityBoundary
  field
    selectedFixtureIsCalibratedPhysicalLaw : Bool
    calibrationClaimIsFalse :
      selectedFixtureIsCalibratedPhysicalLaw ≡ false
    pointwiseCubeImpliesSpatialCoupling : Bool
    couplingClaimIsFalse :
      pointwiseCubeImpliesSpatialCoupling ≡ false
    syntheticChromatinInvarianceIsUniversal : Bool
    chromatinClaimIsFalse :
      syntheticChromatinInvarianceIsUniversal ≡ false
    empiricalPhenotypeEquivalenceEstablished : Bool
    empiricalClaimIsFalse :
      empiricalPhenotypeEquivalenceEstablished ≡ false

canonicalBiologicalFutureBoundary : BiologicalFutureAuthorityBoundary
canonicalBiologicalFutureBoundary =
  biologicalFutureAuthorityBoundary
    false refl false refl false refl false refl
