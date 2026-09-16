module DASHI.ComputerScience.RSA260BidiProjectionIndexedGeneratorSignatureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.ComputerScience.RSA260ProjectionMatrixGeneratorExact as MatrixGenerator
import DASHI.ComputerScience.RSA260BidiProjectionFreezeObservableExact as Freeze

------------------------------------------------------------------------
-- RSA-260 BIDI PROJECTION-INDEXED GENERATOR SIGNATURE
--
-- The projection-freeze owner paid the methodological requirement that X/Y be
-- frozen before controlled cross-carrier comparison.  This owner packages the
-- realized projected degree together with the rectangular-Hankel extension
-- signature under that frozen pair.
--
-- The object is intentionally called a generator SIGNATURE.  The older matrix
-- generator owner already blocks the invalid promotion
--
--   first fitting degree -> canonical minimal generator.
--
-- We preserve that firewall here.  The new theorem is information-theoretic:
-- degree alone cannot recover the full projection-indexed signature.
------------------------------------------------------------------------

matrixGeneratorBoundary : MatrixGenerator.RSA260MatrixGeneratorRoadmapBoundary
matrixGeneratorBoundary = MatrixGenerator.currentRSA260MatrixGeneratorRoadmapBoundary

freezeBoundary : Freeze.ProjectionFreezeInterpretationBoundary
freezeBoundary = Freeze.canonicalProjectionFreezeInterpretationBoundary

record ProjectionIndexedGeneratorSignature : Set where
  constructor projection-indexed-generator-signature
  field
    observable : Freeze.ProjectionIndexedObservable
    projectionFreeze : Freeze.ProjectionPairFreezeReceipt
    degreeIsProjectionIndexed : Bool
    rectangularExtensionIsProjectionIndexed : Bool
    canonicalMinimalGeneratorProved : Bool
    productionSequenceUsed : Bool
open ProjectionIndexedGeneratorSignature public

carrier32BaselineSignature : ProjectionIndexedGeneratorSignature
carrier32BaselineSignature =
  projection-indexed-generator-signature
    Freeze.carrier32BaselineObservable
    Freeze.currentProjectionPairFreezeReceipt
    true true false false

carrier32Y3Signature : ProjectionIndexedGeneratorSignature
carrier32Y3Signature =
  projection-indexed-generator-signature
    Freeze.carrier32Y3Observable
    Freeze.currentProjectionPairFreezeReceipt
    true true false false

carrier128BaselineSignature : ProjectionIndexedGeneratorSignature
carrier128BaselineSignature =
  projection-indexed-generator-signature
    Freeze.carrier128BaselineObservable
    Freeze.currentProjectionPairFreezeReceipt
    true true false false

carrier128Y1Signature : ProjectionIndexedGeneratorSignature
carrier128Y1Signature =
  projection-indexed-generator-signature
    Freeze.carrier128Y1Observable
    Freeze.currentProjectionPairFreezeReceipt
    true true false false

------------------------------------------------------------------------
-- Exact finite obstruction.
--
-- On the touched32/271003 carrier, X0Y0 and X0Y3 both have d=22 while the
-- rectangular extension changes from left-only (1,0,1) to none (0,0,0).
-- Hence projected generator degree alone does not determine the full signature.
------------------------------------------------------------------------

data SignatureWorld : Set where
  world32X0Y0 : SignatureWorld
  world32X0Y3 : SignatureWorld

data DegreeSurface : Set where
  degree22Surface : DegreeSurface

data ProjectionIndexedSurface : Set where
  degree22X0Y0Surface : ProjectionIndexedSurface
  degree22X0Y3Surface : ProjectionIndexedSurface

data SignatureQuery : Set where
  fullProjectionIndexedGeneratorSignature : SignatureQuery

data SignatureAnswer : Set where
  degree22LeftOnly : SignatureAnswer
  degree22NoExtension : SignatureAnswer

degreeObserve : SignatureWorld → DegreeSurface
degreeObserve _ = degree22Surface

projectionIndexedObserve : SignatureWorld → ProjectionIndexedSurface
projectionIndexedObserve world32X0Y0 = degree22X0Y0Surface
projectionIndexedObserve world32X0Y3 = degree22X0Y3Surface

signatureAnswer : SignatureQuery → SignatureWorld → SignatureAnswer
signatureAnswer fullProjectionIndexedGeneratorSignature world32X0Y0 = degree22LeftOnly
signatureAnswer fullProjectionIndexedGeneratorSignature world32X0Y3 = degree22NoExtension

signatureSemantics :
  Query.QuerySemantics SignatureWorld SignatureQuery SignatureAnswer
signatureSemantics = Query.querySemantics signatureAnswer

DegreeOnlySignatureAdequacyDefect : Set₁
DegreeOnlySignatureAdequacyDefect =
  Query.QueryAdequacyDefect
    degreeObserve
    signatureSemantics
    fullProjectionIndexedGeneratorSignature

sameDegreeCanHideDifferentGeneratorSignature : DegreeOnlySignatureAdequacyDefect
sameDegreeCanHideDifferentGeneratorSignature =
  Query.queryAdequacyDefect
    world32X0Y0
    world32X0Y3
    refl
    (λ ())

degreeOnlyNotAdequateForFullSignature :
  Query.AdequateFor
    degreeObserve
    signatureSemantics
    fullProjectionIndexedGeneratorSignature → ⊥
degreeOnlyNotAdequateForFullSignature =
  Query.queryAdequacyDefectBlocksFactorisation
    sameDegreeCanHideDifferentGeneratorSignature

signatureFromProjectionIndexed : ProjectionIndexedSurface → SignatureAnswer
signatureFromProjectionIndexed degree22X0Y0Surface = degree22LeftOnly
signatureFromProjectionIndexed degree22X0Y3Surface = degree22NoExtension

projectionIndexedSignatureFactorisation :
  (world : SignatureWorld) →
  signatureAnswer fullProjectionIndexedGeneratorSignature world
    ≡ signatureFromProjectionIndexed (projectionIndexedObserve world)
projectionIndexedSignatureFactorisation world32X0Y0 = refl
projectionIndexedSignatureFactorisation world32X0Y3 = refl

ProjectionIndexedSignatureAdequacy : Set₁
ProjectionIndexedSignatureAdequacy =
  Query.AdequateFor
    projectionIndexedObserve
    signatureSemantics
    fullProjectionIndexedGeneratorSignature

signatureFactorsThroughProjectionIndexedObserver :
  ProjectionIndexedSignatureAdequacy
signatureFactorsThroughProjectionIndexedObserver =
  Query.factorsForQuery
    signatureFromProjectionIndexed
    projectionIndexedSignatureFactorisation

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

record ProjectionIndexedGeneratorBoundary : Set where
  constructor projection-indexed-generator-boundary
  field
    projectionFreezePaid : Bool
    projectedDegreePaid : Bool
    rectangularExtensionOrientationPaid : Bool
    sameDegreeDifferentSignatureWitnessPaid : Bool
    degreeAloneDeterminesFullGeneratorSignature : Bool
    projectionIndexedObserverAdequateOnFiniteWitness : Bool
    signatureIsCanonicalMinimalGenerator : Bool
    signatureIsProductionGenerator : Bool
    productionAStarAdapterPaid : Bool
    sameObjectProductionSequenceAcquired : Bool
open ProjectionIndexedGeneratorBoundary public

canonicalProjectionIndexedGeneratorBoundary : ProjectionIndexedGeneratorBoundary
canonicalProjectionIndexedGeneratorBoundary =
  projection-indexed-generator-boundary
    true
    true
    true
    true
    false
    true
    false
    false
    false
    false

------------------------------------------------------------------------
-- The next high-alpha step is no longer another synthetic scalar predictor.
-- It is the adapter from authentic projected-sequence custody into this packet.
------------------------------------------------------------------------

data ProjectionIndexedGeneratorResidual : Set where
  liftProjectionIndexedDiagnosticsToProductionAStar : ProjectionIndexedGeneratorResidual
  acquireSameObjectProjectedAStarOrFSols : ProjectionIndexedGeneratorResidual
  recoverProjectionPairForReproductionAndControlledComparison : ProjectionIndexedGeneratorResidual
  characterizeProjectionGeometryCreatingDegreeShift : ProjectionIndexedGeneratorResidual
  characterizeProjectionGeometryCreatingOrientationShift : ProjectionIndexedGeneratorResidual
  deriveCanonicalMinimalGeneratorOnlyIfAdditionalAlgebraPays : ProjectionIndexedGeneratorResidual

firstProjectionIndexedGeneratorResidual : ProjectionIndexedGeneratorResidual
firstProjectionIndexedGeneratorResidual =
  liftProjectionIndexedDiagnosticsToProductionAStar

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data DegreeMeansFullGeneratorSignature : Set where
data ProjectionIndexedSignatureMeansCanonicalMinimalGenerator : Set where
data SyntheticSignatureMeansProductionGenerator : Set where
data ProjectionFreezeMeansSameObjectSequenceCustody : Set where

degreeDoesNotCreateFullSignature : DegreeMeansFullGeneratorSignature → ⊥
degreeDoesNotCreateFullSignature ()

signatureDoesNotCreateCanonicalMinimalGenerator :
  ProjectionIndexedSignatureMeansCanonicalMinimalGenerator → ⊥
signatureDoesNotCreateCanonicalMinimalGenerator ()

syntheticSignatureDoesNotCreateProductionGenerator :
  SyntheticSignatureMeansProductionGenerator → ⊥
syntheticSignatureDoesNotCreateProductionGenerator ()

projectionFreezeDoesNotCreateSequenceCustody :
  ProjectionFreezeMeansSameObjectSequenceCustody → ⊥
projectionFreezeDoesNotCreateSequenceCustody ()
