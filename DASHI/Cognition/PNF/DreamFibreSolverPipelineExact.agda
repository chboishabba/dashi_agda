module DASHI.Cognition.PNF.DreamFibreSolverPipelineExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Cognition.PNF.SpacyNumericProjection as Spacy
import DASHI.Cognition.PNF.DeltaNativePNFDreamFlowExact as Delta
import DASHI.Cognition.PNF.FibreSolverDeltaStreamExact as Solver
import DASHI.Cognition.PNF.DreamPNFDeltaToDatabaseExact as Database

------------------------------------------------------------------------
-- Full dream composition:
--
-- spaCy committed numeric row
--   -> fibre-local solver
--   -> semantic delta + residual/commitment/alternatives
--   -> delta sink / DB authority projection.
------------------------------------------------------------------------

record DreamFibreSolverPipeline
    (Fibre SemanticDelta Candidate Authority Database : Set) : Set₁ where
  field
    solver :
      Solver.FibreLocalSolver
        Spacy.NumericTokenRow Fibre SemanticDelta Candidate
    sink : Database.DeltaDatabaseSink Authority SemanticDelta Database

open DreamFibreSolverPipeline public

emitSolvedDelta :
  ∀ {Fibre SemanticDelta Candidate Authority Database : Set} →
  DreamFibreSolverPipeline Fibre SemanticDelta Candidate Authority Database →
  Spacy.NumericTokenRow → SemanticDelta
emitSolvedDelta pipeline row =
  Solver.semanticDelta
    (Solver.solveEvent (solver pipeline) row)

asDatabaseCompiler :
  ∀ {Fibre SemanticDelta Candidate Authority Database : Set} →
  DreamFibreSolverPipeline Fibre SemanticDelta Candidate Authority Database →
  Database.SpacyDeltaDreamCompiler Authority SemanticDelta Database
asDatabaseCompiler pipeline = record
  { sink = sink pipeline
  ; emitTokenDelta = emitSolvedDelta pipeline
  }

runDreamPipeline :
  ∀ {Fibre SemanticDelta Candidate Authority Database : Set} →
  DreamFibreSolverPipeline Fibre SemanticDelta Candidate Authority Database →
  List Spacy.NumericTokenRow → Database
runDreamPipeline pipeline rows =
  Database.publishRows
    (asDatabaseCompiler pipeline)
    (Database.emptyDatabase (sink pipeline))
    rows

dreamPipelineExact :
  ∀ {Fibre SemanticDelta Candidate Authority Database : Set}
    (pipeline : DreamFibreSolverPipeline
      Fibre SemanticDelta Candidate Authority Database)
    (rows : List Spacy.NumericTokenRow) →
  Database.observeAuthority
    (sink pipeline)
    (runDreamPipeline pipeline rows)
    ≡ Delta.materialize
        (Database.asDeltaNativeCompiler (asDatabaseCompiler pipeline))
        rows
dreamPipelineExact pipeline rows =
  Database.publishRowsExact (asDatabaseCompiler pipeline) rows

------------------------------------------------------------------------
-- Residual stream remains available alongside committed semantic deltas.
------------------------------------------------------------------------

solveRows :
  ∀ {Fibre SemanticDelta Candidate Authority Database : Set} →
  DreamFibreSolverPipeline Fibre SemanticDelta Candidate Authority Database →
  List Spacy.NumericTokenRow →
  List (Solver.SolverEmission SemanticDelta Candidate)
solveRows pipeline [] = []
solveRows pipeline (row ∷ rows) =
  Solver.solveEvent (solver pipeline) row ∷ solveRows pipeline rows

------------------------------------------------------------------------
-- A special initial/bootstrap path must earn its keep.
--
-- Semantic equality is necessary but insufficient: a second physical path is
-- justified only when it also carries an explicit work-order witness.
------------------------------------------------------------------------

record BootstrapSpecialisation
    (Fibre SemanticDelta Candidate Authority Database Work : Set)
    (_≤W_ : Work → Work → Set)
    (pipeline : DreamFibreSolverPipeline
      Fibre SemanticDelta Candidate Authority Database)
    : Set₁ where
  field
    bootstrap : List Spacy.NumericTokenRow → Authority
    bootstrapWork : List Spacy.NumericTokenRow → Work
    deltaNativeWork : List Spacy.NumericTokenRow → Work

    bootstrapSemanticExact :
      ∀ rows →
      bootstrap rows
        ≡ Delta.materialize
            (Database.asDeltaNativeCompiler (asDatabaseCompiler pipeline))
            rows

    bootstrapActuallyCheaper :
      ∀ rows → bootstrapWork rows ≤W deltaNativeWork rows

open BootstrapSpecialisation public

data BootstrapSpecialCaseWithoutEvidence : Set where

bootstrapSpecialCaseMustEarnItsKeep :
  BootstrapSpecialCaseWithoutEvidence → ∀ {A : Set} → A
bootstrapSpecialCaseMustEarnItsKeep ()

------------------------------------------------------------------------
-- Work locality: the declared ordinary-path work folds from per-row/local-fibre
-- work.  Accumulated authority size is not an argument to localWork.
------------------------------------------------------------------------

record StreamingWorkConstitution (Work : Set) : Set₁ where
  field
    zeroWork : Work
    combineWork : Work → Work → Work
    localWork : Spacy.NumericTokenRow → Work
    combineAssociative : ∀ a b c →
      combineWork (combineWork a b) c
        ≡ combineWork a (combineWork b c)

open StreamingWorkConstitution public

streamWork :
  ∀ {Work : Set} →
  StreamingWorkConstitution Work →
  List Spacy.NumericTokenRow → Work
streamWork work [] = zeroWork work
streamWork work (row ∷ rows) =
  combineWork work (localWork work row) (streamWork work rows)

data AccumulatedAuthoritySizeIsRequiredLocalWorkInput : Set where

localWorkNeedNotDependOnAccumulatedAuthoritySize :
  AccumulatedAuthoritySizeIsRequiredLocalWorkInput → ∀ {A : Set} → A
localWorkNeedNotDependOnAccumulatedAuthoritySize ()
