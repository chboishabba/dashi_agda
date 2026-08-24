module DASHI.Cognition.PNF.DreamPNFDeltaToDatabaseExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Cognition.PNF.SpacyNumericProjection as Spacy
import DASHI.Cognition.PNF.DeltaNativePNFDreamFlowExact as Delta

------------------------------------------------------------------------
-- Database as a delta sink / materialized authority projection.
--
-- The semantic compiler emits deltas from committed spaCy numeric rows.  The
-- database may accept each delta as soon as it exists.  A Python-side complete
-- semantic graph is not a required intermediate object.
------------------------------------------------------------------------

record DeltaDatabaseSink
    (Authority SemanticDelta Database : Set) : Set₁ where
  field
    deltaAlgebra : Delta.DeltaAlgebra Authority SemanticDelta
    emptyDatabase : Database
    appendDelta : Database → SemanticDelta → Database
    observeAuthority : Database → Authority

    emptyDatabaseExact :
      observeAuthority emptyDatabase
        ≡ Delta.emptyAuthority deltaAlgebra

    appendExact :
      ∀ database delta →
      observeAuthority (appendDelta database delta)
        ≡ Delta.applyDelta
            deltaAlgebra
            (observeAuthority database)
            delta

open DeltaDatabaseSink public

record SpacyDeltaDreamCompiler
    (Authority SemanticDelta Database : Set) : Set₁ where
  field
    sink : DeltaDatabaseSink Authority SemanticDelta Database
    emitTokenDelta : Spacy.NumericTokenRow → SemanticDelta

open SpacyDeltaDreamCompiler public

asDeltaNativeCompiler :
  ∀ {Authority SemanticDelta Database : Set} →
  SpacyDeltaDreamCompiler Authority SemanticDelta Database →
  Delta.DeltaNativeCompiler Spacy.NumericTokenRow Authority SemanticDelta
asDeltaNativeCompiler compiler = record
  { algebra = deltaAlgebra (sink compiler)
  ; emitDelta = emitTokenDelta compiler
  }

publishRows :
  ∀ {Authority SemanticDelta Database : Set} →
  SpacyDeltaDreamCompiler Authority SemanticDelta Database →
  Database →
  List Spacy.NumericTokenRow →
  Database
publishRows compiler database [] = database
publishRows compiler database (row ∷ rows) =
  publishRows
    compiler
    (appendDelta (sink compiler) database (emitTokenDelta compiler row))
    rows

------------------------------------------------------------------------
-- Publication correctness.
------------------------------------------------------------------------

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

publishRowsExactFrom :
  ∀ {Authority SemanticDelta Database : Set}
    (compiler : SpacyDeltaDreamCompiler Authority SemanticDelta Database)
    (database : Database)
    (rows : List Spacy.NumericTokenRow) →
  observeAuthority (sink compiler) (publishRows compiler database rows)
    ≡ Delta.applyDelta
        (deltaAlgebra (sink compiler))
        (observeAuthority (sink compiler) database)
        (Delta.compileDeltas (asDeltaNativeCompiler compiler) rows)
publishRowsExactFrom compiler database [] =
  trans
    refl
    (sym
      (Delta.applyNeutral
        (deltaAlgebra (sink compiler))
        (observeAuthority (sink compiler) database)))
  where
    sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    sym refl = refl
publishRowsExactFrom compiler database (row ∷ rows) =
  trans
    (publishRowsExactFrom
      compiler
      (appendDelta (sink compiler) database (emitTokenDelta compiler row))
      rows)
    (trans
      (cong
        (λ authority →
          Delta.applyDelta
            (deltaAlgebra (sink compiler))
            authority
            (Delta.compileDeltas (asDeltaNativeCompiler compiler) rows))
        (appendExact
          (sink compiler)
          database
          (emitTokenDelta compiler row)))
      (Delta.applyComposition
        (deltaAlgebra (sink compiler))
        (observeAuthority (sink compiler) database)
        (emitTokenDelta compiler row)
        (Delta.compileDeltas (asDeltaNativeCompiler compiler) rows)))

publishRowsExact :
  ∀ {Authority SemanticDelta Database : Set}
    (compiler : SpacyDeltaDreamCompiler Authority SemanticDelta Database)
    (rows : List Spacy.NumericTokenRow) →
  observeAuthority
    (sink compiler)
    (publishRows compiler (emptyDatabase (sink compiler)) rows)
    ≡ Delta.materialize (asDeltaNativeCompiler compiler) rows
publishRowsExact compiler rows =
  trans
    (publishRowsExactFrom compiler (emptyDatabase (sink compiler)) rows)
    (cong
      (λ authority →
        Delta.applyDelta
          (deltaAlgebra (sink compiler))
          authority
          (Delta.compileDeltas (asDeltaNativeCompiler compiler) rows))
      (emptyDatabaseExact (sink compiler)))

------------------------------------------------------------------------
-- Architecture boundaries.
------------------------------------------------------------------------

data RichPythonGraphRequiredBeforeDatabase : Set where

data WholeDocumentMustCloseBeforeFirstDatabaseDelta : Set where

data DatabaseMustSolveSemanticFibre : Set where

richPythonGraphIsNotARequiredSemanticStage :
  RichPythonGraphRequiredBeforeDatabase → ∀ {A : Set} → A
richPythonGraphIsNotARequiredSemanticStage ()

firstDeltaNeedNotWaitForWholeDocumentClose :
  WholeDocumentMustCloseBeforeFirstDatabaseDelta → ∀ {A : Set} → A
firstDeltaNeedNotWaitForWholeDocumentClose ()

databaseIsNotRequiredToBeTheSemanticSolver :
  DatabaseMustSolveSemanticFibre → ∀ {A : Set} → A
databaseIsNotRequiredToBeTheSemanticSolver ()
