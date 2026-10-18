module DASHI.Cognition.PNF.SensibLawLongDocumentPersistenceRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.PNF.SensibLawGenericSourceCompilationCanonicalWeldExact as Weld
import DASHI.Cognition.PNF.SensibLawGenericSourceCompilationCanonicalWeldRegression as Fixture
import DASHI.Cognition.PNF.SensibLawLongDocumentPersistenceExact as Persist

fixtureSourcePersistence : Persist.PersistedGenericSource Fixture.fixtureSource
fixtureSourcePersistence =
  Persist.persisted-generic-source
    refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

fixturePersistedCompilation :
  Persist.PersistedLongDocumentCompilation Fixture.fixtureSource
fixturePersistedCompilation =
  Persist.persisted-long-document-compilation
    fixtureSourcePersistence
    Fixture.fixtureLosslessReceipt
    (Weld.LosslessCompilationReceipt.assignments Fixture.fixtureLosslessReceipt)
    refl
    false refl
    false refl
    false refl
    false refl

fixtureReloadPreservesPartition :
  Persist.PersistedLongDocumentCompilation.reloadedAssignments
      fixturePersistedCompilation
  ≡ Weld.LosslessCompilationReceipt.assignments
      Fixture.fixtureLosslessReceipt
fixtureReloadPreservesPartition = refl
