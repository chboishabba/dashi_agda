module DASHI.Law.SensibLawExpertEvidenceSourceGenealogyRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawExpertEvidenceProductionIntegrityExact as Expert
import DASHI.Core.ObserverRefinementLatticeExact as Observer

------------------------------------------------------------------------
-- Provenance-independence cross-pollination regression.
--
-- Agreement / multiplicity of expert reports must not manufacture source
-- independence. Joining the source-genealogy axis must be an explicit observer
-- refinement rather than an implicit re-interpretation of the same report count.
------------------------------------------------------------------------

sourceIndependenceDefectIsPresent : Expert.SourceIndependenceQueryAdequacyDefect
sourceIndependenceDefectIsPresent = Expert.sourceIndependenceQueryAdequacyDefect

sourceIndependenceCannotFactorThroughAgreement :
  Expert.SourceIndependenceQueryAdequate → ⊥
sourceIndependenceCannotFactorThroughAgreement =
  Expert.sourceIndependenceQueryNotAdequate

joinedSourceGenealogyRefinesAgreement :
  Observer.Refines
    Expert.reportAgreementSurface
    Expert.reportAgreementPlusGenealogy
joinedSourceGenealogyRefinesAgreement =
  Expert.reportAgreementPlusGenealogyRefinesAgreement

joinedSourceGenealogyIsStrictRepair :
  Observer.StrictRefinement
    Expert.reportAgreementSurface
    Expert.reportAgreementPlusGenealogy
joinedSourceGenealogyIsStrictRepair =
  Expert.reportAgreementPlusGenealogyStrictRefinement

multipleReportsDoNotCreateIndependence :
  Expert.MultipleReportsAutomaticallyIndependent → ⊥
multipleReportsDoNotCreateIndependence =
  Expert.multipleReportsDoNotAutomaticallyCreateIndependence

agreementDoesNotCreateIndependentCorroboration :
  Expert.AgreementAutomaticallyIndependentCorroboration → ⊥
agreementDoesNotCreateIndependentCorroboration =
  Expert.agreementDoesNotAutomaticallyCreateIndependentCorroboration

dependenceDoesNotEraseAllEvidence :
  Expert.DependenceMeansNoEvidence → ⊥
dependenceDoesNotEraseAllEvidence =
  Expert.dependenceDoesNotMeanNoEvidence
