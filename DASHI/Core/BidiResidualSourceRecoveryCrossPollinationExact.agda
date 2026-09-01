module DASHI.Core.BidiResidualSourceRecoveryCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Core.CostedResidualInformationChoiceExact as Costed
import DASHI.Core.SourceAcquisitionGeometryExact as Source

------------------------------------------------------------------------
-- SOURCE RECOVERY AS RESIDUAL-FIBRE REFINEMENT
--
-- Bibliographic metadata, access routes, partial previews, acquired texts,
-- inspected texts, and extracted transcriptions can each reduce uncertainty.
-- Partial acquisition progress is useful without being promoted to full source
-- inspection or theorem/statement correspondence.
------------------------------------------------------------------------

record SourceRecoveryResidualMove (CandidateSource : Set) : Set₁ where
  constructor sourceRecoveryResidualMove
  field
    target : Source.SourceAcquisitionTarget
    prior : Bidi.ResidualFibre CandidateSource
    posterior : Bidi.ResidualFibre CandidateSource
    refinement : Bidi.FibreRefines posterior prior
    cost : Nat
    certifiedGain : Nat
    routeReference : String
    acquisitionEvidenceReference : String
    gainCertificateReference : String
    unresolvedSourceReference : String

open SourceRecoveryResidualMove public

asResidualInformationMove :
  ∀ {CandidateSource} →
  SourceRecoveryResidualMove CandidateSource →
  Costed.ResidualInformationMove CandidateSource
asResidualInformationMove move = Costed.residualInformationMove
  (prior move)
  (posterior move)
  (refinement move)
  Costed.sourceRecoveryResidualMove
  (cost move)
  (certifiedGain move)
  "provenance-aware source-recovery information move"
  (gainCertificateReference move)
  (acquisitionEvidenceReference move)
  (routeReference move)
  (unresolvedSourceReference move)

------------------------------------------------------------------------
-- Acquisition progress grades remain constructor-distinct.
------------------------------------------------------------------------

data SourceRecoveryGrade : Set where
  routeLocated
  textAcquired
  primaryTextInspected
  transcriptionRecovered
  statementCorrespondenceChecked
  : SourceRecoveryGrade

routeNotInspection : routeLocated ≡ primaryTextInspected → ⊥
routeNotInspection ()

acquisitionNotCorrespondence : textAcquired ≡ statementCorrespondenceChecked → ⊥
acquisitionNotCorrespondence ()

inspectionNotCorrespondence : primaryTextInspected ≡ statementCorrespondenceChecked → ⊥
inspectionNotCorrespondence ()

record BidiResidualSourceRecoveryBoundary : Set where
  constructor bidiResidualSourceRecoveryBoundary
  field
    locatingAccessRouteMayReduceSourceUncertainty : Bool
    locatingAccessRouteMayReduceSourceUncertaintyIsTrue :
      locatingAccessRouteMayReduceSourceUncertainty ≡ true
    residualSourceNarrowingEqualsPrimaryInspection : Bool
    residualSourceNarrowingEqualsPrimaryInspectionIsFalse :
      residualSourceNarrowingEqualsPrimaryInspection ≡ false
    acquiredTextAutomaticallyChecksStatementCorrespondence : Bool
    acquiredTextAutomaticallyChecksStatementCorrespondenceIsFalse :
      acquiredTextAutomaticallyChecksStatementCorrespondence ≡ false
    sourceRecoveryCanShareCostProgressObjectiveWithExperimentsAndProofSearch : Bool
    sourceRecoveryCanShareCostProgressObjectiveWithExperimentsAndProofSearchIsTrue :
      sourceRecoveryCanShareCostProgressObjectiveWithExperimentsAndProofSearch ≡ true

canonicalBidiResidualSourceRecoveryBoundary : BidiResidualSourceRecoveryBoundary
canonicalBidiResidualSourceRecoveryBoundary =
  bidiResidualSourceRecoveryBoundary true refl false refl false refl true refl
