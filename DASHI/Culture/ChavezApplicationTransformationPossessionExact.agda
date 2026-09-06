module DASHI.Culture.ChavezApplicationTransformationPossessionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ApplicationTransformationCapabilityBidiExact as T

------------------------------------------------------------------------
-- ANTHONY CHAVEZ: APPLICATION-TRANSFORMATION POSSESSION RECEIPTS
--
-- Sources:
-- Los Alamos National Laboratory, National Security Science, Summer 2025,
-- profile "Anthony Chavez — Engineering, Operations, and Physics".
-- T. J. Burris-Mog et al., "Calibration of two compact permanent magnet
-- spectrometers for high current electron linear induction accelerators",
-- Rev. Sci. Instrum. 89, 073303 (2018), DOI 10.1063/1.5029837.
-- C. Ekdahl et al., "An Improved Beam Position Monitor for Scorpius and the
-- DARHT Multi-Pulse Test Line", LA-UR-24-27763 (2024).
------------------------------------------------------------------------

data PossessionStatus : Set where
  sourceBacked
  partial
  notLocated
  : PossessionStatus

record ApplicationRoleReceipt : Set where
  constructor application-role-receipt
  field
    roleOrPerson : String
    transformationCoordinates : List T.TransformationCoordinate
    status : PossessionStatus
    sourceReference : String
    boundedReading : String

open ApplicationRoleReceipt public

chavezDARHTScorpiusRole : ApplicationRoleReceipt
chavezDARHTScorpiusRole = application-role-receipt
  "Anthony Chavez"
  (T.applicationGeometry ∷ T.calibrationState ∷ T.sourceOrAlgorithmImplementation ∷ T.integrationWorkflow ∷ [])
  sourceBacked
  "LANL National Security Science Summer 2025 Anthony Chavez profile; DOI 10.1063/1.5029837; LA-UR-24-27763"
  "LANL reports >25 years at DARHT and Scorpius design work; coauthored instrumentation/calibration work supports application engineering and diagnostic-calibration involvement."

chavezInverseModelOwnership : ApplicationRoleReceipt
chavezInverseModelOwnership = application-role-receipt
  "Anthony Chavez"
  (T.closureOrRegularisation ∷ T.uncertaintyModel ∷ T.validationCorpus ∷ [])
  notLocated
  "current bounded public search through LANL profile/publications"
  "No source located in this pass establishes ownership of the experiment-specific hydrodynamic forward/inverse model, reconstruction priors, classified experiment geometry, or uncertainty model."

record ChavezApplicationBoundary : Set where
  constructor chavez-application-boundary
  field
    longDARHTTenureImpliesUniqueHolder : Bool
    longDARHTTenureImpliesUniqueHolderIsFalse : longDARHTTenureImpliesUniqueHolder ≡ false
    calibrationCoauthorshipImpliesInverseModelOwnership : Bool
    calibrationCoauthorshipImpliesInverseModelOwnershipIsFalse : calibrationCoauthorshipImpliesInverseModelOwnership ≡ false
    applicationEngineeringRoleSourceBacked : Bool
    applicationEngineeringRoleSourceBackedIsTrue : applicationEngineeringRoleSourceBacked ≡ true
    uniqueReplacementDifficultyClosed : Bool
    uniqueReplacementDifficultyClosedIsFalse : uniqueReplacementDifficultyClosed ≡ false

canonicalChavezApplicationBoundary : ChavezApplicationBoundary
canonicalChavezApplicationBoundary = chavez-application-boundary false refl false refl true refl false refl

data ChavezApplicationReverseTarget : Set where
  acquireExactScorpiusDesignAssignments
  acquireDiagnosticCalibrationOwnership
  acquireConfigurationManagementHistory
  acquireSuccessorOrHandover
  acquireExperimentSpecificInverseModelRole
  acquireReplacementDelayOrRework
  : ChavezApplicationReverseTarget
