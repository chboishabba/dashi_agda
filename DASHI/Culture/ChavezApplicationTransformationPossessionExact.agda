module DASHI.Culture.ChavezApplicationTransformationPossessionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Core.ApplicationTransformationCapabilityBidiExact as T

data PossessionStatus : Set where sourceBacked partial notLocated : PossessionStatus
record ApplicationRoleReceipt : Set where
  constructor application-role-receipt
  field roleOrPerson : String; transformationCoordinates : List T.TransformationCoordinate; status : PossessionStatus; sourceReference : String; boundedReading : String
open ApplicationRoleReceipt public

chavezDARHTScorpiusRole : ApplicationRoleReceipt
chavezDARHTScorpiusRole = application-role-receipt "Anthony Chavez"
  (T.applicationGeometry ∷ T.calibrationState ∷ T.sourceOrAlgorithmImplementation ∷ T.integrationWorkflow ∷ []) sourceBacked
  "LANL National Security Science Summer 2025 Anthony Chavez profile; DOI 10.1063/1.5029837; LA-UR-24-27763"
  "LANL reports more than 25 years at DARHT and Scorpius design work; coauthored instrumentation/calibration work supports application engineering and diagnostic-calibration involvement."

chavezInverseModelOwnership : ApplicationRoleReceipt
chavezInverseModelOwnership = application-role-receipt "Anthony Chavez"
  (T.closureOrRegularisation ∷ T.uncertaintyModel ∷ T.validationCorpus ∷ []) notLocated
  "bounded public LANL search"
  "No source located here establishes ownership of the experiment-specific hydrodynamic forward/inverse model, reconstruction priors, classified experiment geometry, or uncertainty model."

record ChavezApplicationBoundary : Set where
  constructor chavez-application-boundary
  field longDARHTTenureImpliesUniqueHolder : Bool; longDARHTTenureImpliesUniqueHolderIsFalse : longDARHTTenureImpliesUniqueHolder ≡ false; calibrationCoauthorshipImpliesInverseModelOwnership : Bool; calibrationCoauthorshipImpliesInverseModelOwnershipIsFalse : calibrationCoauthorshipImpliesInverseModelOwnership ≡ false; applicationEngineeringRoleSourceBacked : Bool; applicationEngineeringRoleSourceBackedIsTrue : applicationEngineeringRoleSourceBacked ≡ true; uniqueReplacementDifficultyClosed : Bool; uniqueReplacementDifficultyClosedIsFalse : uniqueReplacementDifficultyClosed ≡ false
canonicalChavezApplicationBoundary = chavez-application-boundary false refl false refl true refl false refl

data ChavezApplicationReverseTarget : Set where acquireExactScorpiusDesignAssignments acquireDiagnosticCalibrationOwnership acquireConfigurationManagementHistory acquireSuccessorOrHandover acquireExperimentSpecificInverseModelRole acquireReplacementDelayOrRework : ChavezApplicationReverseTarget
