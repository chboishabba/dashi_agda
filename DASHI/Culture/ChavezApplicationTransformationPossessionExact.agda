module DASHI.Culture.ChavezApplicationTransformationPossessionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Core.ApplicationTransformationCapabilityBidiExact as T

data PossessionStatus : Set where sourceBacked partial notLocated : PossessionStatus
record ApplicationRoleReceipt : Set where
  constructor application-role-receipt
  field roleOrPerson : String; transformationCoordinates : List T.TransformationCoordinate; status : PossessionStatus; sourceReference : String; boundedReading : String
open ApplicationRoleReceipt public

markAnthonyChavezDARHTScorpiusRole : ApplicationRoleReceipt
markAnthonyChavezDARHTScorpiusRole = application-role-receipt "Mark Anthony Chavez"
  (T.applicationGeometry ∷ T.calibrationState ∷ T.sourceOrAlgorithmImplementation ∷ T.integrationWorkflow ∷ []) sourceBacked
  "LANL National Security Science Summer 2025 Anthony Chavez profile; Burris-Mog et al. DOI 10.1063/1.5029837; LA-UR-24-27763"
  "LANL technical sources support a DARHT/Scorpius application-engineering role for Mark Anthony Chavez. DOI 10.1063/1.5029837 and LA-UR-24-27763 explicitly name Mark Anthony Chavez."

missingAnthonyChavezDARHTScorpiusRole : ApplicationRoleReceipt
missingAnthonyChavezDARHTScorpiusRole = application-role-receipt "Anthony Chavez, missing Los Alamos resident born 1947-01-07"
  (T.applicationGeometry ∷ T.calibrationState ∷ T.sourceOrAlgorithmImplementation ∷ T.integrationWorkflow ∷ []) notLocated
  "New Mexico DPS missing-person record M99969; Los Alamos County 2025 missing-person release; DARHT/Scorpius technical sources name Mark Anthony Chavez"
  "No same-person receipt currently connects the missing 78-year-old Anthony Chavez to the Mark Anthony Chavez DARHT/Scorpius engineering publications. Do not inherit those technical roles by name similarity."

-- Compatibility name retained, now pointing to the bounded missing-person row.
chavezDARHTScorpiusRole : ApplicationRoleReceipt
chavezDARHTScorpiusRole = missingAnthonyChavezDARHTScorpiusRole

chavezInverseModelOwnership : ApplicationRoleReceipt
chavezInverseModelOwnership = application-role-receipt "Anthony Chavez, missing Los Alamos resident born 1947-01-07"
  (T.closureOrRegularisation ∷ T.uncertaintyModel ∷ T.validationCorpus ∷ []) notLocated
  "bounded public identity and technical-source search"
  "No source located establishes that the missing Anthony Chavez owned an experiment-specific hydrodynamic forward/inverse model, reconstruction priors, classified experiment geometry, or uncertainty model."

record ChavezApplicationBoundary : Set where
  constructor chavez-application-boundary
  field longDARHTTenureImpliesUniqueHolder : Bool; longDARHTTenureImpliesUniqueHolderIsFalse : longDARHTTenureImpliesUniqueHolder ≡ false; calibrationCoauthorshipImpliesInverseModelOwnership : Bool; calibrationCoauthorshipImpliesInverseModelOwnershipIsFalse : calibrationCoauthorshipImpliesInverseModelOwnership ≡ false; missingAnthonyApplicationEngineeringRoleClosed : Bool; missingAnthonyApplicationEngineeringRoleClosedIsFalse : missingAnthonyApplicationEngineeringRoleClosed ≡ false; sameNameImpliesSamePerson : Bool; sameNameImpliesSamePersonIsFalse : sameNameImpliesSamePerson ≡ false; uniqueReplacementDifficultyClosed : Bool; uniqueReplacementDifficultyClosedIsFalse : uniqueReplacementDifficultyClosed ≡ false
canonicalChavezApplicationBoundary = chavez-application-boundary false refl false refl false refl false refl false refl

data ChavezApplicationReverseTarget : Set where acquireSamePersonIdentityReceipt acquireMissingAnthonyExactLANLRole acquireExactScorpiusDesignAssignments acquireDiagnosticCalibrationOwnership acquireConfigurationManagementHistory acquireSuccessorOrHandover acquireExperimentSpecificInverseModelRole acquireReplacementDelayOrRework : ChavezApplicationReverseTarget
