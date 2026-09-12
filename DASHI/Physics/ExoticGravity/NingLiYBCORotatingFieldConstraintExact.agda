module DASHI.Physics.ExoticGravity.NingLiYBCORotatingFieldConstraintExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as A
import DASHI.Physics.ExoticGravity.NingLiYBCOGravityConstraintBidiExact as Static

------------------------------------------------------------------------
-- ROTATING-FIELD YBCO CONSTRAINT IN THE LI/NOEVER/KOCZOR PROGRAMME LINEAGE
--
-- This is not a Ning Li authored paper.  It is retained because it tests a
-- changed regime immediately downstream of the 1997 static YBCO constraint:
-- large bulk YBCO in a three-phase AC motor stator with rotating magnetic
-- field, with/without DC levitation.  NASA NTRS reports no rotating-field or
-- thermal-environment effect within the precision of the observation.
------------------------------------------------------------------------

ntrs19990019627 : A.AttributedSource
ntrs19990019627 = A.mkNoDOISource
  "David A. Noever; Ronald J. Koczor; Rick Roberson"
  "Superconductor-Mediated Modification of Gravity? AC Motor Experiments with Bulk YBCO Disks in Rotating Magnetic Fields"
  "NASA Technical Reports Server reprint; AIAA-98-3139"
  "1998"
  "https://ntrs.nasa.gov/citations/19990019627"
  A.governmentSource
  "primary NASA bibliographic/abstract carrier for a changed-regime YBCO gravimeter experiment; supports apparatus coordinates and a null/no-observed-effect statement for rotating-field and thermal-environment variations; does not establish anomalous gravity or the later Army programme"
  A.publicAttribution

record RotatingFieldYBCOExperiment : Set where
  constructor rotating-field-ybco-experiment
  field
    ntrsDocumentId : String
    conferenceIdentifier : String
    acquisitionSource : String
    diskDescription : String
    driveGeometry : String
    rotatingFieldRate : String
    magneticFieldProfile : String
    dcLevitationVariants : String
    reportedGravityReading : String
    rotatingFieldEffectObserved : Bool
    thermalEnvironmentEffectObserved : Bool
    sameObjectAs1997StaticConfiguration : Bool
    sameProgrammeLineageAsStaticConstraint : Bool
    sourceReference : String

open RotatingFieldYBCOExperiment public

canonicalRotatingFieldExperiment : RotatingFieldYBCOExperiment
canonicalRotatingFieldExperiment = rotating-field-ybco-experiment
  "19990019627"
  "AIAA-98-3139"
  "NASA Marshall Space Flight Center"
  "large bulk-processed YBCO ceramic superconductors; approximately 15 cm diameter in the reported experiment"
  "three-phase AC motor stator producing a rotating magnetic field"
  "up to 12000 rpm rotating-field rate as reported by NTRS"
  "less than 60 gauss near outer diameter and less than 10 gauss near centre as reported"
  "tested with and without permanent-DC-field levitation of the superconducting disk"
  "apparent gravity-reading change remained below the small reported bound; NTRS states no effect of rotating magnetic field or thermal environment was noted within observation precision"
  false
  false
  false
  true
  "NASA NTRS 19990019627; publication date 1998-01-01; Noever/Koczor/Roberson"

existingStaticBoundary : Static.NingLiConstraintBoundary
existingStaticBoundary = Static.canonicalNingLiConstraintBoundary

record RotatingFieldConstraintBoundary : Set where
  constructor rotating-field-constraint-boundary
  field
    changedDriveRegimeEscapesNeedToCompareAgainstStaticConstraint : Bool
    rotatingFieldPaysPositiveGravityEffect : Bool
    noObservedEffectProvesEveryDynamicVariantImpossible : Bool
    apparatusChangeMayRefineProofSearch : Bool
    laterArmyProgrammeAutomaticallySameObject : Bool

canonicalRotatingFieldConstraintBoundary : RotatingFieldConstraintBoundary
canonicalRotatingFieldConstraintBoundary = rotating-field-constraint-boundary
  false false false true false

rotatingFieldPaysPositiveGravityEffect : Bool
rotatingFieldPaysPositiveGravityEffect = false

staticToRotatingFieldIsChangedRegime : Bool
staticToRotatingFieldIsChangedRegime = true

nasaRotatingFieldDoesNotPayArmyOutcome : Bool
nasaRotatingFieldDoesNotPayArmyOutcome = true
