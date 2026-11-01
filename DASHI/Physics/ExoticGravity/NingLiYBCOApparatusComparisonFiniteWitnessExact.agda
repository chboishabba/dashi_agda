module DASHI.Physics.ExoticGravity.NingLiYBCOApparatusComparisonFiniteWitnessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.NingLiYBCOGravityConstraintBidiExact as Static
import DASHI.Physics.ExoticGravity.NingLiYBCORotatingFieldConstraintExact as Rotating

record FiniteNingApparatusWitness : Set where
  constructor finite-ning-apparatus-witness
  field
    staticSource : String
    rotatingSource : String
    staticConfiguration : String
    staticBound : String
    rotatingConfiguration : String
    rotatingRate : String
    rotatingFieldProfile : String
    staticPositiveEffectObserved : Bool
    rotatingPositiveEffectObserved : Bool
    sameApparatusObject : Bool
    sameProgrammeLineage : Bool
    laterArmyContinuityPaid : Bool
    nextExactLeaf : String

open FiniteNingApparatusWitness public

finiteNingApparatusWitness : FiniteNingApparatusWitness
finiteNingApparatusWitness = finite-ning-apparatus-witness
  "DOI 10.1016/S0921-4534(97)01462-7"
  "NASA NTRS 19990019627 / AIAA-98-3139"
  (Static.NingLiYBCOConstraintReceipt.configuration Static.staticYBCO1997Constraint)
  Static.lessThanTwoPartsIn100MillionG
  (Rotating.RotatingFieldYBCOExperiment.driveGeometry Rotating.canonicalRotatingFieldExperiment)
  (Rotating.RotatingFieldYBCOExperiment.rotatingFieldRate Rotating.canonicalRotatingFieldExperiment)
  (Rotating.RotatingFieldYBCOExperiment.magneticFieldProfile Rotating.canonicalRotatingFieldExperiment)
  false
  false
  false
  true
  false
  "recover source-exact geometry/control differences and any later AC Gravity apparatus receipt before asserting continuity into the Army programme"

finiteComparisonIsSourceExact : Bool
finiteComparisonIsSourceExact = true

finiteComparisonPaysPositiveAntigravity : Bool
finiteComparisonPaysPositiveAntigravity = false

finiteComparisonPaysArmyProgrammeContinuity : Bool
finiteComparisonPaysArmyProgrammeContinuity = false
