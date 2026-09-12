module DASHI.Astronomy.McConnachie2012FrameDerivationExact where

open import DASHI.Core.Prelude
open import DASHI.Astronomy.LocalGroupObservationFrameProvenanceExact
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- McConnachie (2012) Table 2 derivation semantics.
--
-- This module formalises the source-described dependency graph without
-- pretending that the exact Virtual Observatory numerical producer has been
-- acquired.  The paper states that Table 2 columns 5--6 are distance modulus
-- and heliocentric distance, while columns 8--10 are distance/velocity pairs
-- in the Galactocentric (MW), M31 and Local Group frames.
------------------------------------------------------------------------

data DistanceFrame : Set where
  heliocentricFrame : DistanceFrame
  galactocentricMWFrame : DistanceFrame
  m31CentricFrame : DistanceFrame
  localGroupFrame : DistanceFrame

record SourceFrameAssumption : Set where
  constructor sourceFrameAssumption
  field
    label : String
    valueText : String
    sourceRole : String

open SourceFrameAssumption public

m31DistanceModulusAssumption : SourceFrameAssumption
m31DistanceModulusAssumption =
  sourceFrameAssumption
    "M31 distance modulus"
    "(m-M)_0 = 24.47"
    "used by McConnachie (2012) in constructing the Local Group barycentre"

localGroupMidpointAssumption : SourceFrameAssumption
localGroupMidpointAssumption =
  sourceFrameAssumption
    "Local Group barycentre"
    "mid-point of the vector connecting the MW and M31"
    "explicit simplifying equal-mass construction in McConnachie (2012), not a directly measured barycentre"

galacticRotationAssumption : SourceFrameAssumption
galacticRotationAssumption =
  sourceFrameAssumption
    "Galactic rotation at Sun"
    "220 km/s at radius 8.5 kpc"
    "adopted for Galactocentric distances/velocities in McConnachie (2012)"

localGroupSolarApexAssumption : SourceFrameAssumption
localGroupSolarApexAssumption =
  sourceFrameAssumption
    "Local Group velocity correction"
    "Solar Apex from Karachentsev & Makarov (1996)"
    "used to convert heliocentric velocities to the Local Group frame"

record DistanceDerivation : Set where
  constructor distanceDerivation
  field
    outputFrame : DistanceFrame
    inputDescription : String
    construction : String
    directlyMeasured : Bool
    sourceBound : Bool

open DistanceDerivation public

heliocentricDistanceDerivation : DistanceDerivation
heliocentricDistanceDerivation =
  distanceDerivation
    heliocentricFrame
    "distance modulus from resolved-stellar-population analysis"
    "distance obtained from the published distance modulus"
    false
    true

mwDistanceDerivation : DistanceDerivation
mwDistanceDerivation =
  distanceDerivation
    galactocentricMWFrame
    "sky position + heliocentric distance + adopted Sun/Galactic-centre geometry"
    "Euclidean separation after transformation into the adopted Galactocentric frame"
    false
    true

m31DistanceDerivation : DistanceDerivation
m31DistanceDerivation =
  distanceDerivation
    m31CentricFrame
    "sky position + heliocentric distance + adopted M31 position/distance"
    "Euclidean separation from M31 in the same reconstructed spatial frame"
    false
    true

localGroupDistanceDerivation : DistanceDerivation
localGroupDistanceDerivation =
  distanceDerivation
    localGroupFrame
    "sky position + heliocentric distance + midpoint barycentre construction"
    "Euclidean separation from the model Local Group midpoint"
    false
    true

------------------------------------------------------------------------
-- Exact formula identities are represented as source equations/textual
-- contracts until a unit-safe real-number layer is welded in.
------------------------------------------------------------------------

record FormulaContract : Set where
  constructor formulaContract
  field
    formulaName : String
    formulaText : String
    domainRestriction : String
    sourceStatus : String

open FormulaContract public

distanceModulusToDistance : FormulaContract
distanceModulusToDistance =
  formulaContract
    "distance modulus to heliocentric distance"
    "d_pc = 10^((mu + 5)/5); equivalently d_kpc = 10^((mu - 10)/5)"
    "mu is extinction-corrected distance modulus (m-M)_0"
    "standard astronomical relation; McConnachie tabulates both modulus and heliocentric distance"

cartesianSeparation : FormulaContract
cartesianSeparation =
  formulaContract
    "Euclidean frame separation"
    "D(A,B) = sqrt((xA-xB)^2 + (yA-yB)^2 + (zA-zB)^2)"
    "A and B must be represented in the same coordinate frame and length unit"
    "generic geometry used to express the three frame-relative distance derivations"

midpointBarycentre : FormulaContract
midpointBarycentre =
  formulaContract
    "equal-mass MW-M31 midpoint"
    "R_LG = (R_MW + R_M31)/2"
    "encodes McConnachie 2012's simplifying midpoint assumption, not a modern mass-weighted inference"
    "source-described model construction"

------------------------------------------------------------------------
-- Three derived-distance columns in the first-light claim.
--
-- The post says three derived distance columns were recomputed.  The paper
-- identifies the frame-relative distance components of columns 8--10 as MW,
-- M31 and Local Group distances.  Until the exact first-light row/column
-- selector is acquired, we retain that mapping as a strong source-consistent
-- candidate rather than silently upgrading it to same-object identity.
------------------------------------------------------------------------

data MappingStatus : Set where
  sourceConsistentCandidate : MappingStatus
  exactProducerConfirmed : MappingStatus

record FirstLightDerivedColumnCandidate : Set where
  constructor firstLightDerivedColumnCandidate
  field
    ordinal : Nat
    candidateFrame : DistanceFrame
    status : MappingStatus
    rationale : String

open FirstLightDerivedColumnCandidate public

candidateDerivedColumns : List FirstLightDerivedColumnCandidate
candidateDerivedColumns =
  firstLightDerivedColumnCandidate 1 galactocentricMWFrame sourceConsistentCandidate
    "McConnachie Table 2 column 8 is the MW/Galactocentric distance-velocity pair"
  ∷ firstLightDerivedColumnCandidate 2 m31CentricFrame sourceConsistentCandidate
    "McConnachie Table 2 column 9 is the M31 distance-velocity pair"
  ∷ firstLightDerivedColumnCandidate 3 localGroupFrame sourceConsistentCandidate
    "McConnachie Table 2 column 10 is the Local Group distance-velocity pair"
  ∷ []

candidateMappingImpliesExactFirstLightIdentity : Bool
candidateMappingImpliesExactFirstLightIdentity = false

candidateMappingImpliesExactFirstLightIdentityIsFalse :
  candidateMappingImpliesExactFirstLightIdentity ≡ false
candidateMappingImpliesExactFirstLightIdentityIsFalse = refl

------------------------------------------------------------------------
-- KKH 86 diagnosis contract.
------------------------------------------------------------------------

record KKH86DiagnosisDemand : Set where
  constructor kkh86DiagnosisDemand
  field
    exactSourceRowRequired : Bool
    exactPrintedDerivedValueRequired : Bool
    exactFirstLightInputRequired : Bool
    exactTransformConstantsRequired : Bool
    exactRoundingPolicyRequired : Bool
    compareIntermediateCartesianCoordinates : Bool
    unresolvedUntilPaid : Bool

kkh86DiagnosisDemand : KKH86DiagnosisDemand
kkh86DiagnosisDemand =
  kkh86DiagnosisDemand
    true true true true true true true

aggregateRMSMayEraseKKH86 : Bool
aggregateRMSMayEraseKKH86 = false

aggregateRMSMayEraseKKH86IsFalse : aggregateRMSMayEraseKKH86 ≡ false
aggregateRMSMayEraseKKH86IsFalse = refl
