module DASHI.Physics.ExoticGravity.SuperconductingGravityExperimentalConstraintRegistryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- EXPERIMENTAL CONSTRAINT REGISTRY
--
-- This registry separates reported signals, null replications, artifact
-- attribution, transition mismatch, and upper-bound constraints. None is
-- promoted into a universal claim for or against superconducting-gravity
-- coupling. Historical reported anomalies retain their authorship and are not
-- treated as independently replicated observations.
------------------------------------------------------------------------

data ConstraintKind : Set where
  nullReplication : ConstraintKind
  artifactAttributed : ConstraintKind
  transitionMismatch : ConstraintKind
  largeTheoryUpperBound : ConstraintKind
  unresolvedSignal : ConstraintKind

record ExperimentalConstraint : Set where
  constructor experimental-constraint
  field
    experiment : String
    year : String
    sourceReference : String
    kind : ConstraintKind
    sourceConfiguration : String
    measuredChannel : String
    resultSummary : String

open ExperimentalConstraint public

podkletnovNieminen1992ReportedSignal : ExperimentalConstraint
podkletnovNieminen1992ReportedSignal = experimental-constraint
  "Podkletnov-Nieminen bulk-YBCO apparent-weight experiment"
  "1992"
  "E. Podkletnov and R. Nieminen, Physica C 203 (1992) 441-444, DOI 10.1016/0921-4534(92)90055-H"
  unresolvedSignal
  "publisher abstract: dense bulk YBCO below 77 K; 5.48 g nonconducting/nonmagnetic sample above a levitating superconducting disk; disk rotation varied; electro-optical balance"
  "apparent weight of external test sample"
  "authors report 0.05-0.3 percent apparent weight loss depending on disk rotation speed; registry retains this as a published unresolved claim, not as an independently established gravity effect"

nasaStaticYBCO : ExperimentalConstraint
nasaStaticYBCO = experimental-constraint
  "NASA-linked static/type-II YBCO gravity tests"
  "1997-1999"
  "Li et al., Physica C 281 (1997) 260-267; Noever/Koczor follow-on NASA work"
  nullReplication
  "nonrotating or simplified YBCO configurations near/through Tc"
  "apparent weight/gravity-channel response"
  "no expected shielding effect was established; later weak RF-associated anomaly was attributed by the same programme to instrumentation artifact"

nasaRFArrtifact : ExperimentalConstraint
nasaRFArrtifact = experimental-constraint
  "NASA RF-illuminated YBCO follow-on"
  "1998"
  "Noever, Koczor, Robertson, AIAA-98-3139 and related NASA work"
  artifactAttributed
  "bulk YBCO disks in rotating/RF magnetic fields"
  "precision balance / proposed gravity response"
  "weak reported response was later treated as likely instrumental rather than a gravity modification"

hathawayReplication : ExperimentalConstraint
hathawayReplication = experimental-constraint
  "Hathaway-Cleveland-Bao rotating superconducting disk replication"
  "2003"
  "Physica C 385 (2003) 488-500"
  nullReplication
  "large rotating superconducting disk with radio-frequency fields; closest published Podkletnov-style replication"
  "weight/gravity modification above apparatus"
  "published replication reported a null result"

tajmarTransitionMismatch : ExperimentalConstraint
tajmarTransitionMismatch = experimental-constraint
  "Tajmar et al. cryogenic spinning-ring frame-dragging search"
  "2007-2008"
  "arXiv:0707.3806"
  transitionMismatch
  "spinning cryogenic rings with accelerometer and laser-gyroscope probes"
  "angular acceleration / angular velocity correlated external sensor signal"
  "reported onset occurred at a critical temperature that did not coincide with the material superconducting transition"

tajmarLargeTheoryBound : ExperimentalConstraint
tajmarLargeTheoryBound = experimental-constraint
  "Tajmar et al. large-effect theory constraint"
  "2008"
  "arXiv:0707.3806"
  largeTheoryUpperBound
  "cryogenic rotating-ring measurements"
  "frame-dragging-like external response"
  "authors state that several theories predicting very large frame-dragging fields around spinning superconductors are ruled out by up to four orders of magnitude"

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

record ConstraintBoundary : Set where
  constructor constraint-boundary
  field
    reportedSignalEqualsEstablishedEffect : Bool
    reportedSignalEqualsIndependentReplication : Bool
    laterNullRewritesHistoricalReportedClaim : Bool
    nullOneGeometryImpliesUniversalZero : Bool
    nullOneGeometryImpliesUniversalZeroIsFalse :
      nullOneGeometryImpliesUniversalZero ≡ false

    transitionMismatchSupportsSimpleTcLockedCoupling : Bool
    transitionMismatchSupportsSimpleTcLockedCouplingIsFalse :
      transitionMismatchSupportsSimpleTcLockedCoupling ≡ false

    artifactAttributedResultCountsAsGravityDetection : Bool
    artifactAttributedResultCountsAsGravityDetectionIsFalse :
      artifactAttributedResultCountsAsGravityDetection ≡ false

    largeTheoryBoundConstrainsMagnitudeWithoutProvingExactZero : Bool
    largeTheoryBoundConstrainsMagnitudeWithoutProvingExactZeroIsTrue :
      largeTheoryBoundConstrainsMagnitudeWithoutProvingExactZero ≡ true

canonicalConstraintBoundary : ConstraintBoundary
canonicalConstraintBoundary = constraint-boundary
  false false false
  false refl
  false refl
  false refl
  true refl
