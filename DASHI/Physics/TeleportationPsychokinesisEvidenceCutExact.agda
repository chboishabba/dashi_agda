{-# OPTIONS --safe #-}
module DASHI.Physics.TeleportationPsychokinesisEvidenceCutExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import DASHI.Core.ExperimentalCoordinateDesignExact
  using (ExperimentalCoordinateDesign; CoordinateSeparatesCollision)

-- Thin consumer of the canonical experimental-coordinate design.
-- A report, archived copy, theoretical model and independent experimental
-- replication are not interchangeable evidence types.

data SourceRole : Set where
  originalExperiment : SourceRole
  archiveCopy : SourceRole
  intelligenceSummary : SourceRole
  commissionedReview : SourceRole
  metaAnalysis : SourceRole
  independentReplication : SourceRole

data Mechanism : Set where
  quantumStateTransfer : Mechanism
  spacetimeMetricTransport : Mechanism
  higherDimensionalPath : Mechanism
  intentionDependentRNG : Mechanism
  macroscopicPK : Mechanism

data EpistemicStatus : Set where
  sourceExists : EpistemicStatus
  authorClaims : EpistemicStatus
  theoreticalConditional : EpistemicStatus
  observedContrast : EpistemicStatus
  independentlyReplicated : EpistemicStatus
  kernelProved : EpistemicStatus

record AttributedClaim : Set where
  constructor attributedClaim
  field
    sourceRoot : String
    authorCredit : String
    copiedAt : String
    role : SourceRole
    mechanism : Mechanism
    status : EpistemicStatus

afrlDavis2004 : AttributedClaim
afrlDavis2004 = attributedClaim
  "AFRL-PR-ED-TR-2003-0034 / ADA425545"
  "Eric W. Davis"
  "2004 US Air Force Research Laboratory report"
  commissionedReview macroscopicPK authorClaims

-- These inequalities are type-checkable non-promotion firewalls;
-- they are NOT propositions about whether a physical effect exists.
data _≢_ {A : Set} (a b : A) : Set where
  -- Deliberately no constructors: use Agda equality negation below instead.

False : Set
False = Bool ≡ (Bool → Bool)

notEqRole : archiveCopy ≡ independentReplication → False
notEqRole ()

notEqMechanism : quantumStateTransfer ≡ macroscopicPK → False
notEqMechanism ()

notEqStatus : authorClaims ≡ independentlyReplicated → False
notEqStatus ()

-- A physically discriminating experiment must declare independent
-- control, outcome and nuisance readings; it cannot infer cause from an
-- observed contrast without a custody and assignment contract.
record InterventionReceipt (World Control Outcome Nuisance : Set) : Set₁ where
  field
    assign : Control → World → World
    outcome : World → Outcome
    nuisance : World → Nuisance
    randomizationProtocol : String
    blindnessProtocol : String
    acquisitionProtocol : String
    calibrationProtocol : String
    prespecifiedEstimand : String
    negativeControlProtocol : String

record DiscriminationWitness
  {World Control Outcome Nuisance : Set}
  (r : InterventionReceipt World Control Outcome Nuisance) : Set where
  field
    controlHigh controlLow : Control
    world : World
    nuisanceHeld :
      InterventionReceipt.nuisance r
        (InterventionReceipt.assign r controlHigh world)
      ≡
      InterventionReceipt.nuisance r
        (InterventionReceipt.assign r controlLow world)
    outcomeDiffers :
      InterventionReceipt.outcome r
        (InterventionReceipt.assign r controlHigh world)
      ≡
      InterventionReceipt.outcome r
        (InterventionReceipt.assign r controlLow world)
      → False

-- A conditional geometric bypass witness is not a mechanism of matter
-- translocation: its physical implementation remains an independent input.
record HigherDimensionalTransportProposal (Point Path Barrier : Set) : Set₁ where
  field
    start finish : Point
    trajectory : Path
    begins : Path → Point
    ends : Path → Point
    avoids : Path → Barrier → Set
    wall : Barrier
    beginsCorrectly : begins trajectory ≡ start
    endsCorrectly : ends trajectory ≡ finish
    bypassesWall : avoids trajectory wall
    physicalCouplingReference : String

-- Reuse the existing coordinate-collision owner, not a new
-- observer-discrimination calculus.
record CoordinateTest
    (World Control Value Dimension Code : Set)
    (d : ExperimentalCoordinateDesign World Control Value Dimension)
    (encode : World → Code) : Set₁ where
  field
    separation : CoordinateSeparatesCollision d encode
    sourceRoot : String
    calibrationReceipt : String
