module DASHI.Biology.Physical.BDNACalibratedHelicalGeometryExact where

------------------------------------------------------------------------
-- SOURCE-FACING MOTIVATION
-- Wilma K. Olson, Manju Bansal, Stephen K. Burley, Richard E. Dickerson,
-- Mark Gerstein, Stephen C. Harvey, Udo Heinemann, Xiang-Jun Lu,
-- Stephen Neidle, Zippora Shakked, Helen Sklenar, Masami Suzuki,
-- Charon Tung, Eric Westhof and Clive Wolberger,
-- "A standard reference frame for the description of nucleic acid base-pair
-- geometry", Journal of Molecular Biology 313 (2001), 229--237.
-- DOI: 10.1006/jmbi.2001.4987.
--
-- Li-Yan Yu et al., "Structures of an all-alpha protein running along the DNA
-- major groove", Nucleic Acids Research 44 (2016), 3936--3946.
-- DOI: 10.1093/nar/gkw133.
--
-- The second source tabulates an ideal B-DNA reference with rise about 3.4 A,
-- twist 36 degrees and pitch 34 A / 10 bp per turn.  The exact Nat values below
-- are therefore an ideal-reference calibration regression, not a claim that
-- every B-DNA sequence/environment has those exact parameters.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.DNAChemistryCarrier as DNA

------------------------------------------------------------------------
-- Six standard rigid base-pair-step coordinates.
-- Translational values are represented here in 0.1-A units and rotations in
-- whole degrees solely for an exact finite calibrated regression.
------------------------------------------------------------------------

record BasePairStep6 : Set where
  constructor basePairStep6
  field
    shiftTenthsAngstrom slideTenthsAngstrom riseTenthsAngstrom : Nat
    tiltDegrees rollDegrees twistDegrees : Nat

open BasePairStep6 public

idealBStep : BasePairStep6
idealBStep = basePairStep6 0 0 34 0 0 36

basePairsPerIdealTurn : Nat
basePairsPerIdealTurn = 10

idealPitchTenthsAngstrom : Nat
idealPitchTenthsAngstrom = 340

idealFullTurnDegrees : Nat
idealFullTurnDegrees = 360

idealRiseTimesTurnIsPitch :
  basePairsPerIdealTurn * riseTenthsAngstrom idealBStep
  ≡ idealPitchTenthsAngstrom
idealRiseTimesTurnIsPitch = refl

idealTwistTimesTurnIsFullRotation :
  basePairsPerIdealTurn * twistDegrees idealBStep
  ≡ idealFullTurnDegrees
idealTwistTimesTurnIsFullRotation = refl

------------------------------------------------------------------------
-- Exact helical screw-coordinate subgroup used for composition.  This is an
-- axial-translation + axial-rotation subgroup of SE(3), not a replacement for
-- the full noncommutative six-degree rigid-motion group.
------------------------------------------------------------------------

record HelicalFrame : Set where
  constructor helicalFrame
  field
    axialTenthsAngstrom accumulatedDegrees : Nat

open HelicalFrame public

identityFrame : HelicalFrame
identityFrame = helicalFrame 0 0

composeHelical : HelicalFrame → HelicalFrame → HelicalFrame
composeHelical (helicalFrame z theta) (helicalFrame dz dtheta) =
  helicalFrame (z + dz) (theta + dtheta)

stepFrame : BasePairStep6 → HelicalFrame
stepFrame q = helicalFrame (riseTenthsAngstrom q) (twistDegrees q)

advanceIdeal : HelicalFrame → HelicalFrame
advanceIdeal frame = composeHelical frame (stepFrame idealBStep)

advance10 : HelicalFrame → HelicalFrame
advance10 f =
  advanceIdeal (advanceIdeal (advanceIdeal (advanceIdeal (advanceIdeal
    (advanceIdeal (advanceIdeal (advanceIdeal (advanceIdeal (advanceIdeal f)))))))))

idealTenStepsFromIdentity :
  advance10 identityFrame
  ≡ helicalFrame idealPitchTenthsAngstrom idealFullTurnDegrees
idealTenStepsFromIdentity = refl

------------------------------------------------------------------------
-- Sequence/context-dependent geometry interface.  Native C/A/G/T remains the
-- symbolic carrier; physical geometry is compiled from neighbouring bases and
-- environment rather than identified with the alphabet.
------------------------------------------------------------------------

data SaltBand : Set where lowSalt physiologicalLike highSalt : SaltBand

data TemperatureBand : Set where cool referenceTemperature warm : TemperatureBand

record HelixEnvironment : Set where
  constructor helixEnvironment
  field
    salt : SaltBand
    temperature : TemperatureBand

open HelixEnvironment public

record SequenceDependentStepLaw : Set where
  field
    stepFor :
      HelixEnvironment → DNA.DNABase → DNA.DNABase → BasePairStep6

open SequenceDependentStepLaw public

-- A deliberately conservative reference law: every dinucleotide receives the
-- calibrated ideal-B step.  Later empirical parameter tables refine this law
-- without changing the carrier or composition interfaces.
idealReferenceStepLaw : SequenceDependentStepLaw
idealReferenceStepLaw = record
  { stepFor = λ env left right → idealBStep }

referenceLawSequenceIndependent :
  (env : HelixEnvironment) (a b c d : DNA.DNABase) →
  stepFor idealReferenceStepLaw env a b
  ≡ stepFor idealReferenceStepLaw env c d
referenceLawSequenceIndependent env a b c d = refl

------------------------------------------------------------------------
-- Full SE(3) calibration obligation.  The six coordinates above are exactly
-- the required parameter slots; a later owner must supply actual rotations,
-- translations, composition and inverses and prove that calibration maps these
-- step coordinates into that group.
------------------------------------------------------------------------

record SE3CalibrationInterface : Set₁ where
  field
    SE3 : Set
    identity : SE3
    compose : SE3 → SE3 → SE3
    inverse : SE3 → SE3
    realizeStep : BasePairStep6 → SE3
    leftIdentity : (g : SE3) → compose identity g ≡ g
    rightIdentity : (g : SE3) → compose g identity ≡ g
    inverseLeft : (g : SE3) → compose (inverse g) g ≡ identity

------------------------------------------------------------------------
-- Rod/supercoiling authority boundary.  Twist/writhe/linking and elastic-rod
-- energy require geometric/analytic owners beyond this calibrated screw
-- regression.
------------------------------------------------------------------------

record BDNAAuthorityBoundary : Set where
  field
    idealReferenceIsUniversalBDNA : Bool
    idealReferenceIsUniversalBDNAIsFalse :
      idealReferenceIsUniversalBDNA ≡ false
    screwSubgroupIsFullSE3 : Bool
    screwSubgroupIsFullSE3IsFalse : screwSubgroupIsFullSE3 ≡ false
    calibratedStepGeometryProvesLinkingNumberTheorem : Bool
    calibratedStepGeometryProvesLinkingNumberTheoremIsFalse :
      calibratedStepGeometryProvesLinkingNumberTheorem ≡ false

canonicalBDNAAuthorityBoundary : BDNAAuthorityBoundary
canonicalBDNAAuthorityBoundary = record
  { idealReferenceIsUniversalBDNA = false
  ; idealReferenceIsUniversalBDNAIsFalse = refl
  ; screwSubgroupIsFullSE3 = false
  ; screwSubgroupIsFullSE3IsFalse = refl
  ; calibratedStepGeometryProvesLinkingNumberTheorem = false
  ; calibratedStepGeometryProvesLinkingNumberTheoremIsFalse = refl
  }
