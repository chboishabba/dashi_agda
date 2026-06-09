module DASHI.Physics.Closure.NSSprint145ComparisonEnvelopeObstructionReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSSprint144CoupledZeroNumberObstructionReceipt
  as S144

------------------------------------------------------------------------
-- NS Sprint 145 comparison-envelope obstruction receipt.
--
-- This disjoint receipt anchors to Sprint 144 and records
-- ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators as absent/open and
-- fail-closed:
--
--   * the Sprint 144 coupled zero-number obstruction remains closed;
--   * local first-crossing and local favorable source support are accepted;
--   * local commutator rows and local boundary bookkeeping support are
--     accepted only as bounded/support rows;
--   * no simultaneous comparison envelope is constructed;
--   * sign-changing nonlocal psi1 terms remain uncontrolled;
--   * off-peak forcing remains uncontrolled;
--   * radial and log Biot-Savart commutators remain uncontrolled;
--   * boundary/annular constants remain absent/incompatible;
--   * under Hou-Luo geometry the algebraic collapse
--     2u1 dz2psi1 - (dz ur) dr u1 = dz2psi1 * (1/r) drGamma is recorded
--     and has the wrong sign for the desired comparison envelope;
--   * CoupledAxisymmetricZeroNumberForVBarrier remains false/open;
--   * SecondaryPeakExclusion remains false/open;
--   * the AxialMonotonicityOfSwirlProfile barrier route is closed out;
--   * global axial monotonicity is not promoted;
--   * no full Clay Navier-Stokes solution is constructed;
--   * no Clay promotion is recorded.

sprint145ComparisonEnvelopeObstructionLedgerClosed : Bool
sprint145ComparisonEnvelopeObstructionLedgerClosed = true

sprint144CoupledZeroNumberObstructionAnchored : Bool
sprint144CoupledZeroNumberObstructionAnchored = true

ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsAttemptRecorded : Bool
ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsAttemptRecorded = true

localFirstCrossingBarrierSupport : Bool
localFirstCrossingBarrierSupport = true

localFavorableSourceSupport : Bool
localFavorableSourceSupport = true

localBoundedCommutatorSupport : Bool
localBoundedCommutatorSupport = true

localBoundaryAnnularBookkeepingSupport : Bool
localBoundaryAnnularBookkeepingSupport = true

localComparisonSupportAccepted : Bool
localComparisonSupportAccepted = true

ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators : Bool
ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators = false

ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsProved : Bool
ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsProved = false

ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsOpen : Bool
ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsOpen = true

ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsAbsent : Bool
ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsAbsent = true

ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsStillObstructed : Bool
ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsStillObstructed = true

simultaneousEnvelopeConstructed : Bool
simultaneousEnvelopeConstructed = false

simultaneousEnvelopeAvailable : Bool
simultaneousEnvelopeAvailable = false

signChangingNonlocalPsi1Controlled : Bool
signChangingNonlocalPsi1Controlled = false

signChangingNonlocalPsi1ObstructsEnvelope : Bool
signChangingNonlocalPsi1ObstructsEnvelope = true

offPeakForcingControlled : Bool
offPeakForcingControlled = false

offPeakForcingObstructsEnvelope : Bool
offPeakForcingObstructsEnvelope = true

radialCommutatorDominated : Bool
radialCommutatorDominated = false

logBiotSavartCommutatorAbsorbed : Bool
logBiotSavartCommutatorAbsorbed = false

radialLogCommutatorObstructsEnvelope : Bool
radialLogCommutatorObstructsEnvelope = true

boundaryConstantsAvailable : Bool
boundaryConstantsAvailable = false

annularConstantsAvailable : Bool
annularConstantsAvailable = false

boundaryAnnularConstantsCompatible : Bool
boundaryAnnularConstantsCompatible = false

boundaryAnnularConstantsObstructEnvelope : Bool
boundaryAnnularConstantsObstructEnvelope = true

signedResidualInequalityAvailable : Bool
signedResidualInequalityAvailable = false

signedResidualInequalityObstructed : Bool
signedResidualInequalityObstructed = true

globalAlignmentTheorem : Bool
globalAlignmentTheorem = false

globalAlignmentTheoremProved : Bool
globalAlignmentTheoremProved = false

globalAlignmentTheoremOpen : Bool
globalAlignmentTheoremOpen = true

houLuoComparisonAlgebraicCollapseRecorded : Bool
houLuoComparisonAlgebraicCollapseRecorded = true

houLuoComparisonCollapseEquationCanonical : Bool
houLuoComparisonCollapseEquationCanonical = true

houLuoGeometryWrongSignConsequenceRecorded : Bool
houLuoGeometryWrongSignConsequenceRecorded = true

houLuoGeometryWrongSignForComparisonEnvelope : Bool
houLuoGeometryWrongSignForComparisonEnvelope = true

houLuoGeometryFavorableSignForComparisonEnvelope : Bool
houLuoGeometryFavorableSignForComparisonEnvelope = false

houLuoWrongSignObstructsComparisonEnvelope : Bool
houLuoWrongSignObstructsComparisonEnvelope = true

CoupledAxisymmetricZeroNumberForVBarrier : Bool
CoupledAxisymmetricZeroNumberForVBarrier = false

CoupledAxisymmetricZeroNumberForVBarrierProved : Bool
CoupledAxisymmetricZeroNumberForVBarrierProved = false

CoupledAxisymmetricZeroNumberForVBarrierOpen : Bool
CoupledAxisymmetricZeroNumberForVBarrierOpen = true

SecondaryPeakExclusion : Bool
SecondaryPeakExclusion = false

SecondaryPeakExclusionProved : Bool
SecondaryPeakExclusionProved = false

SecondaryPeakExclusionOpen : Bool
SecondaryPeakExclusionOpen = true

globalAxialMonotonicity : Bool
globalAxialMonotonicity = false

globalAxialMonotonicityProved : Bool
globalAxialMonotonicityProved = false

globalAxialMonotonicityPromoted : Bool
globalAxialMonotonicityPromoted = false

AxialMonotonicityOfSwirlProfileBarrierRouteClosedOut : Bool
AxialMonotonicityOfSwirlProfileBarrierRouteClosedOut = true

AxialMonotonicityOfSwirlProfileBarrierRoutePromoted : Bool
AxialMonotonicityOfSwirlProfileBarrierRoutePromoted = false

fullNavierStokesSolutionConstructed : Bool
fullNavierStokesSolutionConstructed = false

full_clay_ns_solved : Bool
full_clay_ns_solved = false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

sprint145KeepsComparisonEnvelopeFalse :
  ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators ≡ false
sprint145KeepsComparisonEnvelopeFalse = refl

sprint145KeepsComparisonEnvelopeOpen :
  ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsOpen ≡ true
sprint145KeepsComparisonEnvelopeOpen = refl

sprint145RecordsComparisonEnvelopeAbsent :
  ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsAbsent ≡ true
sprint145RecordsComparisonEnvelopeAbsent = refl

sprint145AcceptsLocalComparisonSupport :
  localComparisonSupportAccepted ≡ true
sprint145AcceptsLocalComparisonSupport = refl

sprint145KeepsGlobalAlignmentTheoremFalse :
  globalAlignmentTheorem ≡ false
sprint145KeepsGlobalAlignmentTheoremFalse = refl

sprint145KeepsCoupledZeroNumberFalse :
  CoupledAxisymmetricZeroNumberForVBarrier ≡ false
sprint145KeepsCoupledZeroNumberFalse = refl

sprint145KeepsSecondaryPeakExclusionFalse :
  SecondaryPeakExclusion ≡ false
sprint145KeepsSecondaryPeakExclusionFalse = refl

sprint145KeepsGlobalAxialMonotonicityFalse :
  globalAxialMonotonicity ≡ false
sprint145KeepsGlobalAxialMonotonicityFalse = refl

sprint145RecordsHouLuoAlgebraicCollapse :
  houLuoComparisonAlgebraicCollapseRecorded ≡ true
sprint145RecordsHouLuoAlgebraicCollapse = refl

sprint145RecordsHouLuoWrongSign :
  houLuoGeometryWrongSignForComparisonEnvelope ≡ true
sprint145RecordsHouLuoWrongSign = refl

sprint145ClosesAxialMonotonicityBarrierRoute :
  AxialMonotonicityOfSwirlProfileBarrierRouteClosedOut ≡ true
sprint145ClosesAxialMonotonicityBarrierRoute = refl

sprint145KeepsFullNSSolutionFalse :
  fullNavierStokesSolutionConstructed ≡ false
sprint145KeepsFullNSSolutionFalse = refl

sprint145KeepsFullClayNSFalse :
  full_clay_ns_solved ≡ false
sprint145KeepsFullClayNSFalse = refl

sprint145KeepsClayPromotionFalse :
  clayNavierStokesPromoted ≡ false
sprint145KeepsClayPromotionFalse = refl

data ComparisonEnvelopeObstructionStep : Set where
  anchorSprint144CoupledZeroNumberObstruction :
    ComparisonEnvelopeObstructionStep

  acceptLocalFirstCrossingBarrierSupport :
    ComparisonEnvelopeObstructionStep

  acceptLocalFavorableSourceSupport :
    ComparisonEnvelopeObstructionStep

  acceptLocalBoundedCommutatorSupport :
    ComparisonEnvelopeObstructionStep

  acceptLocalBoundaryAnnularBookkeepingSupport :
    ComparisonEnvelopeObstructionStep

  replayComparisonEnvelopeAttempt :
    ComparisonEnvelopeObstructionStep

  recordHouLuoAlgebraicCollapse :
    ComparisonEnvelopeObstructionStep

  recordHouLuoWrongSignConsequence :
    ComparisonEnvelopeObstructionStep

  recordSignChangingNonlocalPsi1Obstruction :
    ComparisonEnvelopeObstructionStep

  recordOffPeakForcingObstruction :
    ComparisonEnvelopeObstructionStep

  recordRadialLogCommutatorObstruction :
    ComparisonEnvelopeObstructionStep

  recordBoundaryAnnularConstantsObstruction :
    ComparisonEnvelopeObstructionStep

  recordMissingSignedResidualInequality :
    ComparisonEnvelopeObstructionStep

  keepCoupledZeroNumberFalseOpen :
    ComparisonEnvelopeObstructionStep

  keepSecondaryPeakExclusionFalseOpen :
    ComparisonEnvelopeObstructionStep

  refuseGlobalAxialMonotonicity :
    ComparisonEnvelopeObstructionStep

  closeAxialMonotonicityOfSwirlProfileBarrierRoute :
    ComparisonEnvelopeObstructionStep

  refuseFullNavierStokesSolutionClaim :
    ComparisonEnvelopeObstructionStep

  keepClayPromotionFlagsFalse :
    ComparisonEnvelopeObstructionStep

canonicalComparisonEnvelopeObstructionSteps :
  List ComparisonEnvelopeObstructionStep
canonicalComparisonEnvelopeObstructionSteps =
  anchorSprint144CoupledZeroNumberObstruction
  ∷ acceptLocalFirstCrossingBarrierSupport
  ∷ acceptLocalFavorableSourceSupport
  ∷ acceptLocalBoundedCommutatorSupport
  ∷ acceptLocalBoundaryAnnularBookkeepingSupport
  ∷ replayComparisonEnvelopeAttempt
  ∷ recordHouLuoAlgebraicCollapse
  ∷ recordHouLuoWrongSignConsequence
  ∷ recordSignChangingNonlocalPsi1Obstruction
  ∷ recordOffPeakForcingObstruction
  ∷ recordRadialLogCommutatorObstruction
  ∷ recordBoundaryAnnularConstantsObstruction
  ∷ recordMissingSignedResidualInequality
  ∷ keepCoupledZeroNumberFalseOpen
  ∷ keepSecondaryPeakExclusionFalseOpen
  ∷ refuseGlobalAxialMonotonicity
  ∷ closeAxialMonotonicityOfSwirlProfileBarrierRoute
  ∷ refuseFullNavierStokesSolutionClaim
  ∷ keepClayPromotionFlagsFalse
  ∷ []

data ComparisonEnvelopeObstruction : Set where
  SignChangingNonlocalPsi1Obstruction :
    ComparisonEnvelopeObstruction

  OffPeakForcingObstruction :
    ComparisonEnvelopeObstruction

  RadialLogCommutatorObstruction :
    ComparisonEnvelopeObstruction

  BoundaryAnnularConstantsObstruction :
    ComparisonEnvelopeObstruction

  MissingSignedResidualInequalityObstruction :
    ComparisonEnvelopeObstruction

  HouLuoWrongSignConsequenceObstruction :
    ComparisonEnvelopeObstruction

canonicalComparisonEnvelopeObstructions :
  List ComparisonEnvelopeObstruction
canonicalComparisonEnvelopeObstructions =
  SignChangingNonlocalPsi1Obstruction
  ∷ OffPeakForcingObstruction
  ∷ RadialLogCommutatorObstruction
  ∷ BoundaryAnnularConstantsObstruction
  ∷ MissingSignedResidualInequalityObstruction
  ∷ HouLuoWrongSignConsequenceObstruction
  ∷ []

data ComparisonEnvelopeOpenBoundary : Set where
  comparisonEnvelopeNotProvedHere :
    ComparisonEnvelopeOpenBoundary

  simultaneousEnvelopeNotConstructedHere :
    ComparisonEnvelopeOpenBoundary

  signChangingNonlocalPsi1NotControlledHere :
    ComparisonEnvelopeOpenBoundary

  offPeakForcingNotControlledHere :
    ComparisonEnvelopeOpenBoundary

  radialLogCommutatorsNotDominatedHere :
    ComparisonEnvelopeOpenBoundary

  boundaryAnnularConstantsNotCompatibleHere :
    ComparisonEnvelopeOpenBoundary

  signedResidualInequalityAbsentHere :
    ComparisonEnvelopeOpenBoundary

  houLuoAlgebraicCollapseWrongSignHere :
    ComparisonEnvelopeOpenBoundary

  coupledZeroNumberStillOpenHere :
    ComparisonEnvelopeOpenBoundary

  secondaryPeakExclusionStillOpenHere :
    ComparisonEnvelopeOpenBoundary

  noGlobalAxialMonotonicityHere :
    ComparisonEnvelopeOpenBoundary

  axialMonotonicityOfSwirlProfileBarrierRouteClosedOutHere :
    ComparisonEnvelopeOpenBoundary

  noFullClayNavierStokesSolutionHere :
    ComparisonEnvelopeOpenBoundary

  noClayPromotionHere :
    ComparisonEnvelopeOpenBoundary

canonicalComparisonEnvelopeOpenBoundaries :
  List ComparisonEnvelopeOpenBoundary
canonicalComparisonEnvelopeOpenBoundaries =
  comparisonEnvelopeNotProvedHere
  ∷ simultaneousEnvelopeNotConstructedHere
  ∷ signChangingNonlocalPsi1NotControlledHere
  ∷ offPeakForcingNotControlledHere
  ∷ radialLogCommutatorsNotDominatedHere
  ∷ boundaryAnnularConstantsNotCompatibleHere
  ∷ signedResidualInequalityAbsentHere
  ∷ houLuoAlgebraicCollapseWrongSignHere
  ∷ coupledZeroNumberStillOpenHere
  ∷ secondaryPeakExclusionStillOpenHere
  ∷ noGlobalAxialMonotonicityHere
  ∷ axialMonotonicityOfSwirlProfileBarrierRouteClosedOutHere
  ∷ noFullClayNavierStokesSolutionHere
  ∷ noClayPromotionHere
  ∷ []

data ComparisonEnvelopePromotion : Set where

comparisonEnvelopePromotionImpossibleHere :
  ComparisonEnvelopePromotion →
  ⊥
comparisonEnvelopePromotionImpossibleHere ()

sprint144AnchorStatement : String
sprint144AnchorStatement =
  "Sprint145 anchors to canonical Sprint144 coupled zero-number obstruction receipt"

localSupportStatement : String
localSupportStatement =
  "Local first-crossing, favorable source, bounded commutator, and boundary-annular bookkeeping rows are accepted only as support"

comparisonEnvelopeAttemptStatement : String
comparisonEnvelopeAttemptStatement =
  "ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators remains absent/open/false because no simultaneous signed envelope is constructed"

comparisonEnvelopeObstructionStatement : String
comparisonEnvelopeObstructionStatement =
  "The obstruction is sign-changing nonlocal psi1, off-peak forcing, radial/log commutators, boundary-annular constants, missing signed residual inequality, and the Hou-Luo wrong-sign collapse"

houLuoAlgebraicCollapseStatement : String
houLuoAlgebraicCollapseStatement =
  "Hou-Luo geometry collapses 2u1 dz2psi1 - (dz ur) dr u1 to dz2psi1 * (1/r) drGamma"

houLuoWrongSignConsequenceStatement : String
houLuoWrongSignConsequenceStatement =
  "Under the Hou-Luo sign geometry this collapse has the wrong sign for ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators"

downstreamBoundaryStatement : String
downstreamBoundaryStatement =
  "CoupledAxisymmetricZeroNumberForVBarrier and SecondaryPeakExclusion remain false/open while the comparison envelope is absent"

promotionBoundaryStatement : String
promotionBoundaryStatement =
  "No global axial monotonicity, the AxialMonotonicityOfSwirlProfile barrier route is closed out, no full Clay Navier-Stokes solution, and no Clay promotion are recorded"

record Sprint144ComparisonEnvelopeAnchor : Set where
  constructor sprint144ComparisonEnvelopeAnchorReceipt
  field
    anchorStatement :
      String
    anchorStatementIsCanonical :
      anchorStatement ≡ sprint144AnchorStatement
    sprint144Receipt :
      S144.NSSprint144CoupledZeroNumberObstructionReceipt
    sprint144ReceiptIsCanonical :
      sprint144Receipt ≡
      S144.canonicalNSSprint144CoupledZeroNumberObstructionReceipt
    sprint144LedgerClosed :
      S144.sprint144CoupledZeroNumberObstructionLedgerClosed ≡ true
    sprint144CoupledZeroNumberOpen :
      S144.CoupledAxisymmetricZeroNumberForVBarrierOpen ≡ true
    sprint144CoupledZeroNumberFalse :
      S144.CoupledAxisymmetricZeroNumberForVBarrier ≡ false
    sprint144SecondaryPeakExclusionOpen :
      S144.SecondaryPeakExclusionOpen ≡ true
    sprint144NoGlobalAxialMonotonicity :
      S144.globalAxialMonotonicityPromoted ≡ false
    sprint144NoFullNSSolution :
      S144.fullNavierStokesSolutionConstructed ≡ false
    sprint144NoFullClayNS :
      S144.full_clay_ns_solved ≡ false
    sprint144NoClayPromotion :
      S144.clayNavierStokesPromoted ≡ false

open Sprint144ComparisonEnvelopeAnchor public

canonicalSprint144ComparisonEnvelopeAnchor :
  Sprint144ComparisonEnvelopeAnchor
canonicalSprint144ComparisonEnvelopeAnchor =
  sprint144ComparisonEnvelopeAnchorReceipt
    sprint144AnchorStatement
    refl
    S144.canonicalNSSprint144CoupledZeroNumberObstructionReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

record LocalComparisonEnvelopeSupport : Set where
  constructor localComparisonEnvelopeSupportReceipt
  field
    supportStatement :
      String
    supportStatementIsCanonical :
      supportStatement ≡ localSupportStatement
    localFirstCrossingBarrierSupportField :
      localFirstCrossingBarrierSupport ≡ true
    localFavorableSourceSupportField :
      localFavorableSourceSupport ≡ true
    localBoundedCommutatorSupportField :
      localBoundedCommutatorSupport ≡ true
    localBoundaryAnnularBookkeepingSupportField :
      localBoundaryAnnularBookkeepingSupport ≡ true
    localComparisonSupportAcceptedField :
      localComparisonSupportAccepted ≡ true

open LocalComparisonEnvelopeSupport public

canonicalLocalComparisonEnvelopeSupport :
  LocalComparisonEnvelopeSupport
canonicalLocalComparisonEnvelopeSupport =
  localComparisonEnvelopeSupportReceipt
    localSupportStatement
    refl
    refl
    refl
    refl
    refl
    refl

record ComparisonEnvelopeAttemptBoundary : Set where
  constructor comparisonEnvelopeAttemptBoundaryReceipt
  field
    attemptStatement :
      String
    attemptStatementIsCanonical :
      attemptStatement ≡ comparisonEnvelopeAttemptStatement
    comparisonEnvelopeField :
      ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators ≡ false
    comparisonEnvelopeProvedField :
      ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsProved ≡ false
    comparisonEnvelopeOpenField :
      ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsOpen ≡ true
    comparisonEnvelopeAbsentField :
      ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsAbsent ≡ true
    comparisonEnvelopeStillObstructedField :
      ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsStillObstructed ≡ true
    simultaneousEnvelopeConstructedField :
      simultaneousEnvelopeConstructed ≡ false
    simultaneousEnvelopeAvailableField :
      simultaneousEnvelopeAvailable ≡ false

open ComparisonEnvelopeAttemptBoundary public

canonicalComparisonEnvelopeAttemptBoundary :
  ComparisonEnvelopeAttemptBoundary
canonicalComparisonEnvelopeAttemptBoundary =
  comparisonEnvelopeAttemptBoundaryReceipt
    comparisonEnvelopeAttemptStatement
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

record HouLuoAlgebraicCollapseEnvelopeObstruction : Set where
  constructor houLuoAlgebraicCollapseEnvelopeObstructionReceipt
  field
    collapseStatement :
      String
    collapseStatementIsCanonical :
      collapseStatement ≡ houLuoAlgebraicCollapseStatement
    wrongSignStatement :
      String
    wrongSignStatementIsCanonical :
      wrongSignStatement ≡ houLuoWrongSignConsequenceStatement
    algebraicCollapseRecordedField :
      houLuoComparisonAlgebraicCollapseRecorded ≡ true
    collapseEquationCanonicalField :
      houLuoComparisonCollapseEquationCanonical ≡ true
    wrongSignConsequenceRecordedField :
      houLuoGeometryWrongSignConsequenceRecorded ≡ true
    wrongSignForComparisonEnvelopeField :
      houLuoGeometryWrongSignForComparisonEnvelope ≡ true
    favorableSignForComparisonEnvelopeField :
      houLuoGeometryFavorableSignForComparisonEnvelope ≡ false
    wrongSignObstructsComparisonEnvelopeField :
      houLuoWrongSignObstructsComparisonEnvelope ≡ true
    comparisonEnvelopeField :
      ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators ≡ false
    comparisonEnvelopeOpenField :
      ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsOpen ≡ true

open HouLuoAlgebraicCollapseEnvelopeObstruction public

canonicalHouLuoAlgebraicCollapseEnvelopeObstruction :
  HouLuoAlgebraicCollapseEnvelopeObstruction
canonicalHouLuoAlgebraicCollapseEnvelopeObstruction =
  houLuoAlgebraicCollapseEnvelopeObstructionReceipt
    houLuoAlgebraicCollapseStatement
    refl
    houLuoWrongSignConsequenceStatement
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

record FiveComparisonEnvelopeObstructions : Set where
  constructor fiveComparisonEnvelopeObstructionsReceipt
  field
    blockerStatement :
      String
    blockerStatementIsCanonical :
      blockerStatement ≡ comparisonEnvelopeObstructionStatement
    obstructions :
      List ComparisonEnvelopeObstruction
    obstructionsAreCanonical :
      obstructions ≡ canonicalComparisonEnvelopeObstructions
    signChangingNonlocalPsi1ControlledField :
      signChangingNonlocalPsi1Controlled ≡ false
    signChangingNonlocalPsi1ObstructsEnvelopeField :
      signChangingNonlocalPsi1ObstructsEnvelope ≡ true
    offPeakForcingControlledField :
      offPeakForcingControlled ≡ false
    offPeakForcingObstructsEnvelopeField :
      offPeakForcingObstructsEnvelope ≡ true
    radialCommutatorDominatedField :
      radialCommutatorDominated ≡ false
    logBiotSavartCommutatorAbsorbedField :
      logBiotSavartCommutatorAbsorbed ≡ false
    radialLogCommutatorObstructsEnvelopeField :
      radialLogCommutatorObstructsEnvelope ≡ true
    boundaryConstantsAvailableField :
      boundaryConstantsAvailable ≡ false
    annularConstantsAvailableField :
      annularConstantsAvailable ≡ false
    boundaryAnnularConstantsCompatibleField :
      boundaryAnnularConstantsCompatible ≡ false
    boundaryAnnularConstantsObstructEnvelopeField :
      boundaryAnnularConstantsObstructEnvelope ≡ true
    signedResidualInequalityAvailableField :
      signedResidualInequalityAvailable ≡ false
    signedResidualInequalityObstructedField :
      signedResidualInequalityObstructed ≡ true

open FiveComparisonEnvelopeObstructions public

canonicalFiveComparisonEnvelopeObstructions :
  FiveComparisonEnvelopeObstructions
canonicalFiveComparisonEnvelopeObstructions =
  fiveComparisonEnvelopeObstructionsReceipt
    comparisonEnvelopeObstructionStatement
    refl
    canonicalComparisonEnvelopeObstructions
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

record DownstreamComparisonEnvelopeBoundary : Set where
  constructor downstreamComparisonEnvelopeBoundaryReceipt
  field
    boundaryStatement :
      String
    boundaryStatementIsCanonical :
      boundaryStatement ≡ downstreamBoundaryStatement
    coupledZeroNumberField :
      CoupledAxisymmetricZeroNumberForVBarrier ≡ false
    coupledZeroNumberProvedField :
      CoupledAxisymmetricZeroNumberForVBarrierProved ≡ false
    coupledZeroNumberOpenField :
      CoupledAxisymmetricZeroNumberForVBarrierOpen ≡ true
    secondaryPeakExclusionField :
      SecondaryPeakExclusion ≡ false
    secondaryPeakExclusionProvedField :
      SecondaryPeakExclusionProved ≡ false
    secondaryPeakExclusionOpenField :
      SecondaryPeakExclusionOpen ≡ true

open DownstreamComparisonEnvelopeBoundary public

canonicalDownstreamComparisonEnvelopeBoundary :
  DownstreamComparisonEnvelopeBoundary
canonicalDownstreamComparisonEnvelopeBoundary =
  downstreamComparisonEnvelopeBoundaryReceipt
    downstreamBoundaryStatement
    refl
    refl
    refl
    refl
    refl
    refl
    refl

record FailClosedComparisonEnvelopeBoundary : Set where
  constructor failClosedComparisonEnvelopeBoundaryReceipt
  field
    boundaryStatement :
      String
    boundaryStatementIsCanonical :
      boundaryStatement ≡ promotionBoundaryStatement
    openBoundaries :
      List ComparisonEnvelopeOpenBoundary
    openBoundariesAreCanonical :
      openBoundaries ≡ canonicalComparisonEnvelopeOpenBoundaries
    globalAxialMonotonicityField :
      globalAxialMonotonicity ≡ false
    globalAxialMonotonicityProvedField :
      globalAxialMonotonicityProved ≡ false
    globalAxialMonotonicityPromotedField :
      globalAxialMonotonicityPromoted ≡ false
    fullNavierStokesSolutionConstructedField :
      fullNavierStokesSolutionConstructed ≡ false
    fullClayNSSolvedField :
      full_clay_ns_solved ≡ false
    clayPromotionField :
      clayNavierStokesPromoted ≡ false
    promotionFlags :
      List ComparisonEnvelopePromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []
    noPromotionPossibleHere :
      ComparisonEnvelopePromotion →
      ⊥

open FailClosedComparisonEnvelopeBoundary public

canonicalFailClosedComparisonEnvelopeBoundary :
  FailClosedComparisonEnvelopeBoundary
canonicalFailClosedComparisonEnvelopeBoundary =
  failClosedComparisonEnvelopeBoundaryReceipt
    promotionBoundaryStatement
    refl
    canonicalComparisonEnvelopeOpenBoundaries
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    []
    refl
    comparisonEnvelopePromotionImpossibleHere

record Sprint145ComparisonEnvelopeObstructionStatuses : Set where
  constructor sprint145ComparisonEnvelopeObstructionStatuses
  field
    ledgerClosedField :
      sprint145ComparisonEnvelopeObstructionLedgerClosed ≡ true
    sprint144AnchoredField :
      sprint144CoupledZeroNumberObstructionAnchored ≡ true
    attemptRecordedField :
      ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsAttemptRecorded ≡ true
    localFirstCrossingBarrierSupportField :
      localFirstCrossingBarrierSupport ≡ true
    localFavorableSourceSupportField :
      localFavorableSourceSupport ≡ true
    localBoundedCommutatorSupportField :
      localBoundedCommutatorSupport ≡ true
    localBoundaryAnnularBookkeepingSupportField :
      localBoundaryAnnularBookkeepingSupport ≡ true
    localComparisonSupportAcceptedField :
      localComparisonSupportAccepted ≡ true
    comparisonEnvelopeField :
      ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators ≡ false
    comparisonEnvelopeProvedField :
      ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsProved ≡ false
    comparisonEnvelopeOpenField :
      ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsOpen ≡ true
    comparisonEnvelopeAbsentField :
      ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsAbsent ≡ true
    comparisonEnvelopeStillObstructedField :
      ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsStillObstructed ≡ true
    simultaneousEnvelopeConstructedField :
      simultaneousEnvelopeConstructed ≡ false
    simultaneousEnvelopeAvailableField :
      simultaneousEnvelopeAvailable ≡ false
    signChangingNonlocalPsi1ControlledField :
      signChangingNonlocalPsi1Controlled ≡ false
    signChangingNonlocalPsi1ObstructsEnvelopeField :
      signChangingNonlocalPsi1ObstructsEnvelope ≡ true
    offPeakForcingControlledField :
      offPeakForcingControlled ≡ false
    offPeakForcingObstructsEnvelopeField :
      offPeakForcingObstructsEnvelope ≡ true
    radialCommutatorDominatedField :
      radialCommutatorDominated ≡ false
    logBiotSavartCommutatorAbsorbedField :
      logBiotSavartCommutatorAbsorbed ≡ false
    radialLogCommutatorObstructsEnvelopeField :
      radialLogCommutatorObstructsEnvelope ≡ true
    boundaryConstantsAvailableField :
      boundaryConstantsAvailable ≡ false
    annularConstantsAvailableField :
      annularConstantsAvailable ≡ false
    boundaryAnnularConstantsCompatibleField :
      boundaryAnnularConstantsCompatible ≡ false
    boundaryAnnularConstantsObstructEnvelopeField :
      boundaryAnnularConstantsObstructEnvelope ≡ true
    signedResidualInequalityAvailableField :
      signedResidualInequalityAvailable ≡ false
    signedResidualInequalityObstructedField :
      signedResidualInequalityObstructed ≡ true
    houLuoComparisonAlgebraicCollapseRecordedField :
      houLuoComparisonAlgebraicCollapseRecorded ≡ true
    houLuoComparisonCollapseEquationCanonicalField :
      houLuoComparisonCollapseEquationCanonical ≡ true
    houLuoGeometryWrongSignConsequenceRecordedField :
      houLuoGeometryWrongSignConsequenceRecorded ≡ true
    houLuoGeometryWrongSignForComparisonEnvelopeField :
      houLuoGeometryWrongSignForComparisonEnvelope ≡ true
    houLuoGeometryFavorableSignForComparisonEnvelopeField :
      houLuoGeometryFavorableSignForComparisonEnvelope ≡ false
    houLuoWrongSignObstructsComparisonEnvelopeField :
      houLuoWrongSignObstructsComparisonEnvelope ≡ true
    coupledZeroNumberField :
      CoupledAxisymmetricZeroNumberForVBarrier ≡ false
    coupledZeroNumberProvedField :
      CoupledAxisymmetricZeroNumberForVBarrierProved ≡ false
    coupledZeroNumberOpenField :
      CoupledAxisymmetricZeroNumberForVBarrierOpen ≡ true
    secondaryPeakExclusionField :
      SecondaryPeakExclusion ≡ false
    secondaryPeakExclusionProvedField :
      SecondaryPeakExclusionProved ≡ false
    secondaryPeakExclusionOpenField :
      SecondaryPeakExclusionOpen ≡ true
    globalAxialMonotonicityField :
      globalAxialMonotonicity ≡ false
    globalAxialMonotonicityProvedField :
      globalAxialMonotonicityProved ≡ false
    globalAxialMonotonicityPromotedField :
      globalAxialMonotonicityPromoted ≡ false
    axialMonotonicityOfSwirlProfileBarrierRouteClosedOutField :
      AxialMonotonicityOfSwirlProfileBarrierRouteClosedOut ≡ true
    axialMonotonicityOfSwirlProfileBarrierRoutePromotedField :
      AxialMonotonicityOfSwirlProfileBarrierRoutePromoted ≡ false
    fullNavierStokesSolutionConstructedField :
      fullNavierStokesSolutionConstructed ≡ false
    fullClayNSSolvedField :
      full_clay_ns_solved ≡ false
    clayPromotionField :
      clayNavierStokesPromoted ≡ false

open Sprint145ComparisonEnvelopeObstructionStatuses public

canonicalSprint145ComparisonEnvelopeObstructionStatuses :
  Sprint145ComparisonEnvelopeObstructionStatuses
canonicalSprint145ComparisonEnvelopeObstructionStatuses =
  sprint145ComparisonEnvelopeObstructionStatuses
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

sprint145ReceiptSummaryStatement : String
sprint145ReceiptSummaryStatement =
  "Sprint145 anchors to Sprint144 and records ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators as absent/open/false: 2u1 dz2psi1 - (dz ur) dr u1 = dz2psi1 * (1/r) drGamma collapses to the Hou-Luo wrong sign for the comparison envelope; the AxialMonotonicityOfSwirlProfile barrier route is closed out; CoupledAxisymmetricZeroNumberForVBarrier, SecondaryPeakExclusion, globalAxialMonotonicity, full_clay_ns_solved, and clayNavierStokesPromoted remain false."

record NSSprint145ComparisonEnvelopeObstructionReceipt : Set where
  constructor nsSprint145ComparisonEnvelopeObstructionReceipt
  field
    sprint144Anchor :
      Sprint144ComparisonEnvelopeAnchor
    localSupport :
      LocalComparisonEnvelopeSupport
    attemptBoundary :
      ComparisonEnvelopeAttemptBoundary
    houLuoCollapse :
      HouLuoAlgebraicCollapseEnvelopeObstruction
    obstructions :
      FiveComparisonEnvelopeObstructions
    downstreamBoundary :
      DownstreamComparisonEnvelopeBoundary
    failClosedBoundary :
      FailClosedComparisonEnvelopeBoundary
    statuses :
      Sprint145ComparisonEnvelopeObstructionStatuses
    statusesAreCanonical :
      statuses ≡ canonicalSprint145ComparisonEnvelopeObstructionStatuses
    steps :
      List ComparisonEnvelopeObstructionStep
    stepsAreCanonical :
      steps ≡ canonicalComparisonEnvelopeObstructionSteps
    receiptSummary :
      String
    receiptSummaryIsCanonical :
      receiptSummary ≡ sprint145ReceiptSummaryStatement

open NSSprint145ComparisonEnvelopeObstructionReceipt public

canonicalNSSprint145ComparisonEnvelopeObstructionReceipt :
  NSSprint145ComparisonEnvelopeObstructionReceipt
canonicalNSSprint145ComparisonEnvelopeObstructionReceipt =
  nsSprint145ComparisonEnvelopeObstructionReceipt
    canonicalSprint144ComparisonEnvelopeAnchor
    canonicalLocalComparisonEnvelopeSupport
    canonicalComparisonEnvelopeAttemptBoundary
    canonicalHouLuoAlgebraicCollapseEnvelopeObstruction
    canonicalFiveComparisonEnvelopeObstructions
    canonicalDownstreamComparisonEnvelopeBoundary
    canonicalFailClosedComparisonEnvelopeBoundary
    canonicalSprint145ComparisonEnvelopeObstructionStatuses
    refl
    canonicalComparisonEnvelopeObstructionSteps
    refl
    sprint145ReceiptSummaryStatement
    refl

sprint145ComparisonEnvelopeObstructionSummary :
  Sprint144ComparisonEnvelopeAnchor
  × LocalComparisonEnvelopeSupport
  × ComparisonEnvelopeAttemptBoundary
  × HouLuoAlgebraicCollapseEnvelopeObstruction
  × FiveComparisonEnvelopeObstructions
  × DownstreamComparisonEnvelopeBoundary
  × FailClosedComparisonEnvelopeBoundary
  × Sprint145ComparisonEnvelopeObstructionStatuses
sprint145ComparisonEnvelopeObstructionSummary =
  canonicalSprint144ComparisonEnvelopeAnchor ,
  canonicalLocalComparisonEnvelopeSupport ,
  canonicalComparisonEnvelopeAttemptBoundary ,
  canonicalHouLuoAlgebraicCollapseEnvelopeObstruction ,
  canonicalFiveComparisonEnvelopeObstructions ,
  canonicalDownstreamComparisonEnvelopeBoundary ,
  canonicalFailClosedComparisonEnvelopeBoundary ,
  canonicalSprint145ComparisonEnvelopeObstructionStatuses

sprint145AllRequiredStatuses :
  (sprint145ComparisonEnvelopeObstructionLedgerClosed ≡ true)
  × (sprint144CoupledZeroNumberObstructionAnchored ≡ true)
  × (ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsAttemptRecorded ≡ true)
  × (localFirstCrossingBarrierSupport ≡ true)
  × (localFavorableSourceSupport ≡ true)
  × (localBoundedCommutatorSupport ≡ true)
  × (localBoundaryAnnularBookkeepingSupport ≡ true)
  × (localComparisonSupportAccepted ≡ true)
  × (ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators ≡ false)
  × (ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsProved ≡ false)
  × (ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsOpen ≡ true)
  × (ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsAbsent ≡ true)
  × (ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsStillObstructed ≡ true)
  × (simultaneousEnvelopeConstructed ≡ false)
  × (simultaneousEnvelopeAvailable ≡ false)
  × (signChangingNonlocalPsi1Controlled ≡ false)
  × (signChangingNonlocalPsi1ObstructsEnvelope ≡ true)
  × (offPeakForcingControlled ≡ false)
  × (offPeakForcingObstructsEnvelope ≡ true)
  × (radialCommutatorDominated ≡ false)
  × (logBiotSavartCommutatorAbsorbed ≡ false)
  × (radialLogCommutatorObstructsEnvelope ≡ true)
  × (boundaryConstantsAvailable ≡ false)
  × (annularConstantsAvailable ≡ false)
  × (boundaryAnnularConstantsCompatible ≡ false)
  × (boundaryAnnularConstantsObstructEnvelope ≡ true)
  × (signedResidualInequalityAvailable ≡ false)
  × (signedResidualInequalityObstructed ≡ true)
  × (globalAlignmentTheorem ≡ false)
  × (globalAlignmentTheoremProved ≡ false)
  × (globalAlignmentTheoremOpen ≡ true)
  × (houLuoComparisonAlgebraicCollapseRecorded ≡ true)
  × (houLuoComparisonCollapseEquationCanonical ≡ true)
  × (houLuoGeometryWrongSignConsequenceRecorded ≡ true)
  × (houLuoGeometryWrongSignForComparisonEnvelope ≡ true)
  × (houLuoGeometryFavorableSignForComparisonEnvelope ≡ false)
  × (houLuoWrongSignObstructsComparisonEnvelope ≡ true)
  × (CoupledAxisymmetricZeroNumberForVBarrier ≡ false)
  × (CoupledAxisymmetricZeroNumberForVBarrierProved ≡ false)
  × (CoupledAxisymmetricZeroNumberForVBarrierOpen ≡ true)
  × (SecondaryPeakExclusion ≡ false)
  × (SecondaryPeakExclusionProved ≡ false)
  × (SecondaryPeakExclusionOpen ≡ true)
  × (globalAxialMonotonicity ≡ false)
  × (globalAxialMonotonicityProved ≡ false)
  × (globalAxialMonotonicityPromoted ≡ false)
  × (AxialMonotonicityOfSwirlProfileBarrierRouteClosedOut ≡ true)
  × (AxialMonotonicityOfSwirlProfileBarrierRoutePromoted ≡ false)
  × (fullNavierStokesSolutionConstructed ≡ false)
  × (full_clay_ns_solved ≡ false)
  × (clayNavierStokesPromoted ≡ false)
sprint145AllRequiredStatuses =
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl
