module DASHI.Physics.Closure.NSCascadeTransversalityCollapseBoundary where

-- Corrected finite Navier-Stokes cascade boundary.
--
-- The output-only cascade-width target is too permissive for the exact
-- strain/Leray symbol: if the output frame is chosen after seeing the output
-- direction, Family-I/II zero-mode compatibility can become tautological.
--
-- The live finite theorem therefore tracks propagated polarization states:
--
--   (a , Omega_a) , (b , Omega_b) in T¹S² × T¹S²
--
-- and the true Leray polarization cascade map
--
--   u_a = a × Omega_a
--   u_b = b × Omega_b
--   c   = normalize (a + b)
--   Y_c = P_c [ (b · u_a) u_b + (a · u_b) u_a ]
--   Omega_c = normalize (c × Y_c).
--
-- The target is not merely a rank count.  The required finite theorem is a
-- propagated-coherence transversality collapse:
--
--   K_k = (kappa_1 , ... , kappa_k)
--   rank dK_k = k, through the finite depths needed to force collapse,
--
-- followed by the output-width/LRT consequence.  This module records that
-- target and its exact proof obligations.  It does not prove the rank
-- theorem, does not prove the output-width theorem, does not prove analytic
-- leakage transfer, and keeps Clay NS promotion false.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSSignAntisymmetryExactIdentityBoundary as Sign
import DASHI.Physics.Closure.NSTrueLerayTriadicDefectSymbol as TrueSymbol

------------------------------------------------------------------------
-- Local utility.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Project-local source anchors.

trueLerayTriadicDefectSymbolReference : String
trueLerayTriadicDefectSymbolReference =
  "DASHI.Physics.Closure.NSTrueLerayTriadicDefectSymbol"

signAntisymmetryIdentityReference : String
signAntisymmetryIdentityReference =
  "DASHI.Physics.Closure.NSSignAntisymmetryExactIdentityBoundary"

trueLerayTriadicDefectSymbolImported : Bool
trueLerayTriadicDefectSymbolImported =
  true

signAntisymmetryIdentityImported : Bool
signAntisymmetryIdentityImported =
  true

trueLerayTriadicDefectSymbolReceipt :
  TrueSymbol.TrueLerayTriadicDefectSymbolBoundary
trueLerayTriadicDefectSymbolReceipt =
  TrueSymbol.canonicalTrueLerayTriadicDefectSymbolBoundary

signAntisymmetryIdentityReceipt :
  Sign.NSSignAntisymmetryExactIdentityReceipt
signAntisymmetryIdentityReceipt =
  Sign.canonicalNSSignAntisymmetryExactIdentityReceipt

------------------------------------------------------------------------
-- Corrected finite state space: T¹S² × T¹S².

data SphereDirectionCarrier : Set where
  inputDirectionA :
    SphereDirectionCarrier

  inputDirectionB :
    SphereDirectionCarrier

  outputDirectionC :
    SphereDirectionCarrier

  continuationDirectionD :
    SphereDirectionCarrier

  continuationOutputDirectionE :
    SphereDirectionCarrier

data UnitTangentPolarizationCarrier : Set where
  omegaAInTangentSpaceAtA :
    UnitTangentPolarizationCarrier

  omegaBInTangentSpaceAtB :
    UnitTangentPolarizationCarrier

  omegaCTransportedByTrueLerayCascade :
    UnitTangentPolarizationCarrier

  omegaDContinuationInput :
    UnitTangentPolarizationCarrier

  omegaETransportedBySecondCascade :
    UnitTangentPolarizationCarrier

data UnitTangentSphereState : Set where
  t1s2State :
    SphereDirectionCarrier →
    UnitTangentPolarizationCarrier →
    UnitTangentSphereState

data PropagatedPolarizationStatePair : Set where
  t1s2TimesT1s2InputPair :
    UnitTangentSphereState →
    UnitTangentSphereState →
    PropagatedPolarizationStatePair

canonicalStateA : UnitTangentSphereState
canonicalStateA =
  t1s2State inputDirectionA omegaAInTangentSpaceAtA

canonicalStateB : UnitTangentSphereState
canonicalStateB =
  t1s2State inputDirectionB omegaBInTangentSpaceAtB

canonicalStateC : UnitTangentSphereState
canonicalStateC =
  t1s2State outputDirectionC omegaCTransportedByTrueLerayCascade

canonicalStateD : UnitTangentSphereState
canonicalStateD =
  t1s2State continuationDirectionD omegaDContinuationInput

canonicalStateE : UnitTangentSphereState
canonicalStateE =
  t1s2State continuationOutputDirectionE omegaETransportedBySecondCascade

canonicalInputStatePair : PropagatedPolarizationStatePair
canonicalInputStatePair =
  t1s2TimesT1s2InputPair canonicalStateA canonicalStateB

canonicalContinuationStatePair : PropagatedPolarizationStatePair
canonicalContinuationStatePair =
  t1s2TimesT1s2InputPair canonicalStateC canonicalStateD

------------------------------------------------------------------------
-- True Leray propagated-polarization cascade map target.

data VelocityRecoveryStep : Set where
  velocityFromVorticityByBiotSavartCrossProduct :
    UnitTangentSphereState →
    VelocityRecoveryStep

data ResonanceStep : Set where
  outputDirectionIsNormalizedInputSum :
    UnitTangentSphereState →
    UnitTangentSphereState →
    SphereDirectionCarrier →
    ResonanceStep

data LerayProjectionStep : Set where
  applyOutputLerayProjectorPc :
    SphereDirectionCarrier →
    LerayProjectionStep

data TrueLerayBilinearOutputStep : Set where
  symmetrizedConvectiveOutput :
    VelocityRecoveryStep →
    VelocityRecoveryStep →
    ResonanceStep →
    LerayProjectionStep →
    TrueLerayBilinearOutputStep

data OutputVorticityTransportStep : Set where
  outputVorticityFromCcrossYc :
    SphereDirectionCarrier →
    TrueLerayBilinearOutputStep →
    UnitTangentSphereState →
    OutputVorticityTransportStep

data TrueLerayPolarizationCascadeMapTarget : Set where
  trueLerayPolarizationCascadeMap :
    PropagatedPolarizationStatePair →
    UnitTangentSphereState →
    TrueLerayBilinearOutputStep →
    OutputVorticityTransportStep →
    TrueLerayPolarizationCascadeMapTarget

canonicalVelocityRecoveryA : VelocityRecoveryStep
canonicalVelocityRecoveryA =
  velocityFromVorticityByBiotSavartCrossProduct canonicalStateA

canonicalVelocityRecoveryB : VelocityRecoveryStep
canonicalVelocityRecoveryB =
  velocityFromVorticityByBiotSavartCrossProduct canonicalStateB

canonicalResonanceStepABC : ResonanceStep
canonicalResonanceStepABC =
  outputDirectionIsNormalizedInputSum
    canonicalStateA
    canonicalStateB
    outputDirectionC

canonicalLerayProjectionC : LerayProjectionStep
canonicalLerayProjectionC =
  applyOutputLerayProjectorPc outputDirectionC

canonicalBilinearOutputStepABC : TrueLerayBilinearOutputStep
canonicalBilinearOutputStepABC =
  symmetrizedConvectiveOutput
    canonicalVelocityRecoveryA
    canonicalVelocityRecoveryB
    canonicalResonanceStepABC
    canonicalLerayProjectionC

canonicalOutputVorticityTransportC : OutputVorticityTransportStep
canonicalOutputVorticityTransportC =
  outputVorticityFromCcrossYc
    outputDirectionC
    canonicalBilinearOutputStepABC
    canonicalStateC

canonicalTrueLerayPolarizationCascadeMapTarget :
  TrueLerayPolarizationCascadeMapTarget
canonicalTrueLerayPolarizationCascadeMapTarget =
  trueLerayPolarizationCascadeMap
    canonicalInputStatePair
    canonicalStateC
    canonicalBilinearOutputStepABC
    canonicalOutputVorticityTransportC

------------------------------------------------------------------------
-- Propagated coherence constraints K_k.

data CoherenceChannel : Set where
  outputOnlyFrameCompatibilityChannel :
    CoherenceChannel

  propagatedVelocityMeanChannel :
    CoherenceChannel

  propagatedVorticityMeanChannel :
    CoherenceChannel

  transportedInputPolarizationChannel :
    CoherenceChannel

  secondGenerationPropagatedChannel :
    CoherenceChannel

data PropagatedCoherenceConstraint : Set where
  kappaConstraintAtDepth :
    Nat →
    CoherenceChannel →
    TrueLerayPolarizationCascadeMapTarget →
    PropagatedCoherenceConstraint

data PropagatedCoherenceConstraintFamily : Set where
  KkPropagatedCoherenceConstraints :
    Nat →
    List PropagatedCoherenceConstraint →
    PropagatedCoherenceConstraintFamily

canonicalKappa1 : PropagatedCoherenceConstraint
canonicalKappa1 =
  kappaConstraintAtDepth
    (suc zero)
    propagatedVelocityMeanChannel
    canonicalTrueLerayPolarizationCascadeMapTarget

canonicalKappa2 : PropagatedCoherenceConstraint
canonicalKappa2 =
  kappaConstraintAtDepth
    (suc (suc zero))
    secondGenerationPropagatedChannel
    canonicalTrueLerayPolarizationCascadeMapTarget

canonicalKappa3 : PropagatedCoherenceConstraint
canonicalKappa3 =
  kappaConstraintAtDepth
    (suc (suc (suc zero)))
    transportedInputPolarizationChannel
    canonicalTrueLerayPolarizationCascadeMapTarget

canonicalPropagatedCoherenceConstraints :
  List PropagatedCoherenceConstraint
canonicalPropagatedCoherenceConstraints =
  canonicalKappa1
  ∷ canonicalKappa2
  ∷ canonicalKappa3
  ∷ []

propagatedCoherenceConstraintCount : Nat
propagatedCoherenceConstraintCount =
  listLength canonicalPropagatedCoherenceConstraints

propagatedCoherenceConstraintCountIs3 :
  propagatedCoherenceConstraintCount ≡ 3
propagatedCoherenceConstraintCountIs3 =
  refl

canonicalPropagatedCoherenceConstraintFamily :
  PropagatedCoherenceConstraintFamily
canonicalPropagatedCoherenceConstraintFamily =
  KkPropagatedCoherenceConstraints
    (suc (suc (suc zero)))
    canonicalPropagatedCoherenceConstraints

------------------------------------------------------------------------
-- Transversality-collapse theorem target.

data JacobianRankConditionTarget : Set where
  rankDKkEqualsKOffDegeneracyLocus :
    PropagatedCoherenceConstraintFamily →
    JacobianRankConditionTarget

data DegeneracyLocusGuard : Set where
  excludeZeroOutputFrequency :
    DegeneracyLocusGuard

  excludeZeroBilinearOutputYc :
    DegeneracyLocusGuard

  excludeUndefinedStrainEigenbundle :
    DegeneracyLocusGuard

  excludeOutputOnlyTautologicalFrameChoice :
    DegeneracyLocusGuard

data CascadeTransversalityCollapseTarget : Set where
  propagatedCoherenceConstraintsCollapseDimension :
    PropagatedCoherenceConstraintFamily →
    JacobianRankConditionTarget →
    List DegeneracyLocusGuard →
    CascadeTransversalityCollapseTarget

canonicalRankConditionTarget : JacobianRankConditionTarget
canonicalRankConditionTarget =
  rankDKkEqualsKOffDegeneracyLocus
    canonicalPropagatedCoherenceConstraintFamily

canonicalDegeneracyGuards : List DegeneracyLocusGuard
canonicalDegeneracyGuards =
  excludeZeroOutputFrequency
  ∷ excludeZeroBilinearOutputYc
  ∷ excludeUndefinedStrainEigenbundle
  ∷ excludeOutputOnlyTautologicalFrameChoice
  ∷ []

degeneracyGuardCount : Nat
degeneracyGuardCount =
  listLength canonicalDegeneracyGuards

degeneracyGuardCountIs4 :
  degeneracyGuardCount ≡ 4
degeneracyGuardCountIs4 =
  refl

canonicalCascadeTransversalityCollapseTarget :
  CascadeTransversalityCollapseTarget
canonicalCascadeTransversalityCollapseTarget =
  propagatedCoherenceConstraintsCollapseDimension
    canonicalPropagatedCoherenceConstraintFamily
    canonicalRankConditionTarget
    canonicalDegeneracyGuards

------------------------------------------------------------------------
-- Output-width / Lei-Ren-Tian consequence target.

data PropagatedCascadeClosedZeroModeSetTarget : Set where
  zNSInfinityPropagatedIntersection :
    CascadeTransversalityCollapseTarget →
    PropagatedCascadeClosedZeroModeSetTarget

data OutputProjectionTarget : Set where
  piOutFromPropagatedCascadeClosedStatesToS2 :
    PropagatedCascadeClosedZeroModeSetTarget →
    OutputProjectionTarget

data OutputWidthConsequenceTarget : Set where
  positiveGreatCircleAvoidanceWidthAfterPropagatedCollapse :
    OutputProjectionTarget →
    OutputWidthConsequenceTarget

data LeiRenTianCompatibilityConsequence : Set where
  lrtGreatCircleHittingForcesLeakageOutsidePropagatedZeroModeSheaf :
    OutputWidthConsequenceTarget →
    LeiRenTianCompatibilityConsequence

canonicalPropagatedCascadeClosedZeroModeSetTarget :
  PropagatedCascadeClosedZeroModeSetTarget
canonicalPropagatedCascadeClosedZeroModeSetTarget =
  zNSInfinityPropagatedIntersection
    canonicalCascadeTransversalityCollapseTarget

canonicalOutputProjectionTarget : OutputProjectionTarget
canonicalOutputProjectionTarget =
  piOutFromPropagatedCascadeClosedStatesToS2
    canonicalPropagatedCascadeClosedZeroModeSetTarget

canonicalOutputWidthConsequenceTarget : OutputWidthConsequenceTarget
canonicalOutputWidthConsequenceTarget =
  positiveGreatCircleAvoidanceWidthAfterPropagatedCollapse
    canonicalOutputProjectionTarget

canonicalLeiRenTianCompatibilityConsequence :
  LeiRenTianCompatibilityConsequence
canonicalLeiRenTianCompatibilityConsequence =
  lrtGreatCircleHittingForcesLeakageOutsidePropagatedZeroModeSheaf
    canonicalOutputWidthConsequenceTarget

------------------------------------------------------------------------
-- Local-calculation evidence rows.

data LocalHarnessObservation : Set where
  signAntisymmetryHoldsToRoundoffInDepthSweep :
    LocalHarnessObservation

  outputOnlyFamilyIIFamilyICompatibilityTooPermissive :
    LocalHarnessObservation

  propagatedCoherenceRejectsSampledDepthTwoSurvivors :
    LocalHarnessObservation

  jacobianRankGrowsAcrossPropagatedDepths :
    LocalHarnessObservation

  widthGrowsAsSurvivorSetShrinksInDepthSweep :
    LocalHarnessObservation

canonicalLocalHarnessObservations :
  List LocalHarnessObservation
canonicalLocalHarnessObservations =
  signAntisymmetryHoldsToRoundoffInDepthSweep
  ∷ outputOnlyFamilyIIFamilyICompatibilityTooPermissive
  ∷ propagatedCoherenceRejectsSampledDepthTwoSurvivors
  ∷ jacobianRankGrowsAcrossPropagatedDepths
  ∷ widthGrowsAsSurvivorSetShrinksInDepthSweep
  ∷ []

localHarnessObservationCount : Nat
localHarnessObservationCount =
  listLength canonicalLocalHarnessObservations

localHarnessObservationCountIs5 :
  localHarnessObservationCount ≡ 5
localHarnessObservationCountIs5 =
  refl

------------------------------------------------------------------------
-- Proof obligations, deliberately not discharged here.

data NSCascadeTransversalityCollapseObligation : Set where
  definePropagatedPolarizationStateSpaceT1S2TimesT1S2 :
    NSCascadeTransversalityCollapseObligation

  proveTrueLerayPolarizationCascadeMapMatchesFourierNS :
    NSCascadeTransversalityCollapseObligation

  provePropagatedCoherenceDefectIsNotOutputOnly :
    NSCascadeTransversalityCollapseObligation

  proveRankDKkEqualsKOffDegeneracyLocus :
    NSCascadeTransversalityCollapseObligation

  provePersistentGreatCircleComponentsCannotSurvive :
    NSCascadeTransversalityCollapseObligation

  provePositiveOutputWidthForPropagatedCascadeClosedSet :
    NSCascadeTransversalityCollapseObligation

  transferLeiRenTianOutputConditionToTriadicDefectMeasure :
    NSCascadeTransversalityCollapseObligation

  proveTriadicCompensatedLeakageIdentitySeparately :
    NSCascadeTransversalityCollapseObligation

  keepClayNavierStokesPromotionFalse :
    NSCascadeTransversalityCollapseObligation

canonicalTransversalityCollapseObligations :
  List NSCascadeTransversalityCollapseObligation
canonicalTransversalityCollapseObligations =
  definePropagatedPolarizationStateSpaceT1S2TimesT1S2
  ∷ proveTrueLerayPolarizationCascadeMapMatchesFourierNS
  ∷ provePropagatedCoherenceDefectIsNotOutputOnly
  ∷ proveRankDKkEqualsKOffDegeneracyLocus
  ∷ provePersistentGreatCircleComponentsCannotSurvive
  ∷ provePositiveOutputWidthForPropagatedCascadeClosedSet
  ∷ transferLeiRenTianOutputConditionToTriadicDefectMeasure
  ∷ proveTriadicCompensatedLeakageIdentitySeparately
  ∷ keepClayNavierStokesPromotionFalse
  ∷ []

transversalityCollapseObligationCount : Nat
transversalityCollapseObligationCount =
  listLength canonicalTransversalityCollapseObligations

transversalityCollapseObligationCountIs9 :
  transversalityCollapseObligationCount ≡ 9
transversalityCollapseObligationCountIs9 =
  refl

data FailClosedBlocker : Set where
  rankConditionNotProved :
    FailClosedBlocker

  persistentGreatCircleComponentExclusionNotProved :
    FailClosedBlocker

  outputWidthConsequenceNotProved :
    FailClosedBlocker

  lrtDefectMeasureTransferNotProved :
    FailClosedBlocker

  triadicCompensatedLeakageIdentityNotProved :
    FailClosedBlocker

  fullLocalDefectMonotonicityNotProved :
    FailClosedBlocker

  clayNavierStokesAuthorityAbsent :
    FailClosedBlocker

canonicalFailClosedBlockers : List FailClosedBlocker
canonicalFailClosedBlockers =
  rankConditionNotProved
  ∷ persistentGreatCircleComponentExclusionNotProved
  ∷ outputWidthConsequenceNotProved
  ∷ lrtDefectMeasureTransferNotProved
  ∷ triadicCompensatedLeakageIdentityNotProved
  ∷ fullLocalDefectMonotonicityNotProved
  ∷ clayNavierStokesAuthorityAbsent
  ∷ []

failClosedBlockerCount : Nat
failClosedBlockerCount =
  listLength canonicalFailClosedBlockers

failClosedBlockerCountIs7 :
  failClosedBlockerCount ≡ 7
failClosedBlockerCountIs7 =
  refl

------------------------------------------------------------------------
-- Receipt.

record NSCascadeTransversalityCollapseBoundaryReceipt : Set where
  constructor nsCascadeTransversalityCollapseBoundaryReceipt
  field
    correctedStateSpace :
      PropagatedPolarizationStatePair
    trueLerayCascadeMap :
      TrueLerayPolarizationCascadeMapTarget
    propagatedCoherenceConstraints :
      PropagatedCoherenceConstraintFamily
    transversalityRankTarget :
      JacobianRankConditionTarget
    collapseTarget :
      CascadeTransversalityCollapseTarget
    outputWidthTarget :
      OutputWidthConsequenceTarget
    leiRenTianConsequenceTarget :
      LeiRenTianCompatibilityConsequence
    localHarnessEvidence :
      List LocalHarnessObservation
    remainingObligations :
      List NSCascadeTransversalityCollapseObligation
    failClosedBlockers :
      List FailClosedBlocker

canonicalNSCascadeTransversalityCollapseBoundaryReceipt :
  NSCascadeTransversalityCollapseBoundaryReceipt
canonicalNSCascadeTransversalityCollapseBoundaryReceipt =
  nsCascadeTransversalityCollapseBoundaryReceipt
    canonicalInputStatePair
    canonicalTrueLerayPolarizationCascadeMapTarget
    canonicalPropagatedCoherenceConstraintFamily
    canonicalRankConditionTarget
    canonicalCascadeTransversalityCollapseTarget
    canonicalOutputWidthConsequenceTarget
    canonicalLeiRenTianCompatibilityConsequence
    canonicalLocalHarnessObservations
    canonicalTransversalityCollapseObligations
    canonicalFailClosedBlockers

------------------------------------------------------------------------
-- Promotion / theorem flags.

propagatedPolarizationStateSpaceRecorded :
  Bool
propagatedPolarizationStateSpaceRecorded =
  true

trueLerayPolarizationCascadeMapRecorded :
  Bool
trueLerayPolarizationCascadeMapRecorded =
  true

propagatedCoherenceConstraintsRecorded :
  Bool
propagatedCoherenceConstraintsRecorded =
  true

outputOnlyCascadeWidthTargetSuperseded :
  Bool
outputOnlyCascadeWidthTargetSuperseded =
  true

signAntisymmetryFiniteAlgebraAvailable :
  Bool
signAntisymmetryFiniteAlgebraAvailable =
  true

rankTransversalityTheoremProved :
  Bool
rankTransversalityTheoremProved =
  false

persistentGreatCircleComponentExcluded :
  Bool
persistentGreatCircleComponentExcluded =
  false

propagatedPolarizationOutputWidthProved :
  Bool
propagatedPolarizationOutputWidthProved =
  false

leiRenTianDefectMeasureTransferProved :
  Bool
leiRenTianDefectMeasureTransferProved =
  false

triadicCompensatedLeakageIdentityProved :
  Bool
triadicCompensatedLeakageIdentityProved =
  false

fullLocalDefectMonotonicityProved :
  Bool
fullLocalDefectMonotonicityProved =
  false

clayNavierStokesPromoted :
  Bool
clayNavierStokesPromoted =
  false

terminalClayPromotion :
  Bool
terminalClayPromotion =
  false

rankTransversalityTheoremStillFalse :
  rankTransversalityTheoremProved ≡ false
rankTransversalityTheoremStillFalse =
  refl

propagatedPolarizationOutputWidthStillFalse :
  propagatedPolarizationOutputWidthProved ≡ false
propagatedPolarizationOutputWidthStillFalse =
  refl

triadicCompensatedLeakageIdentityStillFalse :
  triadicCompensatedLeakageIdentityProved ≡ false
triadicCompensatedLeakageIdentityStillFalse =
  refl

clayNavierStokesPromotionStillFalse :
  clayNavierStokesPromoted ≡ false
clayNavierStokesPromotionStillFalse =
  refl

terminalClayPromotionStillFalse :
  terminalClayPromotion ≡ false
terminalClayPromotionStillFalse =
  refl

boundarySummary :
  String
boundarySummary =
  "Corrected NS finite gate: propagated-polarization state space T1S2 x T1S2, true Leray cascade map, K_k transversality rank target, output-width/LRT consequence target, promotion=false."
