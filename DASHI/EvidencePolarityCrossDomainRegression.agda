module DASHI.EvidencePolarityCrossDomainRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (proj₁; proj₂)

import DASHI.Algebra.BalancedTernaryOppositionEvidenceBridgeExact as GeometricEvidence
import DASHI.Algebra.ClaimIndexedEvidencePolarityExact as Indexed
import DASHI.Algebra.DisagreementFourViewBoundary as Four
import DASHI.Biology.BrainProxyEvidenceAuthorityBridgeExact as Brain
import DASHI.Biology.IntersectionalClaimEvidenceFibreExact as Intersectional
import DASHI.Chemistry.EvidenceObligationAuthorityBridgeExact as Chemistry
import DASHI.Cognition.PNF.BinaryBalancedTernaryAggregateLossExact as Aggregate
import DASHI.Core.EvidenceObligationAuthoritySeparationExact as Governed
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit
import DASHI.Foundations.Base369InteractionAntipodalFibreExact as Interaction
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.TernaryNineAntipodalD4SeparationExact as D4Sep
import DASHI.Physics.Chemistry.AtomicEvidenceObligationBridgeExact as Atomic
import DASHI.Reasoning.HyperfabricHypervoxelEvidencePolarityBridgeExact as Hyper
import DASHI.Reasoning.RelationalLensSynthesisCore as Lens

conflictStillRetained :
  Indexed.conflict ≡ Four.assess true true
conflictStillRetained = Indexed.conflictIsBoth

contextualCounterpositionStillNotLogicalNegation :
  Lens.contextualCounterpositionRole ≡ Lens.logicalNegationRole → ⊥
contextualCounterpositionStillNotLogicalNegation =
  Indexed.contextualCounterpositionRoleIsNotLogicalNegation

orientationReversalStillNotLogicalNegation :
  Lens.orientationReversalRole ≡ Lens.logicalNegationRole → ⊥
orientationReversalStillNotLogicalNegation =
  Indexed.orientationReversalRoleIsNotLogicalNegation

strictAntipodeStillCannotSelfQualifyAsLogicalNegation :
  Indexed.LogicalNegationQualified GeometricEvidence.positiveStrictAntipodeOpposition → ⊥
strictAntipodeStillCannotSelfQualifyAsLogicalNegation =
  GeometricEvidence.positiveAntipodeCannotSelfQualifyAsLogicalNegation

opposingSupportDoesNotSelfQualifyAsNegation :
  Indexed.ClaimIndexedEvidencePolarityBoundary.opposingSupportAutomaticallyMeansLogicalNegation
    Indexed.canonicalClaimIndexedEvidencePolarityBoundary
  ≡ false
opposingSupportDoesNotSelfQualifyAsNegation = refl

supportStillLeavesObligationOpen :
  Governed.obligations Governed.supportOnlyOpen ≡ Governed.obligationsOpen
supportStillLeavesObligationOpen = Governed.supportDoesNotDischargeObligations

dischargedTechnicalObligationsStillCannotOpenLocalAuthority :
  Governed.localPromotion Governed.supportOnlyDischarged ≡ false
dischargedTechnicalObligationsStillCannotOpenLocalAuthority =
  Governed.dischargedObligationsDoNotOpenAuthorityGate

conflictStillCannotOpenAuthority :
  Governed.localPromotion Governed.conflictDischarged ≡ false
conflictStillCannotOpenAuthority = Governed.conflictDoesNotOpenAuthorityGate

brainProxySupportStillNonPromoting :
  Governed.localPromotion Brain.proxyObservationSupportedOnly ≡ false
brainProxySupportStillNonPromoting = Brain.proxySupportDoesNotPromoteHiddenState

chemistrySupportStillNonPromoting :
  Governed.localPromotion Chemistry.chemistryCandidateSupportedButNotPromotable
  ≡ false
chemistrySupportStillNonPromoting =
  Chemistry.chemistryCandidateSupportDoesNotPromote

atomicSupportStillNonPromoting :
  Governed.localPromotion Atomic.atomicCandidateSupportedOnly ≡ false
atomicSupportStillNonPromoting =
  Atomic.atomicCandidateSupportDoesNotPromoteRecovery

intersectionalContextAlignmentRequired :
  Intersectional.IntersectionalClaimEvidenceBoundary.explicitAlignmentRequiredAcrossContexts
    Intersectional.canonicalIntersectionalClaimEvidenceBoundary
  ≡ true
intersectionalContextAlignmentRequired = refl

hyperfabricDoesNotDiagnose :
  Hyper.HyperfabricHypervoxelEvidenceBoundary.hyperfabricAutomaticallyDiagnosesClaimed
    Hyper.canonicalHyperfabricHypervoxelEvidenceBoundary
  ≡ false
hyperfabricDoesNotDiagnose = refl

zeroStillFixedUnderStrictAntipode :
  Orbit.strictAntipode SSP.sspZero ≡ SSP.sspZero
zeroStillFixedUnderStrictAntipode = Orbit.zeroIsAntipodeFixedCentre

zeroStillNotNegativePole : SSP.sspZero ≡ SSP.sspNegOne → ⊥
zeroStillNotNegativePole = Orbit.zeroIsNotNegativePole

nineAntipodalClassesStillFive : Orbit.antipodalClass9Count ≡ 5
nineAntipodalClassesStillFive = Orbit.antipodalClass9CountIsFive

twentySevenAntipodalClassesStillFourteen : Orbit.antipodalClass27Count ≡ 14
twentySevenAntipodalClassesStillFourteen = Orbit.antipodalClass27CountIsFourteen

repoNativeThreeCubeCarrierStill19683 : Interaction.fineInteractionStateCount ≡ 19683
repoNativeThreeCubeCarrierStill19683 = Interaction.fineInteractionStateCountIs19683

blockwiseOrientationBaseStill2744 : Interaction.blockOrientationClassCount ≡ 2744
blockwiseOrientationBaseStill2744 = Interaction.blockOrientationClassCountIs2744

allNoncentralBlockOrientationFibreStillEight :
  Interaction.allThreeNoncentralOrientationFibreSize ≡ 8
allNoncentralBlockOrientationFibreStillEight =
  Interaction.allThreeNoncentralOrientationFibreSizeIsEight

aggregateZeroStillHasNontrivialFineFibre :
  Interaction.aggregateSum Interaction.structuralZeroRound
  ≡ Interaction.aggregateSum Interaction.cancellationZeroRound
aggregateZeroStillHasNontrivialFineFibre =
  proj₁ Interaction.cancellationToNeutralDoesNotImplyTrivialFineState

aggregateZeroDoesNotIdentifyFineStates :
  Interaction.structuralZeroRound ≡ Interaction.cancellationZeroRound → ⊥
aggregateZeroDoesNotIdentifyFineStates =
  proj₂ Interaction.cancellationToNeutralDoesNotImplyTrivialFineState

binaryCountStillErasesDisagreementDirection :
  Aggregate.acceptCount (Aggregate.binaryProjectPositiveOnly Aggregate.forwardDisagreement)
  ≡ Aggregate.acceptCount (Aggregate.binaryProjectPositiveOnly Aggregate.reverseDisagreement)
binaryCountStillErasesDisagreementDirection =
  Aggregate.aggregateErasesDisagreementDirection

halfPointStillComplementFixed :
  Aggregate.complementPoint Aggregate.probabilityHalf ≡ Aggregate.probabilityHalf
halfPointStillComplementFixed = Aggregate.halfIsComplementFixed

fiveAntipodalClassesStillNotFiveD4IrrepSpecies :
  D4Sep.TernaryNineAntipodalD4Boundary.fiveAntipodalOrbitClassesAreFiveD4IrrepSpecies
    D4Sep.canonicalTernaryNineAntipodalD4Boundary
  ≡ false
fiveAntipodalClassesStillNotFiveD4IrrepSpecies = refl
