module DASHI.Reasoning.TernarySynthesisOrbitWeldRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)
open import Data.Integer using (+_; -[1+_])

import Base369 as Base
import DASHI.Biology.JFineCoarseRelativeScaleExact as JScale
import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Foundations.DialecticCubieTetralemmaExact as Tetra
import DASHI.Foundations.HexTruthS3CarrierBridgeExact as HexS3
import DASHI.Foundations.NaryCyclicOutputPhaseCountExact as Nary
import DASHI.Foundations.SignedZeroTernaryOrientationExact as Signed
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Conj
import DASHI.Foundations.TernaryEndomorphismPhaseQuotientExact as Phase
import DASHI.Foundations.TernaryEndomorphismS3ActionLawsExact as Action
import DASHI.Foundations.TernaryPermutationS3LawsExact as S3
import DASHI.Moonshine.TernarySevenOggSSPComparisonExact as Ogg
import DASHI.Physics.ShiftDiscreteWaveStep as Wave
import DASHI.Reasoning.RelationalLensSynthesisCore as Lens
import DASHI.Reasoning.TernaryComparisonSynthesisExact as Synthesis
import DASHI.Reasoning.TernarySynthesisLogicQualificationExact as Logic
import DASHI.Reasoning.TernarySynthesisTransportWeldExact as Transport

------------------------------------------------------------------------
-- 27 = C3 phase x (2 reversible + 7 nonunit).
------------------------------------------------------------------------

phaseQuotientIsNine : Phase.phaseQuotientCardinality ≡ 9
phaseQuotientIsNine = Phase.phaseQuotientIsNine

phaseFactorizationIsTwentySeven :
  Phase.factorizedCardinality ≡ 27
phaseFactorizationIsTwentySeven = Phase.factorizedIsTwentySeven

phaseTwoPlusSevenIsNine : 2 + 7 ≡ Phase.phaseQuotientCardinality
phaseTwoPlusSevenIsNine = refl

naryTernarySpecializationIsNine :
  Nary.phaseQuotientCount Nary.ternaryCount ≡ 9
naryTernarySpecializationIsNine =
  Nary.ternaryPhaseQuotientCountIsNine

------------------------------------------------------------------------
-- Exact S3 group and seven conjugation shapes.
------------------------------------------------------------------------

conjugacyShapeCountIsSeven :
  Conj.listCount Conj.allShapeOrbits ≡ 7
conjugacyShapeCountIsSeven = Conj.shapeOrbitCountIsSeven

conjugacyOrbitSizesSumToTwentySeven :
  Conj.shapeOrbitSize Conj.identityShape
  + Conj.shapeOrbitSize Conj.threeCycleShape
  + Conj.shapeOrbitSize Conj.transpositionShape
  + Conj.shapeOrbitSize Conj.constantShape
  + Conj.shapeOrbitSize Conj.rank2OneFixedShape
  + Conj.shapeOrbitSize Conj.rank2TwoFixedShape
  + Conj.shapeOrbitSize Conj.rank2TwoCycleShape
  ≡ 27
conjugacyOrbitSizesSumToTwentySeven =
  Conj.shapeOrbitSizesSumToTwentySeven

s3IsNonAbelian :
  S3._∙_ Conj.permRotate Conj.permSwapLowMid
  ≡ S3._∙_ Conj.permSwapLowMid Conj.permRotate → ⊥
s3IsNonAbelian = S3.nonCommutativeWitness

conjugationIdentityActsTrivially :
  (code : Tower.LevelTwoCode) →
  Conj.conjugateCode Conj.permIdentity code ≡ code
conjugationIdentityActsTrivially = Action.conjugateIdentity

------------------------------------------------------------------------
-- Existing cyclic HexTruth remains a distinct sixfold operation.
------------------------------------------------------------------------

hexS3CarrierRoundTrip :
  (hex : Base.HexTruth) →
  HexS3.permutationToHex (HexS3.hexToPermutation hex) ≡ hex
hexS3CarrierRoundTrip = HexS3.hexRoundTrip

hexProductCannotBeS3ProductUnderTheCarrierChart :
  ((left right : Base.HexTruth) →
    HexS3.hexToPermutation (Base.hexXor left right)
    ≡ S3._∙_
      (HexS3.hexToPermutation left)
      (HexS3.hexToPermutation right)) →
  ⊥
hexProductCannotBeS3ProductUnderTheCarrierChart =
  HexS3.hexCarrierChartCannotPreserveBothProducts

------------------------------------------------------------------------
-- Signed-neutral completion retains -0 / 0 / +0.
------------------------------------------------------------------------

signedNeutralRotationHasOrderThree :
  (phase : Signed.SignedNeutralPhase3) →
  Signed.rotateSignedNeutral
    (Signed.rotateSignedNeutral (Signed.rotateSignedNeutral phase))
  ≡ phase
signedNeutralRotationHasOrderThree =
  Signed.rotateSignedNeutralOrderThree

centreHasNoDirectedSignedZero :
  Signed.signedZeroWitness Signed.neutralZeroPhase ≡ Signed.none
centreHasNoDirectedSignedZero =
  Signed.centreCarriesNoDirectedSignedZero

------------------------------------------------------------------------
-- Comparison+synthesis and higher-order logical qualification.
------------------------------------------------------------------------

comparisonCarrierIsNine : Synthesis.comparisonDimension ≡ 9
comparisonCarrierIsNine = Synthesis.comparisonDimensionIsNine

synthesisCarrierIsTwentySeven :
  Synthesis.synthesisChoiceDimension ≡ 27
synthesisCarrierIsTwentySeven =
  Synthesis.synthesisChoiceDimensionIsTwentySeven

bothSupportRemainsTetralemmaQualified :
  (choice : Synthesis.SynthesisChoice27) →
  Logic.tetralemmaPosition (Logic.bothSupportedQualification choice)
  ≡ Tetra.bothSupported
bothSupportRemainsTetralemmaQualified =
  Logic.bothPositionIsBothSupported

lensReversalIsNotLogicalNegation :
  Lens.orientationReversalRole ≡ Lens.logicalNegationRole → ⊥
lensReversalIsNotLogicalNegation =
  Lens.orientationReversalIsNotLogicalNegation

------------------------------------------------------------------------
-- Existing j-coarse/j-fine wave/Hodge transport witnesses.
------------------------------------------------------------------------

canonicalTransportDefectIsZero :
  Transport.transportDefect Transport.canonicalOneToThreeSynthesis
  ≡ Wave.mkDiscreteWave (+ 0) (+ 0)
canonicalTransportDefectIsZero =
  Transport.canonicalSynthesisDefectIsZero

phaseChangedTransportDefectIsNonzeroWitness :
  Transport.transportDefect Transport.phaseChangedSynthesis
  ≡ Wave.mkDiscreteWave (-[1+ 0 ]) (+ 1)
phaseChangedTransportDefectIsNonzeroWitness =
  Transport.phaseChangedSynthesisDefectExact

jCoarseIsNine : JScale.jCoarseFrequency ≡ 9
jCoarseIsNine = Transport.jCoarseIsNine

jFineIsThreePowerNine : JScale.jFineFrequency ≡ 19683
jFineIsThreePowerNine = Transport.jFineIsThreePowerNine

------------------------------------------------------------------------
-- Ogg / SSP seven lanes are compared, not identified.
------------------------------------------------------------------------

oggMirrorAIsSeven : Ogg.listCount Ogg.oggMirrorASeven ≡ 7
oggMirrorAIsSeven = Ogg.oggMirrorACountIsSeven

oggMirrorBIsSeven : Ogg.listCount Ogg.oggMirrorBSeven ≡ 7
oggMirrorBIsSeven = Ogg.oggMirrorBCountIsSeven

phaseNonunitCarrierIsSeven :
  Ogg.listCount Ogg.phaseNonUnitSeven ≡ 7
phaseNonunitCarrierIsSeven = Ogg.phaseNonUnitCountIsSeven

conjugacyShapeCarrierIsSeven :
  Ogg.listCount Ogg.shapeOrbitSeven ≡ 7
conjugacyShapeCarrierIsSeven = Ogg.shapeOrbitCountIsSeven
