module DASHI.Moonshine.Y443VNaturalPairGenerationValidation where

------------------------------------------------------------------------
-- Focused golden root: finite Y443 relators and constructive literal
-- V-natural action transport; keep the Suzuki 12 distinct from Y443 12.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y443
import DASHI.Moonshine.Y443VNaturalPairGenerationExact as Pair
import DASHI.Moonshine.Y443JMDTracePowerExact as JMD
import DASHI.Moonshine.Y443JMDSourceWordInstantiationExact as JMDSource
import DASHI.Moonshine.Y443JMDConcretePairPowerCompilerExact as JMDCertificate
import DASHI.Moonshine.Y443JMDPowerFiveSixAlgebraExact as JMDPowerProof
import DASHI.Moonshine.Y443JMDThreePathGraphCertificateExact as JMDPaths
import DASHI.Moonshine.Y443JMDSquareFromPresentationExact as JMDSquare
import DASHI.Moonshine.Y443JMDNonadjacentRelatorConsequencesExact as JMDNonadjacent
import DASHI.Moonshine.Y443JMDFromRelatorsToPowerExact as JMDFromRelators
import DASHI.Moonshine.Y443JMDBetaFiveFiniteRewriteExact as BetaRewrite
import DASHI.Moonshine.Y443JMDBetaFiveSemanticCompilerExact as BetaSemantics
import DASHI.Moonshine.Y443CoxeterRelatorSemanticLawsExact as CoxeterLaws
import DASHI.Moonshine.Y443JMDA4RulesFromPresentationExact as ActualBeta
import DASHI.Moonshine.Y443Monster3BTwelveDisjointExact as H3
import DASHI.Moonshine.Y443ArmSwapOrbitMaxCutExact as Orbit
import DASHI.Moonshine.Y443Relator72IndexedBidiExact as Indexed
import DASHI.Moonshine.Y443Nonary72EquivarianceNoGoExact as NoGo
import DASHI.Moonshine.Monster3BNormalizerBridge as N3B

coxeterTwelveMatchesSuzukiDegreeNumerically :
  Y443.length Y443.nodes ≡ N3B.naturalSuzukiDegree
coxeterTwelveMatchesSuzukiDegreeNumerically = refl

coxeterTwelveIsNotSuzukiCoordinateIdentity :
  Y443.coxeterInvolutionAlphabet ≡ Y443.suzukiDegreeTwelve → ⊥
coxeterTwelveIsNotSuzukiCoordinateIdentity =
  Y443.distinctTwelveRoles

y443RelatorCountIsEighty :
  Y443.length Y443.monsterRelators ≡ 80
y443RelatorCountIsEighty = Y443.monsterRelatorCount

y443WrittenLengthIsFourSixtyThree :
  Y443.wordLengthSum Y443.monsterRelators ≡ 463
y443WrittenLengthIsFourSixtyThree = Y443.monsterWrittenLength

import DASHI.Moonshine.Y443JMDAllTwelveNodeWordCompilerExact as NodeRecovery

import DASHI.Moonshine.Y443JMDThreePathFiniteRewriteExact as ElevenFinite
import DASHI.Moonshine.Y443JMDPathShiftSemanticCompilerExact as ElevenSemantics
import DASHI.Moonshine.Y443AllCoxeterGraphLawsFrom80Exact as FullGraphSource
import DASHI.Moonshine.Y443PresentedGroupNodeGenerationExact as PresentedGeneration
import DASHI.Moonshine.Y443JMDAllTwelveNodeWordCompilerExact as AllTwelve
import DASHI.Moonshine.Y443JMDPresentedVNaturalCapstoneExact as PresentedCapstone
import DASHI.Moonshine.Y443MonsterGradedLiteralSameObjectCapstoneExact as ActualVnatural

import DASHI.Moonshine.Y443FLMGriessFullAutSelectedVOAExact as FLMSelected
import DASHI.Moonshine.Y443TwoGeneratorSameVOAActionExact as JMDTwoGeneratorAction
import DASHI.Moonshine.Y443FLMDirectSameObjectCapstoneExact as FLMDirectCapstone
import DASHI.Moonshine.Y443FLMConcreteVOAGroupTransportExact as FLMConcreteTransport
import DASHI.Moonshine.Y443FLMConcreteSameObjectActionClosureExact as FLMConcreteActionClosure
import DASHI.Moonshine.Y443FLMWeightTwoOnlyUVExact as FLMWeightTwoUV
import DASHI.Moonshine.Y443FLMWeightTwoBasisUVExact as FLMBasisUV
import DASHI.Moonshine.Y443FLMFiniteBasisUVEndcapExact as FLMBasisEndcap
import DASHI.Moonshine.Y443PublishedQuotientIsoCompositionExact as Y443PublishedMonsterIso
import DASHI.Moonshine.Y443FLMGriessGeneratorUVExact as FLMGriessGenerators
import DASHI.Moonshine.Y443FLMGriessGeneratorsUVEndcapExact as FLMGriessSeedEndcap
import DASHI.Moonshine.Y443FLMCanonicalReferenceFromQuotientExact as FLMTrueCanonicalReference
import DASHI.Moonshine.Y443DGLUniquenessSelectedFLMExact as DGLSelectedUniqueness
import DASHI.Moonshine.Y443FLMWeakVOACoreNoPromotionExact as WeakFLMCountermodel
import DASHI.Moonshine.Y443DGLWeakCertificateNoGoExact as DGLWeakRouteNoGo