module DASHI.Moonshine.P11MarkedDeckCharacterHighestAlphaRegression where

open import DASHI.Core.Prelude

import DASHI.Cognition.PhaseEnrichedTrit as Phase
import DASHI.Foundations.Phase3RootCharacterWeldExact as Root
import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11MarkedQuaternionHeckeHighestAlphaRegression as Prior
import DASHI.Moonshine.P11MarkedX2S3HeckeDecompositionExact as Dec
import DASHI.Moonshine.P11MarkedX2JointHeckeFrobeniusSpectrumExact as Joint
import DASHI.Moonshine.P11MarkedX2DeckCharacterSeparationExact as Char
import DASHI.Moonshine.P11MarkedJointEigenspaceCharacterSplitExact as Split
import DASHI.Moonshine.P11MarkedObservationRefinementExact as Refinement
import DASHI.Moonshine.P37NonOggFullLevel2DeckCharacterControlExact as P37Deck

------------------------------------------------------------------------
-- PR #572 exact C3 character authority is genuinely reused.
------------------------------------------------------------------------

zetaCubedStillOne :
  Root.phaseMul Root.phaseZeta (Root.phaseMul Root.phaseZeta Root.phaseZeta)
  ≡ Root.phaseOne
zetaCubedStillOne = Root.zetaCubedIsOne

c3RowsRemainExact :
  Root.characterRow Phase.phase1
  ≡ (Phase.phase0 , (Phase.phase1 , Phase.phase2))
  ×
  Root.characterRow Phase.phase2
  ≡ (Phase.phase0 , (Phase.phase2 , Phase.phase1))
c3RowsRemainExact = Root.characterRow1Exact , Root.characterRow2Exact

------------------------------------------------------------------------
-- PR #576 complete arithmetic decomposition is consumed, not sampled.
------------------------------------------------------------------------

completeJointBlockMultiplicityThree :
  Joint.JointSpectrumBoundary.nonconstantEvenJointMultiplicity
    Joint.canonicalJointSpectrumBoundary
  ≡ 3
completeJointBlockMultiplicityThree = refl

completeJointBasisSpans :
  (observable : Joint.Observable5) →
  (state : Fine.P11Fine5) →
  Joint.reconstruct observable state ≡ observable state
completeJointBasisSpans = Joint.jointBasisSpans

completeCollisionC3Split :
  Split.collisionC3Multiplicity ≡ Char.c3Multiplicity 1 1 1
completeCollisionC3Split = refl

collisionSplitIsBrandtPlusStandard :
  Split.addC3Multiplicity Split.brandtPartC3Multiplicity Split.standardPartC3Multiplicity
  ≡ Split.collisionC3Multiplicity
collisionSplitIsBrandtPlusStandard = Split.collisionSplitIsBrandtPlusStandard

------------------------------------------------------------------------
-- The old arithmetic collision is preserved, not rewritten away.
------------------------------------------------------------------------

brandtStandardArithmeticCollision :
  Dec.brandtNewformFingerprint ≡ Dec.standardFingerprint
brandtStandardArithmeticCollision = Dec.brandtAndStandardFingerprintsCoincide

------------------------------------------------------------------------
-- Deck C3 character strictly refines that observation.
------------------------------------------------------------------------

brandtC3IsTrivial : Char.brandtC3Multiplicity ≡ Char.c3Multiplicity 1 0 0
brandtC3IsTrivial = Char.brandtRestrictionIsTrivial

standardC3IsNontrivialPair :
  Char.standardC3Multiplicity ≡ Char.c3Multiplicity 0 1 1
standardC3IsNontrivialPair = Char.standardRestrictionIsConjugatePair

brandtStandardSeparatedByDeckCharacter :
  Char.brandtExtendedFingerprint ≡ Char.standardExtendedFingerprint → ⊥
brandtStandardSeparatedByDeckCharacter = Char.extendedFingerprintsSeparate

coarseCannotDecodeSector : Refinement.SectorDecoder → ⊥
coarseCannotDecodeSector = Refinement.coarseObservationHasNoExactSectorDecoder

------------------------------------------------------------------------
-- Reflection then separates sign from the one-dimensional trivial deck type.
------------------------------------------------------------------------

signVsBrandtReflectionSeparation :
  Char.signDeckObservation ≡ Char.brandtDeckObservation → ⊥
signVsBrandtReflectionSeparation = Char.signAndTrivialSeparatedByReflection

------------------------------------------------------------------------
-- Non-Ogg p=37 control target available before marked T3/T5 reconstruction.
------------------------------------------------------------------------

p37S3MultiplicityPrediction :
  P37Deck.p37MarkedS3Multiplicity ≡ P37Deck.s3Multiplicity 3 3 6
p37S3MultiplicityPrediction = refl

p37C3MultiplicityPrediction :
  P37Deck.p37MarkedC3Multiplicity ≡ P37Deck.c3Multiplicity 6 6 6
p37C3MultiplicityPrediction = refl

p37RepresentationDimensionIsEighteen :
  P37Deck.trivialMultiplicity P37Deck.p37MarkedS3Multiplicity
  + P37Deck.signMultiplicity P37Deck.p37MarkedS3Multiplicity
  + 2 * P37Deck.standardMultiplicity P37Deck.p37MarkedS3Multiplicity
  ≡ 18
p37RepresentationDimensionIsEighteen = P37Deck.p37MarkedS3DimensionCheck

------------------------------------------------------------------------
-- Prior p=11 marked quaternion reconstruction remains imported as the source
-- arithmetic lane; this regression only adds the missing observation coordinate.
------------------------------------------------------------------------

p11ThetaCountsStillSourceNative : Prior.p11MarkedFrobeniusFixedCount ≡ 3
p11ThetaCountsStillSourceNative = refl
