module DASHI.Physics.YangMills.BalabanSmallPolymerTaylorNormalizationExact where

------------------------------------------------------------------------
-- ROUND66: EXACT FOUR-CHANNEL SMALL-POLYMER NORMALIZATION
--
-- PRIMARY SOURCES / CALIBRATION
--
-- David C. Brydges, John Dimock and Thomas R. Hurd,
-- "Estimates on Renormalization Group Transformations",
-- Canadian Journal of Mathematics 50 (1998), 756--793.
-- DOI: 10.4153/CJM-1998-041-5.
--
-- David C. Brydges, P. K. Mitter and B. Scoppola,
-- "Critical (Phi^4)_{3,epsilon}", Communications in Mathematical Physics
-- 240 (2003), 281--327. DOI: 10.1007/s00220-003-0895-4.
--
-- P. K. Mitter, "A non trivial fixed point in a three dimensional quantum
-- field theory", Oberwolfach Report 17/2006, The Rigorous Renormalization
-- Group. DOI of report: 10.4171/OWR/2006/17.
--
-- DASHI CONTRIBUTION
--
-- Small-set extraction is represented by the four finite Taylor coordinates
-- used by the constructive RG normalization boundary:
--
--   J(X,0),
--   D2 J(X,0;1,1),
--   D2 J(X,0;1,x_mu),
--   D4 J(X,0;1,1,1,1).
--
-- On the coefficient carrier itself, extracting exactly those four coordinates
-- and subtracting them annihilates every relevant/marginal channel by exact
-- rational algebra.  Therefore the physical YM problem is not to prove this
-- cancellation again: it is to construct the SAME four coefficients from the
-- literal gauge polymer activity and bound the normalized remainder in the
-- corrected unified norm.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _-_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel

data SmallPolymerTaylorChannel : Set where
  valueAtZero : SmallPolymerTaylorChannel
  quadraticConstant : SmallPolymerTaylorChannel
  quadraticFirstMoment : SmallPolymerTaylorChannel
  quarticConstant : SmallPolymerTaylorChannel

record SmallPolymerTaylorJet : Set where
  constructor jet
  field
    j0 j2Constant j2FirstMoment j4Constant : ℚ

open SmallPolymerTaylorJet public

zeroJet : SmallPolymerTaylorJet
zeroJet = jet 0ℚ 0ℚ 0ℚ 0ℚ

subtractJet : SmallPolymerTaylorJet → SmallPolymerTaylorJet → SmallPolymerTaylorJet
subtractJet left right = jet
  (j0 left - j0 right)
  (j2Constant left - j2Constant right)
  (j2FirstMoment left - j2FirstMoment right)
  (j4Constant left - j4Constant right)

-- Extraction on the four-coordinate jet is identity: the relevant part is the
-- finite jet itself.  The remainder jet therefore vanishes exactly.
extractRelevantJet : SmallPolymerTaylorJet → SmallPolymerTaylorJet
extractRelevantJet jetData = jetData

normalizedRemainderJet : SmallPolymerTaylorJet → SmallPolymerTaylorJet
normalizedRemainderJet jetData =
  subtractJet jetData (extractRelevantJet jetData)

normalizedJ0Zero : ∀ jetData →
  j0 (normalizedRemainderJet jetData) ≡ 0ℚ
normalizedJ0Zero jetData = ℚRing.solve-∀ (j0 jetData)

normalizedJ2ConstantZero : ∀ jetData →
  j2Constant (normalizedRemainderJet jetData) ≡ 0ℚ
normalizedJ2ConstantZero jetData = ℚRing.solve-∀ (j2Constant jetData)

normalizedJ2FirstMomentZero : ∀ jetData →
  j2FirstMoment (normalizedRemainderJet jetData) ≡ 0ℚ
normalizedJ2FirstMomentZero jetData = ℚRing.solve-∀ (j2FirstMoment jetData)

normalizedJ4ConstantZero : ∀ jetData →
  j4Constant (normalizedRemainderJet jetData) ≡ 0ℚ
normalizedJ4ConstantZero jetData = ℚRing.solve-∀ (j4Constant jetData)

record FourChannelNormalized (jetData : SmallPolymerTaylorJet) : Set where
  field
    valueZero : j0 jetData ≡ 0ℚ
    quadraticConstantZero : j2Constant jetData ≡ 0ℚ
    quadraticFirstMomentZero : j2FirstMoment jetData ≡ 0ℚ
    quarticConstantZero : j4Constant jetData ≡ 0ℚ

open FourChannelNormalized public

extractionProducesFourChannelNormalization :
  ∀ jetData → FourChannelNormalized (normalizedRemainderJet jetData)
extractionProducesFourChannelNormalization jetData = record
  { valueZero = normalizedJ0Zero jetData
  ; quadraticConstantZero = normalizedJ2ConstantZero jetData
  ; quadraticFirstMomentZero = normalizedJ2FirstMomentZero jetData
  ; quarticConstantZero = normalizedJ4ConstantZero jetData
  }

smallPolymerFourChannelExtractionAlgebraLevel : ProofLevel
smallPolymerFourChannelExtractionAlgebraLevel = machineChecked

-- Physical finite calculation: construct these four jets from each literal
-- small YM polymer (at most eight blocks in the Round66 extraction boundary)
-- and prove the corrected-norm bound for the remainder.
physicalYMSmallPolymerTaylorJetLevel : ProofLevel
physicalYMSmallPolymerTaylorJetLevel = conditional

physicalYMNormalizedSmallPolymerRemainderBoundLevel : ProofLevel
physicalYMNormalizedSmallPolymerRemainderBoundLevel = conditional
