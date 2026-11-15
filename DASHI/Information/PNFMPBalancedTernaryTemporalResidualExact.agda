module DASHI.Information.PNFMPBalancedTernaryTemporalResidualExact where

-- Original DASHI finite time-domain consumer of the existing sibling
-- TriadicVideoCodecObservationQuotient.BalancedTernarySymbol carrier.
-- It is NOT the dashitest motion codec, serialized entropy code,
-- measured bit rate, stochastic null, or evidence of malicious intent.
-- Shows the minimum predictor-residual coordinate needed to separate
-- the two chronological sequences with equal static MP covariance.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Combinatorics.TriadicVideoCodecObservationQuotient as Codec
import DASHI.Information.PNFMPTemporalOrderingNonIdentificationExact as Time

-- The original four sample values are 0/1; this definition clips a
-- general Nat to the binary demonstration carrier. No physiological
-- or other real-valued time series is discretised here.
delta : Nat → Nat → Codec.BalancedTernarySymbol
delta zero zero = Codec.zeroTrit
delta zero (suc _) = Codec.posTrit
delta (suc _) zero = Codec.negTrit
delta (suc _) (suc _) = Codec.zeroTrit

predictNext : Nat → Codec.BalancedTernarySymbol → Nat
predictNext old Codec.zeroTrit = old
predictNext old Codec.negTrit = zero
predictNext old Codec.posTrit = 1

-- For each source-owned history the three signed (next - current)
-- predictor residuals are exactly known.
residual12 : Time.TimeOrder → Codec.BalancedTernarySymbol
residual12 h = delta (Time.sample h Time.first) (Time.sample h Time.second)

residual23 : Time.TimeOrder → Codec.BalancedTernarySymbol
residual23 h = delta (Time.sample h Time.second) (Time.sample h Time.third)

residual34 : Time.TimeOrder → Codec.BalancedTernarySymbol
residual34 h = delta (Time.sample h Time.third) (Time.sample h Time.fourth)

residualStream : Time.TimeOrder → List Codec.BalancedTernarySymbol
residualStream h = residual12 h ∷ residual23 h ∷ residual34 h ∷ []

-- Decoder includes the first sample as explicit side information,
-- then reconstructs all four 0/1 observations in chronological order.
decodeThree : Nat → List Codec.BalancedTernarySymbol → List Nat
decodeThree x [] = x ∷ []
decodeThree x (step ∷ tail) =
  x ∷ decodeThree (predictNext x step) tail

originalSamples : Time.TimeOrder → List Nat
originalSamples h =
  Time.sample h Time.first ∷ Time.sample h Time.second ∷
  Time.sample h Time.third ∷ Time.sample h Time.fourth ∷ []

reconstructionAlternating :
  decodeThree (Time.sample Time.alternating Time.first)
    (residualStream Time.alternating)
    ≡ originalSamples Time.alternating
reconstructionAlternating = refl

reconstructionClustered :
  decodeThree (Time.sample Time.clustered Time.first)
    (residualStream Time.clustered)
    ≡ originalSamples Time.clustered
reconstructionClustered = refl

reconstructionForBoth :
  (h : Time.TimeOrder) →
  decodeThree (Time.sample h Time.first) (residualStream h)
    ≡ originalSamples h
reconstructionForBoth Time.alternating = reconstructionAlternating
reconstructionForBoth Time.clustered = reconstructionClustered

-- A model-independent *symbol count* for nonzero residuals.
-- This is NOT entropy-coded bits or rate-distortion.
nonzero : Codec.BalancedTernarySymbol → Nat
nonzero Codec.zeroTrit = 0
nonzero Codec.negTrit = 1
nonzero Codec.posTrit = 1

changeCount : Time.TimeOrder → Nat
changeCount h =
  nonzero (residual12 h) +
  nonzero (residual23 h) +
  nonzero (residual34 h)

alternatingThreeChanges : changeCount Time.alternating ≡ 3
alternatingThreeChanges = refl

clusteredOneChange : changeCount Time.clustered ≡ 1
clusteredOneChange = refl

signedResidualChangeCountDiffers :
  changeCount Time.alternating ≡ changeCount Time.clustered → ⊥
signedResidualChangeCountDiffers ()

-- The old static moment observer provably cannot reconstruct this new
-- selected chronological residual count, even if given arbitrary
-- charting/MP spectral postprocessing.
sameStaticMPDifferentResidualCount :
  NF.NonFactorabilityWitness Time.staticMoments changeCount
sameStaticMPDifferentResidualCount =
  NF.nonFactorabilityWitness
    Time.alternating Time.clustered
    Time.sameStaticMoments signedResidualChangeCountDiffers

staticMPCannotPredictSignedResidualWork :
  NF.FactorsThrough Time.staticMoments changeCount → ⊥
staticMPCannotPredictSignedResidualWork =
  NF.witnessRulesOutEveryFlatFactorisation
    sameStaticMPDifferentResidualCount

-- The signed residual is a legitimate extra observation for this
-- finite synthetic sample. To use the real video codec one must still
-- pay its predictor, side-bit, decoder, equality/correction, entropy
-- serialization and source-provenance gates.
