module DASHI.Physics.YangMills.BalabanRegular240MarginalCouplingExact where

-- Finite information-loss theorem on the ACTUAL newly constructed
-- Round56 support-mask × F4 half-root sign carrier.
-- A complete pair coordinate is lossless; two independent marginal
-- histograms erase its source-specific incidence/coupling.
-- This is a synthetic mathematical witness, not physical integrand data.
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Physics.YangMills.BalabanRegular240SupportHalfExact as Pair
import DASHI.Physics.YangMills.BalabanRankTwoF4LongHalfIncidenceExact as F4

maskA maskB : Pair.Mask4
maskA = Pair.mask4 true false false false
maskB = Pair.mask4 false true false false

signA signB : F4.Half4
signA = F4.half4 F4.positive F4.positive F4.positive F4.positive
signB = F4.half4 F4.negative F4.negative F4.negative F4.negative

data Coupling : Set where
  aligned crossed : Coupling

firstPair : Coupling → Pair.SupportHalf256
firstPair aligned = Pair.supportHalf256 maskA signA
firstPair crossed = Pair.supportHalf256 maskA signB

secondPair : Coupling → Pair.SupportHalf256
secondPair aligned = Pair.supportHalf256 maskB signB
secondPair crossed = Pair.supportHalf256 maskB signA

maskACount maskBCount : Pair.Mask4 → Nat
maskACount (Pair.mask4 true false false false) = 1
maskACount _ = 0
maskBCount (Pair.mask4 false true false false) = 1
maskBCount _ = 0

signACount signBCount : F4.Half4 → Nat
signACount (F4.half4 F4.positive F4.positive F4.positive F4.positive) = 1
signACount _ = 0
signBCount (F4.half4 F4.negative F4.negative F4.negative F4.negative) = 1
signBCount _ = 0

record SeparateMarginals : Set where
  constructor counts
  field
    supportA supportB halfA halfB : Nat

-- These counts depend on the actual pairs, but forget pair identity.
marginals : Coupling → SeparateMarginals
marginals a = counts
  (maskACount (Pair.supportMask (firstPair a)) +
   maskACount (Pair.supportMask (secondPair a)))
  (maskBCount (Pair.supportMask (firstPair a)) +
   maskBCount (Pair.supportMask (secondPair a)))
  (signACount (Pair.halfRootSigns (firstPair a)) +
   signACount (Pair.halfRootSigns (secondPair a)))
  (signBCount (Pair.halfRootSigns (firstPair a)) +
   signBCount (Pair.halfRootSigns (secondPair a)))

sameSeparateMarginals :
  marginals aligned ≡ marginals crossed
sameSeparateMarginals = refl

-- Distinguishes the original correspondence of maskA to signA.
matchingJointCell : Pair.SupportHalf256 → Nat
matchingJointCell
  (Pair.supportHalf256
    (Pair.mask4 true false false false)
    (F4.half4 F4.positive F4.positive F4.positive F4.positive)) = 1
matchingJointCell _ = 0

jointIncidence : Coupling → Nat
jointIncidence a =
  matchingJointCell (firstPair a) +
  matchingJointCell (secondPair a)

alignedIncidenceOne : jointIncidence aligned ≡ 1
alignedIncidenceOne = refl

crossedIncidenceZero : jointIncidence crossed ≡ 0
crossedIncidenceZero = refl

differentOriginalCoupling :
  jointIncidence aligned ≡ jointIncidence crossed → ⊥
differentOriginalCoupling ()

marginalsLoseOriginalCoupling :
  NF.NonFactorabilityWitness marginals jointIncidence
marginalsLoseOriginalCoupling =
  NF.nonFactorabilityWitness
    aligned crossed sameSeparateMarginals differentOriginalCoupling

noMarginalDecoderForJointIncidence :
  NF.FactorsThrough marginals jointIncidence → ⊥
noMarginalDecoderForJointIncidence =
  NF.witnessRulesOutEveryFlatFactorisation
    marginalsLoseOriginalCoupling

-- A spectral estimator, type classifier, chart, or other recharting
-- of the two marginals cannot reconstruct the erased joint incidence.
noRechartCanRestoreOriginalPairing :
  ∀ {Chart : Set} (chart : SeparateMarginals → Chart) →
  NF.FactorsThrough (λ c → chart (marginals c)) jointIncidence → ⊥
noRechartCanRestoreOriginalPairing chart =
  NF.rechartingCannotRecoverErasedPhenomenon
    chart marginalsLoseOriginalCoupling

-- Both displayed support masks have positive outer degree and both
-- half-roots are real original signed-coordinate F4 half-root vectors.
-- Therefore each of the four source pairs decodes to a genuine
-- Round56 regular cell via Pair.decode256.
