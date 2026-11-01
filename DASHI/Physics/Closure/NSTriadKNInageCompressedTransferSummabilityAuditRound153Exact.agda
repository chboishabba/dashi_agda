module DASHI.Physics.Closure.NSTriadKNInageCompressedTransferSummabilityAuditRound153Exact where

------------------------------------------------------------------------
-- ROUND153 / SOURCE-EXACT AUDIT OF THE INAGE 2026 COMPRESSED-TRANSFER STEP
--
-- Source:
--   Shin-ichi Inage,
--   "Structural Reduction Framework and Residence-Time Compression of
--   Coherent Same-Scale Triadic Interactions in the 3D Navier-Stokes
--   Equations", Mathematics 14 (2026), 1410.
--   DOI: 10.3390/math14091410.
--
-- The paper's Theorem 6 / equations (257)--(262) use
--
--   |T_j^core| <= C Theta_j^(3/2) 2^(-j/2),
--   Theta_j^2 ~ E_j,
--   sum_j 2^(2 s j) E_j < infinity,
--
-- and state that the extra 2^(-j/2) makes
--
--   sum_j 2^(2 s j) E_j^(3/4) 2^(-j/2)
--
-- summable.
--
-- That implication is NOT valid from the displayed H^s shell hierarchy alone.
-- This file gives an exact rational counterexample on the shell subsequence
-- j=4n at the perfectly admissible value s=3 (>5/2):
--
--   E_(4n) = 2^(-28 n).
--
-- Then the H^3 weighted energy term is
--
--   2^(6*4n) E_(4n) = 2^(-4n) = (1/16)^n,
--
-- hence its prefix is uniformly bounded.  But the displayed compressed-
-- transfer summand is
--
--   2^(6*4n) E_(4n)^(3/4) 2^(-(4n)/2)
--     = 2^n,
--
-- which does not even decay.
--
-- Therefore Inage's residence-time theorem may still be an interesting
-- family-level dynamical statement, but equations (259)--(262) do not provide
-- a valid source theorem for DASHI package A without an additional shell
-- decay/sequence hypothesis.  We fail closed and do not import the claimed
-- Sobolev summability/absorbability.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo

oneSixteenth two : ℚ
oneSixteenth = Int.+ 1 / 16
two = Int.+ 2 / 1

-- Exact shell-subsequence terms after all fractional powers have been evaluated
-- on E_(4n)=2^(-28n).
hThreeWeightedEnergyTerm : Nat → ℚ
hThreeWeightedEnergyTerm n = Geo.pow oneSixteenth n

compressedTransferTerm : Nat → ℚ
compressedTransferTerm n = Geo.pow two n

hThreeWeightedEnergyPrefix : Nat → ℚ
hThreeWeightedEnergyPrefix = Geo.partialSum oneSixteenth

sixteenFifteenths : ℚ
sixteenFifteenths = Int.+ 16 / 15

oneSixteenthNonnegative : 0ℚ ≤ oneSixteenth
oneSixteenthNonnegative = toWitness {a? = 0ℚ ≤? oneSixteenth} _

oneMinusOneSixteenthPositive : 0ℚ < 1ℚ - oneSixteenth
oneMinusOneSixteenthPositive = toWitness {a? = 0ℚ <? 1ℚ - oneSixteenth} _

oneSixteenthBoundIdentity :
  (1ℚ - oneSixteenth) * sixteenFifteenths ≡ 1ℚ
oneSixteenthBoundIdentity = refl

hThreeEnergyPrefixUniformlyBounded :
  (cutoff : Nat) →
  hThreeWeightedEnergyPrefix cutoff ≤ sixteenFifteenths
hThreeEnergyPrefixUniformlyBounded cutoff =
  Geo.geometricPartialSumBound
    oneSixteenth sixteenFifteenths cutoff
    oneSixteenthNonnegative
    oneMinusOneSixteenthPositive
    oneSixteenthBoundIdentity

compressedTransferStartsAtOne : compressedTransferTerm zero ≡ 1ℚ
compressedTransferStartsAtOne = refl

compressedTransferDoubles :
  (n : Nat) →
  compressedTransferTerm (suc n) ≡ two * compressedTransferTerm n
compressedTransferDoubles n = refl

oneBelowCompressedTransferTerm :
  (n : Nat) → 1ℚ ≤ compressedTransferTerm n
oneBelowCompressedTransferTerm zero = ℚₚ.≤-refl
oneBelowCompressedTransferTerm (suc n) =
  let
    previous = oneBelowCompressedTransferTerm n
    twoPositiveEnough : 1ℚ ≤ two
    twoPositiveEnough = toWitness {a? = 1ℚ ≤? two} _
    termNN : 0ℚ ≤ compressedTransferTerm n
    termNN = Geo.powNonnegative two n
      (toWitness {a? = 0ℚ ≤? two} _)
    scalePrevious :
      compressedTransferTerm n ≤ two * compressedTransferTerm n
    scalePrevious =
      let instance termNonnegative = nonNegative termNN
      in ℚₚ.*-monoʳ-≤-nonNeg
          (compressedTransferTerm n)
          twoPositiveEnough
  in
  ℚₚ.≤-trans previous scalePrevious

------------------------------------------------------------------------
-- Receipt boundary.
------------------------------------------------------------------------

round153InageResidenceCompressionStructurallyRelevant : Bool
round153InageResidenceCompressionStructurallyRelevant = true

round153DisplayedHSSummabilityImpliesCompressedTransferSummability : Bool
round153DisplayedHSSummabilityImpliesCompressedTransferSummability = false

round153InageTheoremSixImportedAsPackageAAuthority : Bool
round153InageTheoremSixImportedAsPackageAAuthority = false

round153AdditionalShellDecayHypothesisWouldBeRequired : Bool
round153AdditionalShellDecayHypothesisWouldBeRequired = true

round153PackageAClosed : Bool
round153PackageAClosed = false

round153DisplayedHSSummabilityImpliesCompressedTransferSummabilityIsFalse :
  round153DisplayedHSSummabilityImpliesCompressedTransferSummability ≡ false
round153DisplayedHSSummabilityImpliesCompressedTransferSummabilityIsFalse = refl

round153PackageAClosedIsFalse : round153PackageAClosed ≡ false
round153PackageAClosedIsFalse = refl
