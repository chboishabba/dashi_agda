module DASHI.Physics.YangMills.BalabanSelectedKKTWeightedToOrdinaryRowBoundExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- The selected KKT locality theorem already controls the weighted row sum of
-- the literal Gram pseudoinverse K+:
--
--     sum_y |K+(x,y)| w(y) <= rho w(x).
--
-- G2's Schur/Penrose compiler asks for the ordinary absolute row mass instead.
-- On any finite selected region with
--
--     1 <= w(y) <= W,
--
-- no new pseudoinverse estimate is required:
--
--     sum_y |K+(x,y)|
--       <= sum_y |K+(x,y)| w(y)
--       <= rho w(x)
--       <= rho W.
--
-- This file proves that adapter on the exact finite rational carriers already
-- used by both modules and returns precisely `pseudoinverseRowBound`.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; ∣_∣; NonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedRowSumContractionExact as Row
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanKKTPseudoinverseSchurEnergyBoundExact as Energy
import DASHI.Physics.YangMills.BalabanSelectedKKTMultiplierLocalityExact as Locality

absoluteEntryBelowWeighted : ∀ value weight →
  1ℚ ≤ weight →
  ∣ value ∣ ≤ ∣ value ∣ * weight
absoluteEntryBelowWeighted value weight oneBelow =
  let
    instance
      absNN : NonNegative ∣ value ∣
      absNN = ℚP.∣-∣-nonNeg value

    scaled : ∣ value ∣ * 1ℚ ≤ ∣ value ∣ * weight
    scaled = ℚP.*-monoˡ-≤-nonNeg ∣ value ∣ oneBelow
  in
  subst
    (λ lower → lower ≤ ∣ value ∣ * weight)
    (ℚP.*-identityʳ ∣ value ∣)
    scaled

ordinaryRowBelowWeightedRow :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    (weight : Multiplier → ℚ) →
  (∀ column → 1ℚ ≤ weight column) →
  ∀ row →
  Schur.absoluteRowMass
    (Matrix.coordinates (Pseudo.multiplierCarrier pseudoData))
    (Pseudo.gramPseudoinverse pseudoData) row
  ≤ Row.weightedRowSum
      (Matrix.coordinates (Pseudo.multiplierCarrier pseudoData))
      (Pseudo.gramPseudoinverse pseudoData) weight row
ordinaryRowBelowWeightedRow pseudoData weight weightAboveOne row =
  let
    indices = Matrix.coordinates (Pseudo.multiplierCarrier pseudoData)
    kernel = Pseudo.gramPseudoinverse pseudoData

    finiteSumBound :
      Schur.absoluteRowMass indices kernel row
      ≤ Locality.Sums.sumRational indices
          (λ column → ∣ kernel row column ∣ * weight column)
    finiteSumBound =
      Schur.sumPointwiseBelow indices
        (λ column → ∣ kernel row column ∣)
        (λ column → ∣ kernel row column ∣ * weight column)
        (λ column →
          absoluteEntryBelowWeighted
            (kernel row column) (weight column) (weightAboveOne column))

    implementationsAgree :
      Row.weightedRowSum indices kernel weight row
      ≡ Locality.Sums.sumRational indices
          (λ column → ∣ kernel row column ∣ * weight column)
    implementationsAgree =
      Locality.sumImplementationsAgree indices
        (λ column → ∣ kernel row column ∣ * weight column)
  in
  subst
    (λ upper → Schur.absoluteRowMass indices kernel row ≤ upper)
    (sym implementationsAgree)
    finiteSumBound

selectedLocalityGivesOrdinaryPseudoinverseRowBound :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {source : Pseudo.MultiplierVector Multiplier}
    (locality : Locality.CanonicalMultiplierLocalityData pseudoData source)
    (weightEnvelope : ℚ) →
  (∀ row → 1ℚ ≤ Locality.weight locality row) →
  (∀ row → Locality.weight locality row ≤ weightEnvelope) →
  Energy.pseudoinverseRowBound pseudoData
    (Locality.greenWeightedRowMajorant locality * weightEnvelope)
selectedLocalityGivesOrdinaryPseudoinverseRowBound
    {pseudoData = pseudoData} locality weightEnvelope
    weightAboveOne weightBelowEnvelope row =
  let
    indices = Matrix.coordinates (Pseudo.multiplierCarrier pseudoData)
    kernel = Pseudo.gramPseudoinverse pseudoData
    rho = Locality.greenWeightedRowMajorant locality
    weight = Locality.weight locality

    ordinaryToWeighted :
      Schur.absoluteRowMass indices kernel row
      ≤ Row.weightedRowSum indices kernel weight row
    ordinaryToWeighted =
      ordinaryRowBelowWeightedRow pseudoData weight weightAboveOne row

    weightedToLocal :
      Row.weightedRowSum indices kernel weight row
      ≤ rho * weight row
    weightedToLocal = Locality.greenWeightedRowBound locality row

    localToEnvelope :
      rho * weight row ≤ rho * weightEnvelope
    localToEnvelope =
      Norm.scaleNonnegative rho
        (Locality.greenMajorantNonnegative locality)
        (weightBelowEnvelope row)
  in
  ℚP.≤-trans ordinaryToWeighted
    (ℚP.≤-trans weightedToLocal localToEnvelope)

selectedKKTWeightedToOrdinaryRowBoundLevel : ProofLevel
selectedKKTWeightedToOrdinaryRowBoundLevel = machineChecked

-- The remaining selected-region input is now only a finite weight envelope
-- 1 <= w <= W for whichever Combes--Thomas/locality weight is used.  Once that
-- is supplied, G2 receives the exact ordinary K+ row bound rho*W directly.
selectedKKTPhysicalWeightEnvelopeLevel : ProofLevel
selectedKKTPhysicalWeightEnvelopeLevel = conditional
