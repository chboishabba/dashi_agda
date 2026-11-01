module DASHI.Physics.Closure.NSTriadKNExactPairIncidenceGramAssembly where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNAdmissibleFourierShellData as Fourier
import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice
import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNExactRetainedPairIncidences as Incidence

------------------------------------------------------------------------
-- Coefficients on the actual three-edge incidence carrier.
--
-- triadAbsoluteCoefficient and triadNegativeCoefficient already include
-- the factor 1/3.  Thus every edge of a triad receives m_tau / 3, rather
-- than accidentally assigning the complete triad weight to all three edges.
------------------------------------------------------------------------

pairIncidenceAbsoluteCoefficient :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  {N : Nat} → {interaction : Fourier.PhysicalTriadInteractionLaw S C N} →
  Fourier.AdmissibleFourierShellData S C N interaction →
  Incidence.PairIncidence → Scalar.Scalar S
pairIncidenceAbsoluteCoefficient u r =
  Fourier.triadAbsoluteCoefficient u (Incidence.triad r)

pairIncidenceNegativeCoefficient :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  {N : Nat} → {interaction : Fourier.PhysicalTriadInteractionLaw S C N} →
  Fourier.AdmissibleFourierShellData S C N interaction →
  Incidence.PairIncidence → Scalar.Scalar S
pairIncidenceNegativeCoefficient u r =
  Fourier.triadNegativeCoefficient u (Incidence.triad r)

threeEdgeAbsoluteCoefficientsAgree :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  {N : Nat} → {interaction : Fourier.PhysicalTriadInteractionLaw S C N} →
  (u : Fourier.AdmissibleFourierShellData S C N interaction) →
  (τ : Lattice.LatticeTriad) →
  pairIncidenceAbsoluteCoefficient u (Incidence.mkPairIncidence τ Incidence.firstPair) ≡
  pairIncidenceAbsoluteCoefficient u (Incidence.mkPairIncidence τ Incidence.secondPair)
threeEdgeAbsoluteCoefficientsAgree u τ = refl

threeEdgeNegativeCoefficientsAgree :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  {N : Nat} → {interaction : Fourier.PhysicalTriadInteractionLaw S C N} →
  (u : Fourier.AdmissibleFourierShellData S C N interaction) →
  (τ : Lattice.LatticeTriad) →
  pairIncidenceNegativeCoefficient u (Incidence.mkPairIncidence τ Incidence.firstPair) ≡
  pairIncidenceNegativeCoefficient u (Incidence.mkPairIncidence τ Incidence.thirdPair)
threeEdgeNegativeCoefficientsAgree u τ = refl

pairIncidenceNegativeCoefficientNonnegative :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  {N : Nat} → {interaction : Fourier.PhysicalTriadInteractionLaw S C N} →
  (u : Fourier.AdmissibleFourierShellData S C N interaction) →
  (r : Incidence.PairIncidence) →
  Scalar.Nonnegative S (pairIncidenceNegativeCoefficient u r)
pairIncidenceNegativeCoefficientNonnegative u r =
  Fourier.negativeTriadCoefficientNonnegative u (Incidence.triad r)

pairIncidenceNegativeCoefficientLeAbsolute :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  {N : Nat} → {interaction : Fourier.PhysicalTriadInteractionLaw S C N} →
  (u : Fourier.AdmissibleFourierShellData S C N interaction) →
  (r : Incidence.PairIncidence) →
  Scalar._≤_ S
    (pairIncidenceNegativeCoefficient u r)
    (pairIncidenceAbsoluteCoefficient u r)
pairIncidenceNegativeCoefficientLeAbsolute u r =
  Fourier.negativeTriadCoefficientLeAbsolute u (Incidence.triad r)

-- This is an auxiliary Gram surrogate, not the signed Fourier convection
-- operator.  The remaining construction must instantiate b_r as
-- e_(source r) - e_(target r) in a concrete finite shell vector space and
-- establish that the fold of these rank-one edges is the PDE Gram form.
-- No such equality is asserted by the diagnostic count kernel.
record ExactPairIncidenceFoldEqualsAuxiliaryTriadGram (N : Nat) : Set₁ where
  field
    threeEdgeRankOneExpansion : Set
    orientationReversalPreservesRankOne : Set
    triadCoefficientSplitConservesWeight : Set
    pairIncidenceFoldEqualsTriadGramContribution : Set
    allPairIncidencesFoldEqualsAuxiliaryGramOperator : Set

exactPairIncidenceFoldEqualsAuxiliaryTriadGramClosed : Bool
exactPairIncidenceFoldEqualsAuxiliaryTriadGramClosed = false
