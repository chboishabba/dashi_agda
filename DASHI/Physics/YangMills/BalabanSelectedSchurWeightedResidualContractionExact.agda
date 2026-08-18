module DASHI.Physics.YangMills.BalabanSelectedSchurWeightedResidualContractionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrodinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Tadeusz Balaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Push the strict Schur residual contraction through the repository's literal
-- rational side-four Combes--Thomas growth weight.  The already-proved
-- constants are
--
--   q = 126633 / 1048576,
--   1 <= w <= W = 6561 / 4096.
--
-- Therefore the coarse bounded-weight promotion gives
--
--   sum_y |R(x,y)| w(y)
--     <= (W q) w(x),
--
-- with the exact factor
--
--   W q = 830839113 / 4294967296 < 1/5.
--
-- This is a genuine weighted contraction for the SAME residual
-- R=G_0 Q_A produced by the exact average-sector Schur elimination.  It does
-- not yet identify the complete combined KKT pseudoinverse kernel; the next
-- step is the finite weighted reopening / Schur inverse reconstruction.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; _<_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary.Decidable.Core using (toWitness)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedRowSumContractionExact as Row
import DASHI.Physics.YangMills.BalabanSelectedBackgroundRationalCombesThomasWeightExact as Weight
import DASHI.Physics.YangMills.BalabanSelectedBackgroundRationalCombesThomasWeightEnvelopeExact as Envelope
import DASHI.Physics.YangMills.BalabanFiniteWeightEnvelopeRowPromotionExact as Promote
import DASHI.Physics.YangMills.BalabanSelectedSchurCrossAbsoluteMassExact as Cross
import DASHI.Physics.YangMills.BalabanSelectedSchurGaugeGreenContractionExact as Schur

weightedSchurResidualContraction : ℚ
weightedSchurResidualContraction = + 830839113 / 4294967296

weightedSchurResidualContractionExact :
  Weight.siteGrowthEnvelope * Schur.schurGreenContractionBound
  ≡ weightedSchurResidualContraction
weightedSchurResidualContractionExact = ℚRing.solve []

weightedSchurResidualContractionBelowOneFifth :
  weightedSchurResidualContraction < + 1 / 5
weightedSchurResidualContractionBelowOneFifth = toWitness _

selectedSchurResidualWeightedRowBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ root left →
  Row.weightedRowSum Cross.gaugeRows
    (Schur.flatGreenTimesSchurPerturbation background)
    (Weight.gaugeInverseWeight root) left
  ≤ weightedSchurResidualContraction
      * Weight.gaugeInverseWeight root left
selectedSchurResidualWeightedRowBound background radius root left =
  let
    raw = Promote.boundedWeightPromotesUniformRow
      Cross.gaugeRows
      (Schur.flatGreenTimesSchurPerturbation background)
      (Weight.gaugeInverseWeight root)
      Weight.siteGrowthEnvelope
      Schur.schurGreenContractionBound
      (ℚP.nonNegative⁻¹ Weight.siteGrowthEnvelope)
      (ℚP.nonNegative⁻¹ Schur.schurGreenContractionBound)
      (Envelope.gaugeInverseWeightAboveOne root)
      (Weight.gaugeInverseWeightBelowEnvelope root)
      (Schur.selectedFlatGreenSchurPerturbationRowMassBound background radius)
      left
  in
  subst
    (λ factor →
      Row.weightedRowSum Cross.gaugeRows
        (Schur.flatGreenTimesSchurPerturbation background)
        (Weight.gaugeInverseWeight root) left
      ≤ factor * Weight.gaugeInverseWeight root left)
    weightedSchurResidualContractionExact raw

selectedSchurWeightedResidualContractionLevel : ProofLevel
selectedSchurWeightedResidualContractionLevel = machineChecked

selectedSchurWeightedResidualOneFifthLevel : ProofLevel
selectedSchurWeightedResidualOneFifthLevel = machineChecked
