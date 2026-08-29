module DASHI.Physics.YangMills.YangMillsSameFamilyCumulantMarginToInteractingExact where

------------------------------------------------------------------------
-- ROUND87: FINITE SAME-FAMILY CUMULANT MARGIN -> CONTINUUM NONTRIVIALITY
--
-- MATHEMATICAL CONTEXT
--
-- A centred Gaussian field satisfies Wick factorization, hence its connected
-- fourth function vanishes.  The repository already has:
--
--   * exact rational fourth-cumulant / Wick algebra;
--   * a same-limit margin transport theorem
--
--       delta + epsilon <= kappa4_N
--       kappa4_N - epsilon <= kappa4_infinity
--                     => delta <= kappa4_infinity.
--
-- This file closes the remaining logical composition.  If delta>0 and the
-- continuum quantity is literally the fourth cumulant of one gauge-invariant
-- observable quadruple on the SAME Schwinger system, the continuum cumulant is
-- positive, Wick factorization is impossible, and the existing interaction
-- witness carrier is inhabited.
--
-- This is the exact 4->3 fusion criterion discussed in Round87 planning: if the
-- strengthened marked-source theorem itself supplies the buffered finite
-- cumulant and its same-family continuum approximation, nontriviality is no
-- longer an independent analytic theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary.Negation.Core using (¬_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.BalabanUnifiedContinuumEndpointMarginTransportExact as Endpoint
import DASHI.Physics.YangMills.YangMillsContinuumFourthCumulantNonGaussianExact as Cumulant

record SameFamilyBufferedCumulantWitness
    {Observable Point Scalar Separation : Set}
    (system : OS.ContinuumSchwingerSystem Observable Point Scalar) : Set₁ where
  field
    endpointMargins : Endpoint.SameScaleEndpointMargins Separation
    interactionMarginPositive :
      0ℚ < Endpoint.interactionMargin endpointMargins

    moments : Cumulant.FourPointMomentData
    continuumCumulantIsMoments :
      Endpoint.continuumFourthCumulant endpointMargins
      ≡ Cumulant.fourthCumulant moments

open SameFamilyBufferedCumulantWitness public

positiveRationalIsNonzero : ∀ value → 0ℚ < value → ¬ (value ≡ 0ℚ)
positiveRationalIsNonzero value positive valueZero =
  let
    zeroPositive : 0ℚ < 0ℚ
    zeroPositive = subst (λ selected → 0ℚ < selected) valueZero positive
  in
  ⊥-elim (ℚP.<-irrefl refl zeroPositive)

continuumCumulantPositive :
  ∀ {Observable Point Scalar Separation}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
    (dataSet : SameFamilyBufferedCumulantWitness {Separation = Separation} system) →
  0ℚ < Cumulant.fourthCumulant (moments dataSet)
continuumCumulantPositive dataSet =
  let
    endpointPositive :
      0ℚ < Endpoint.continuumFourthCumulant (endpointMargins dataSet)
    endpointPositive =
      ℚP.<-≤-trans
        (interactionMarginPositive dataSet)
        (Endpoint.sameLimitInteractionMargin (endpointMargins dataSet))
  in
  subst
    (λ selected → 0ℚ < selected)
    (continuumCumulantIsMoments dataSet)
    endpointPositive

bufferedContinuumCumulantRefutesWick :
  ∀ {Observable Point Scalar Separation}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
    (dataSet : SameFamilyBufferedCumulantWitness {Separation = Separation} system) →
  ¬ Cumulant.GaussianWickFour (moments dataSet)
bufferedContinuumCumulantRefutesWick dataSet wick =
  positiveRationalIsNonzero
    (Cumulant.fourthCumulant (moments dataSet))
    (continuumCumulantPositive dataSet)
    (Cumulant.wickFourImpliesFourthCumulantZero (moments dataSet) wick)

sameFamilyBufferedCumulantGivesInteractingWitness :
  ∀ {Observable Point Scalar Separation}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar} →
  SameFamilyBufferedCumulantWitness {Separation = Separation} system →
  OS.InteractingContinuumWitness Observable Point Scalar system
sameFamilyBufferedCumulantGivesInteractingWitness dataSet = record
  { Witness = Cumulant.GaussianWickFour (moments dataSet)
  ; witness = bufferedContinuumCumulantRefutesWick dataSet
  }

sameFamilyBufferedCumulantCompilerLevel : ProofLevel
sameFamilyBufferedCumulantCompilerLevel = machineChecked

-- Physical fusion seam only: one marked-source theorem would need to provide
-- `SameFamilyBufferedCumulantWitness` for an actual gauge-invariant local
-- observable quadruple of the same continuum Schwinger family.
physicalMarkedSourceBufferedCumulantLevel : ProofLevel
physicalMarkedSourceBufferedCumulantLevel = conditional
