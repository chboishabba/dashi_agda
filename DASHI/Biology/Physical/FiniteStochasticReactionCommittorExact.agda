module DASHI.Biology.Physical.FiniteStochasticReactionCommittorExact where

------------------------------------------------------------------------
-- SOURCE-FACING MOTIVATION
-- Daniel T. Gillespie, "Exact stochastic simulation of coupled chemical
-- reactions", The Journal of Physical Chemistry 81 (1977), 2340--2361.
-- DOI: 10.1021/j100540a008.
--
-- Jeremy L. England, "Statistical physics of self-replication",
-- Journal of Chemical Physics 139 (2013), 121923.
-- DOI: 10.1063/1.4818538.
--
-- DASHI CONTRIBUTION
-- A finite exact Markov-jump regression separating (i) thermodynamic labels,
-- (ii) kinetic accessibility, and (iii) probability of hitting a proto-life
-- target before extinction.  The committor satisfies the discrete backward
-- harmonic equation exactly.  This is the finite theorem surface underneath
-- the future countable-state / Gillespie / rare-event lane; it is not a claim
-- about abiogenesis probability in nature.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; ½; _+_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

------------------------------------------------------------------------
-- Four coarse chemical macrostates.
------------------------------------------------------------------------

data ChemicalState : Set where
  extinct drivenChemistry replicator protoLife : ChemicalState

quarter : ℚ
quarter = ½ * ½

------------------------------------------------------------------------
-- Exact transition-mass kernel.  extinct and protoLife are absorbing.
-- drivenChemistry has equal mass to extinction and replicator formation;
-- replicator has equal mass to extinction and proto-life entry.
------------------------------------------------------------------------

transitionMass : ChemicalState → ChemicalState → ℚ
transitionMass extinct extinct = 1ℚ
transitionMass extinct drivenChemistry = 0ℚ
transitionMass extinct replicator = 0ℚ
transitionMass extinct protoLife = 0ℚ
transitionMass drivenChemistry extinct = ½
transitionMass drivenChemistry drivenChemistry = 0ℚ
transitionMass drivenChemistry replicator = ½
transitionMass drivenChemistry protoLife = 0ℚ
transitionMass replicator extinct = ½
transitionMass replicator drivenChemistry = 0ℚ
transitionMass replicator replicator = 0ℚ
transitionMass replicator protoLife = ½
transitionMass protoLife extinct = 0ℚ
transitionMass protoLife drivenChemistry = 0ℚ
transitionMass protoLife replicator = 0ℚ
transitionMass protoLife protoLife = 1ℚ

totalOutgoing : ChemicalState → ℚ
totalOutgoing x =
  transitionMass x extinct
  + transitionMass x drivenChemistry
  + transitionMass x replicator
  + transitionMass x protoLife

kernelNormalized : (x : ChemicalState) → totalOutgoing x ≡ 1ℚ
kernelNormalized extinct = solve-∀
kernelNormalized drivenChemistry = solve-∀
kernelNormalized replicator = solve-∀
kernelNormalized protoLife = solve-∀

expectation : (ChemicalState → ℚ) → ChemicalState → ℚ
expectation f x =
  transitionMass x extinct * f extinct
  + transitionMass x drivenChemistry * f drivenChemistry
  + transitionMass x replicator * f replicator
  + transitionMass x protoLife * f protoLife

------------------------------------------------------------------------
-- q(x) = P_x[hit protoLife before extinct] for this finite absorbing chain.
------------------------------------------------------------------------

committor : ChemicalState → ℚ
committor extinct = 0ℚ
committor drivenChemistry = quarter
committor replicator = ½
committor protoLife = 1ℚ

committorExtinctionBoundary : committor extinct ≡ 0ℚ
committorExtinctionBoundary = refl

committorProtoLifeBoundary : committor protoLife ≡ 1ℚ
committorProtoLifeBoundary = refl

committorBackwardHarmonicDriven :
  expectation committor drivenChemistry ≡ committor drivenChemistry
committorBackwardHarmonicDriven = solve-∀

committorBackwardHarmonicReplicator :
  expectation committor replicator ≡ committor replicator
committorBackwardHarmonicReplicator = solve-∀

committorBackwardHarmonic : (x : ChemicalState) →
  expectation committor x ≡ committor x
committorBackwardHarmonic extinct = solve-∀
committorBackwardHarmonic drivenChemistry = committorBackwardHarmonicDriven
committorBackwardHarmonic replicator = committorBackwardHarmonicReplicator
committorBackwardHarmonic protoLife = solve-∀

emergenceBeforeExtinctionFromDrivenChemistry :
  committor drivenChemistry ≡ quarter
emergenceBeforeExtinctionFromDrivenChemistry = refl

emergenceBeforeExtinctionFromReplicator :
  committor replicator ≡ ½
emergenceBeforeExtinctionFromReplicator = refl

------------------------------------------------------------------------
-- Thermodynamic score is deliberately not the committor.
-- Equal coarse energetic labelling can hide different future hitting laws.
------------------------------------------------------------------------

thermodynamicBand : ChemicalState → Nat
thermodynamicBand extinct = 0
thermodynamicBand drivenChemistry = 1
thermodynamicBand replicator = 1
thermodynamicBand protoLife = 2

sameThermodynamicBandDifferentCommittor :
  thermodynamicBand drivenChemistry ≡ thermodynamicBand replicator
  × committor drivenChemistry ≢ committor replicator
sameThermodynamicBandDifferentCommittor = refl , λ ()

kineticallyAccessibleProtoLife : ChemicalState → Bool
kineticallyAccessibleProtoLife extinct = false
kineticallyAccessibleProtoLife drivenChemistry = true
kineticallyAccessibleProtoLife replicator = true
kineticallyAccessibleProtoLife protoLife = true

accessibilityDoesNotDetermineProbability :
  kineticallyAccessibleProtoLife drivenChemistry
  ≡ kineticallyAccessibleProtoLife replicator
  × committor drivenChemistry ≢ committor replicator
accessibilityDoesNotDetermineProbability = refl , λ ()

------------------------------------------------------------------------
-- PNF bridge: a committor is a consumer-specific future statistic for the
-- binary question "proto-life before extinction?".  Equality of this scalar
-- is not asserted to preserve any richer chemical future law.
------------------------------------------------------------------------

record CommittorConsumerBoundary : Set where
  field
    committorIsCompleteChemicalState : Bool
    committorIsCompleteChemicalStateIsFalse :
      committorIsCompleteChemicalState ≡ false
    finiteChainProvesNaturalAbiogenesisProbability : Bool
    finiteChainProvesNaturalAbiogenesisProbabilityIsFalse :
      finiteChainProvesNaturalAbiogenesisProbability ≡ false

canonicalCommittorConsumerBoundary : CommittorConsumerBoundary
canonicalCommittorConsumerBoundary = record
  { committorIsCompleteChemicalState = false
  ; committorIsCompleteChemicalStateIsFalse = refl
  ; finiteChainProvesNaturalAbiogenesisProbability = false
  ; finiteChainProvesNaturalAbiogenesisProbabilityIsFalse = refl
  }
