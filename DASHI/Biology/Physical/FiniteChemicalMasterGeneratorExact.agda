module DASHI.Biology.Physical.FiniteChemicalMasterGeneratorExact where

------------------------------------------------------------------------
-- SOURCE-FACING MOTIVATION
-- Daniel T. Gillespie, "Exact stochastic simulation of coupled chemical
-- reactions", The Journal of Physical Chemistry 81 (1977), 2340--2361.
-- DOI: 10.1021/j100540a008.
--
-- Continuous-time finite-state generator skeleton for the chemical-master-
-- equation lane.  Rates are exact rationals.  The generator is written in the
-- jump form sum_y r(x,y)(f(y)-f(x)), so the committor equation Lq=0 is literal.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; ½; _+_; _-_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

import DASHI.Biology.Physical.FiniteStochasticReactionCommittorExact as Embedded

ChemicalState : Set
ChemicalState = Embedded.ChemicalState

open Embedded using (extinct; drivenChemistry; replicator; protoLife)

jumpRate : ChemicalState → ChemicalState → ℚ
jumpRate extinct y = 0ℚ
jumpRate drivenChemistry extinct = 1ℚ
jumpRate drivenChemistry drivenChemistry = 0ℚ
jumpRate drivenChemistry replicator = 1ℚ
jumpRate drivenChemistry protoLife = 0ℚ
jumpRate replicator extinct = 1ℚ
jumpRate replicator drivenChemistry = 0ℚ
jumpRate replicator replicator = 0ℚ
jumpRate replicator protoLife = 1ℚ
jumpRate protoLife y = 0ℚ

generator : (ChemicalState → ℚ) → ChemicalState → ℚ
generator f x =
  jumpRate x extinct * (f extinct - f x)
  + jumpRate x drivenChemistry * (f drivenChemistry - f x)
  + jumpRate x replicator * (f replicator - f x)
  + jumpRate x protoLife * (f protoLife - f x)

committor : ChemicalState → ℚ
committor = Embedded.committor

committorGeneratorHarmonic : (x : ChemicalState) → generator committor x ≡ 0ℚ
committorGeneratorHarmonic extinct = solve-∀
committorGeneratorHarmonic drivenChemistry = solve-∀
committorGeneratorHarmonic replicator = solve-∀
committorGeneratorHarmonic protoLife = solve-∀

------------------------------------------------------------------------
-- Chemical-master equation on the same finite state carrier.  This is the
-- Kolmogorov forward operator pQ, expressed componentwise.
------------------------------------------------------------------------

record StateMass : Set where
  constructor stateMass
  field
    pExtinct pDriven pReplicator pProto : ℚ

open StateMass public

incoming : StateMass → ChemicalState → ℚ
incoming p y =
  pExtinct p * jumpRate extinct y
  + pDriven p * jumpRate drivenChemistry y
  + pReplicator p * jumpRate replicator y
  + pProto p * jumpRate protoLife y

escapeRate : ChemicalState → ℚ
escapeRate x =
  jumpRate x extinct + jumpRate x drivenChemistry
  + jumpRate x replicator + jumpRate x protoLife

massAt : StateMass → ChemicalState → ℚ
massAt p extinct = pExtinct p
massAt p drivenChemistry = pDriven p
massAt p replicator = pReplicator p
massAt p protoLife = pProto p

masterDerivativeAt : StateMass → ChemicalState → ℚ
masterDerivativeAt p x = incoming p x - massAt p x * escapeRate x

totalDerivative : StateMass → ℚ
totalDerivative p =
  masterDerivativeAt p extinct
  + masterDerivativeAt p drivenChemistry
  + masterDerivativeAt p replicator
  + masterDerivativeAt p protoLife

chemicalMasterConservesProbabilityInfinitesimally :
  (p : StateMass) → totalDerivative p ≡ 0ℚ
chemicalMasterConservesProbabilityInfinitesimally
  (stateMass a b c d) = solve-∀

------------------------------------------------------------------------
-- Generic stoichiometric CRN signature: counts, jump vectors and propensities
-- are explicit owners rather than being conflated with the four-state example.
------------------------------------------------------------------------

record StochasticReactionNetwork : Set₁ where
  field
    Species Reaction Population : Set
    populationAt : Population → Species → Nat
    jumpPopulation : Reaction → Population → Population
    propensity : Reaction → Population → ℚ

open StochasticReactionNetwork public

------------------------------------------------------------------------
-- Certified truncation interval.  This is the interface required before a
-- countably infinite network can be used: lower/upper finite-state committor
-- bounds must nest.  It does not assert convergence without a supplied proof.
------------------------------------------------------------------------

record TruncationCommittorBounds : Set₁ where
  field
    lower upper : Nat → ℚ
    lowerBound : (n : Nat) → lower n ≤ upper n
    lowerMonotone : (n : Nat) → lower n ≤ lower (suc n)
    upperAntitone : (n : Nat) → upper (suc n) ≤ upper n

open TruncationCommittorBounds public

record CertifiedTruncationConvergence (B : TruncationCommittorBounds) : Set₁ where
  field
    limit : ℚ
    lowerBelowLimit : (n : Nat) → lower B n ≤ limit
    limitBelowUpper : (n : Nat) → limit ≤ upper B n

------------------------------------------------------------------------
-- Local-detailed-balance / entropy-production slot.  The logarithmic
-- rate-ratio/chemical-potential law is deliberately a supplied physical law;
-- the finite generator does not manufacture it from rates alone.
------------------------------------------------------------------------

record LocalDetailedBalanceLaw : Set₁ where
  field
    Edge : Set
    forwardRate reverseRate affinity : Edge → ℚ
    entropyProductionContribution : Edge → ℚ
    entropyProductionDefinition : (e : Edge) →
      entropyProductionContribution e ≡
      (forwardRate e - reverseRate e) * affinity e

record ChemicalMasterAuthorityBoundary : Set where
  field
    finiteGeneratorProvesRareEventErrorBounds : Bool
    finiteGeneratorProvesRareEventErrorBoundsIsFalse :
      finiteGeneratorProvesRareEventErrorBounds ≡ false
    truncationInterfaceProvesConvergenceWithoutCertificate : Bool
    truncationInterfaceProvesConvergenceWithoutCertificateIsFalse :
      truncationInterfaceProvesConvergenceWithoutCertificate ≡ false

canonicalChemicalMasterAuthorityBoundary : ChemicalMasterAuthorityBoundary
canonicalChemicalMasterAuthorityBoundary = record
  { finiteGeneratorProvesRareEventErrorBounds = false
  ; finiteGeneratorProvesRareEventErrorBoundsIsFalse = refl
  ; truncationInterfaceProvesConvergenceWithoutCertificate = false
  ; truncationInterfaceProvesConvergenceWithoutCertificateIsFalse = refl
  }
