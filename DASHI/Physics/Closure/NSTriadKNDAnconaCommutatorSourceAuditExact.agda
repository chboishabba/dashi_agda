module DASHI.Physics.Closure.NSTriadKNDAnconaCommutatorSourceAuditExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Piero D'Ancona.
-- Title: "A Short Proof of Commutator Estimates".
-- Journal of Fourier Analysis and Applications 25 (2019), 1134--1146.
-- DOI: 10.1007/s00041-018-9612-8.
-- Correction DOI: 10.1007/s00041-019-09724-7.
-- arXiv:1109.5485.
--
-- PURPOSE
-- Record the exact applicability boundary of the source.  D'Ancona proves a
-- fractional Leibniz/commutator theorem based on products of first
-- differences for 0<s<2.  That result supports the paired-difference design
-- used in the DASHI centered commutator, but it is not literally the dyadic
-- transport estimate
--
--   [Delta_q , a . grad] g.
--
-- This audit prevents a fractional D^s theorem from being imported as a
-- completed Littlewood--Paley transport producer.  The source remains a valid
-- provenance anchor for the difference representation and Holder exponent
-- architecture.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

_≢_ : ∀ {A : Set} → A → A → Set
left ≢ right = left ≡ right → ⊥

data CommutatorTheoremShape : Set where
  fractionalLeibnizDifference : CommutatorTheoremShape
  dyadicTransportBlock : CommutatorTheoremShape
  rieszTransportEnergy : CommutatorTheoremShape

sourceTheoremShape : CommutatorTheoremShape
sourceTheoremShape = fractionalLeibnizDifference

sourceIsNotDyadicTransportBlock :
  sourceTheoremShape ≢ dyadicTransportBlock
sourceIsNotDyadicTransportBlock ()

sourceIsNotRieszTransportEnergy :
  sourceTheoremShape ≢ rieszTransportEnergy
sourceIsNotRieszTransportEnergy ()

data SourceContribution : Set where
  pairedFirstDifferenceRepresentation : SourceContribution
  holderExponentConstraint : SourceContribution
  completeSixThreeDyadicProducer : SourceContribution

sourceSuppliesDifferenceRepresentation : SourceContribution
sourceSuppliesDifferenceRepresentation = pairedFirstDifferenceRepresentation

sourceSuppliesHolderConstraint : SourceContribution
sourceSuppliesHolderConstraint = holderExponentConstraint

sourceDoesNotDirectlySupplySixThreeProducer :
  sourceSuppliesDifferenceRepresentation ≢ completeSixThreeDyadicProducer
sourceDoesNotDirectlySupplySixThreeProducer ()

------------------------------------------------------------------------
-- Exact algebraic kernel identity used in the source.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)

fractionalDifferenceProductIdentity :
  (uCenter uShift vCenter vShift : ℚ) →
  uShift * vShift - uCenter * vCenter
    - uCenter * (vShift - vCenter)
    - vCenter * (uShift - uCenter)
  ≡ (uShift - uCenter) * (vShift - vCenter)
fractionalDifferenceProductIdentity
  uCenter uShift vCenter vShift =
  solve (uCenter ∷ uShift ∷ vCenter ∷ vShift ∷ [])
