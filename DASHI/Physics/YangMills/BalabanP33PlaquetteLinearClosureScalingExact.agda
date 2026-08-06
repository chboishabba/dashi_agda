module DASHI.Physics.YangMills.BalabanP33PlaquetteLinearClosureScalingExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks".
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Balaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories".
-- DOI: 10.1007/BF01229381.
--
-- Tadeusz Balaban,
-- "Propagators for Lattice Gauge Theories in a Background Field".
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Identify an exact algebraic reason the radius-only W-local implication fails.
-- A bondwise estimate controls each link perturbation at order rho, but a
-- plaquette product generally has the first-order term
--
--                   a + b - c - d.
--
-- Unless selected-background structure controls or cancels this correlated
-- plaquette term, the Wilson defect may remain O(rho), whereas the desired
-- sharp local budget needs the grouped remainder to begin at higher order.
--
-- The complete scalar plaquette expansion and its rho-scaled form are proved
-- by exact rational normalization.  This is a commuting regression for the
-- first-order obstruction; the physical SU(2) theorem must prove the analogous
-- correlated statement using the actual ordered link jets.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

plaquetteProduct : ℚ → ℚ → ℚ → ℚ → ℚ
plaquetteProduct a b c d =
  (1ℚ + a) * (1ℚ + b) * (1ℚ - c) * (1ℚ - d)

linearPlaquettePart : ℚ → ℚ → ℚ → ℚ → ℚ
linearPlaquettePart a b c d = a + b - c - d

quadraticPlaquettePart : ℚ → ℚ → ℚ → ℚ → ℚ
quadraticPlaquettePart a b c d =
  a * b - a * c - a * d - b * c - b * d + c * d

cubicPlaquettePart : ℚ → ℚ → ℚ → ℚ → ℚ
cubicPlaquettePart a b c d =
  a * c * d + b * c * d - a * b * c - a * b * d

quarticPlaquettePart : ℚ → ℚ → ℚ → ℚ → ℚ
quarticPlaquettePart a b c d = a * b * c * d

plaquetteExpansionExact :
  ∀ a b c d →
  plaquetteProduct a b c d - 1ℚ
  ≡ linearPlaquettePart a b c d
    + quadraticPlaquettePart a b c d
    + cubicPlaquettePart a b c d
    + quarticPlaquettePart a b c d
plaquetteExpansionExact a b c d = solve (a ∷ b ∷ c ∷ d ∷ [])

scaledPlaquetteExpansionExact :
  ∀ rho a b c d →
  plaquetteProduct (rho * a) (rho * b) (rho * c) (rho * d) - 1ℚ
  ≡ rho * linearPlaquettePart a b c d
    + (rho * rho) * quadraticPlaquettePart a b c d
    + (rho * rho * rho) * cubicPlaquettePart a b c d
    + (rho * rho * rho * rho) * quarticPlaquettePart a b c d
scaledPlaquetteExpansionExact rho a b c d =
  solve (rho ∷ a ∷ b ∷ c ∷ d ∷ [])

linearClosureRemovesFirstOrder :
  ∀ rho a b c d →
  linearPlaquettePart a b c d ≡ 0ℚ →
  plaquetteProduct (rho * a) (rho * b) (rho * c) (rho * d) - 1ℚ
  ≡ (rho * rho) * quadraticPlaquettePart a b c d
    + (rho * rho * rho) * cubicPlaquettePart a b c d
    + (rho * rho * rho * rho) * quarticPlaquettePart a b c d
linearClosureRemovesFirstOrder rho a b c d closure
  rewrite closure =
  solve (rho ∷ a ∷ b ∷ c ∷ d ∷ [])

unbalancedSingleLinkDefectExact :
  ∀ rho → plaquetteProduct rho 0ℚ 0ℚ 0ℚ - 1ℚ ≡ rho
unbalancedSingleLinkDefectExact rho = solve (rho ∷ [])

balancedOppositeLinkDefectExact :
  ∀ rho → plaquetteProduct rho 0ℚ 0ℚ rho - 1ℚ ≡ - (rho * rho)
balancedOppositeLinkDefectExact rho = solve (rho ∷ [])

balancedOppositeLinkLinearClosure :
  ∀ rho → linearPlaquettePart rho 0ℚ 0ℚ rho ≡ 0ℚ
balancedOppositeLinkLinearClosure rho = solve (rho ∷ [])

record PhysicalLinearClosureTarget : Set₁ where
  field
    Background Plaquette : Set
    selectedBackground : Background
    physicalLinearPlaquetteClosure : Plaquette → Set
    orderedQuaternionRemainderStartsQuadratically :
      (plaquette : Plaquette) →
      physicalLinearPlaquetteClosure plaquette → Set

-- The target record names the physical replacement for the scalar regression.
-- It is intentionally not inhabited here: the variational equation, background
-- gauge and actual SU(2) plaquette curvature must supply it.
