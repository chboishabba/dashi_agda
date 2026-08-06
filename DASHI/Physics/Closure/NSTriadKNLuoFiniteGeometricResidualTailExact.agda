module DASHI.Physics.Closure.NSTriadKNLuoFiniteGeometricResidualTailExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Far-field, commutator and cutoff tails frequently reduce to a geometric
-- shell separation once the physical producer has supplied a ratio rho.  This
-- module proves the exact finite identity
--
--   (1-rho) sum_{j=0}^n rho^j = 1-rho^(n+1)
--
-- recursively over the rational carrier.  It also transports a common
-- residual coefficient through the sum.  No convergence or small-ratio claim
-- is hidden: the analytic route must still prove 0 <= rho < 1 uniformly and
-- identify the actual far-field/low/tail terms with this geometric envelope.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans)

rationalPower : ℚ → Nat → ℚ
rationalPower ratio zero = 1ℚ
rationalPower ratio (suc exponent) =
  ratio * rationalPower ratio exponent

finiteGeometricSum : ℚ → Nat → ℚ
finiteGeometricSum ratio zero = 1ℚ
finiteGeometricSum ratio (suc exponent) =
  1ℚ + ratio * finiteGeometricSum ratio exponent

finiteGeometricIdentity :
  ∀ ratio exponent →
  (1ℚ - ratio) * finiteGeometricSum ratio exponent
  ≡ 1ℚ - rationalPower ratio (suc exponent)
finiteGeometricIdentity ratio zero = solve (ratio ∷ [])
finiteGeometricIdentity ratio (suc exponent) =
  let
    previousSum = finiteGeometricSum ratio exponent
    previousPower = rationalPower ratio exponent

    expanded :
      (1ℚ - ratio) * (1ℚ + ratio * previousSum)
      ≡
      (1ℚ - ratio)
      + ratio * ((1ℚ - ratio) * previousSum)
    expanded = solve (ratio ∷ previousSum ∷ [])

    inductiveSubstitution :
      (1ℚ - ratio)
        + ratio * ((1ℚ - ratio) * previousSum)
      ≡
      (1ℚ - ratio)
        + ratio * (1ℚ - ratio * previousPower)
    inductiveSubstitution =
      cong
        (λ value → (1ℚ - ratio) + ratio * value)
        (finiteGeometricIdentity ratio exponent)

    closed :
      (1ℚ - ratio)
        + ratio * (1ℚ - ratio * previousPower)
      ≡ 1ℚ - ratio * (ratio * previousPower)
    closed = solve (ratio ∷ previousPower ∷ [])
  in
  trans expanded (trans inductiveSubstitution closed)

scaledGeometricTail : ℚ → ℚ → Nat → ℚ
scaledGeometricTail coefficient ratio exponent =
  coefficient * finiteGeometricSum ratio exponent

scaledFiniteGeometricIdentity :
  ∀ coefficient ratio exponent →
  (1ℚ - ratio) * scaledGeometricTail coefficient ratio exponent
  ≡ coefficient * (1ℚ - rationalPower ratio (suc exponent))
scaledFiniteGeometricIdentity coefficient ratio exponent =
  let
    reassociated :
      (1ℚ - ratio)
        * (coefficient * finiteGeometricSum ratio exponent)
      ≡
      coefficient
        * ((1ℚ - ratio) * finiteGeometricSum ratio exponent)
    reassociated =
      solve
        ( coefficient
        ∷ ratio
        ∷ finiteGeometricSum ratio exponent
        ∷ [])

    substituted =
      cong
        (λ value → coefficient * value)
        (finiteGeometricIdentity ratio exponent)
  in
  trans reassociated substituted

record GeometricResidualAuthorityBoundary : Set where
  constructor geometricResidualAuthorityBoundary
  field
    exactFiniteGeometricIdentityProved : Set
    coefficientTransportProved : Set
    physicalFarFieldRatioProduced : Set
    physicalCommutatorRatioProduced : Set
    physicalGalerkinTailRatioProduced : Set
    uniformRatioStrictlyBelowOneProved : Set

canonicalGeometricResidualAuthorityBoundary :
  GeometricResidualAuthorityBoundary
canonicalGeometricResidualAuthorityBoundary =
  geometricResidualAuthorityBoundary ⊤ ⊤ ⊥ ⊥ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
