module DASHI.NumberTheory.Collatz.SyracuseLogDriftBoundaryExact where

------------------------------------------------------------------------
-- REAL-ANALYSIS BOUNDARY FOR SYRACUSE LOG DRIFT
--
-- Logarithms never live on residue classes.  This record names exactly the
-- real-analysis facts a downstream concentration theorem may consume.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

record SyracuseLogAnalysisSource : Set₁ where
  field
    Real : Set
    natReal : Nat → Real
    _+R_ _-R_ _*R_ _/R_ _≤R_ : Real → Real → Real
    logR : Real → Real
    zeroR oneR twoR threeR : Real

    logThreeHalvesIncrement :
      (x : Nat) → Set

    logOnePlusUpperBound :
      (u : Real) → Set

    negativeMeanDrift :
      Set

open SyracuseLogAnalysisSource public

record SyracuseLogBoundary : Set where
  constructor syracuseLogBoundary
  field
    logOnFiniteResidueAllowed : Nat
    exactIntegerOrbitRequired : Nat
    logOnePlusInequalityExplicit : Nat
    concentrationAutomaticFromEigenvalues : Nat

canonicalSyracuseLogBoundary : SyracuseLogBoundary
canonicalSyracuseLogBoundary = syracuseLogBoundary 0 1 1 0
