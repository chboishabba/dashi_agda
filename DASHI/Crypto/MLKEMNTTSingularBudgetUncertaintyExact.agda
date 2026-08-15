module DASHI.Crypto.MLKEMNTTSingularBudgetUncertaintyExact where

------------------------------------------------------------------------
-- ML-KEM NTT: SINGULAR-RESIDUE BUDGET UNCERTAINTY
--
-- Primary cryptographic source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard",
-- FIPS 203, 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- Finite-field uncertainty source:
-- Martino Borello; Patrick Sole,
-- "The uncertainty principle over finite fields",
-- Discrete Mathematics 345 (2022), 112670.
-- DOI: 10.1016/j.disc.2021.112670.
--
-- PURPOSE
--
-- Isolate the exact arithmetic seam in the full-module dream theorem.
-- For a nonzero perturbation delta, write
--
--   s     = coefficient-position support,
--   h     = 128-residue harmonic/NTT support,
--   o     = surviving public-output residue support,
--   sigma = number of singular local public matrices.
--
-- The finite-field Fourier theorem supplies
--
--   128 <= s * h.
--
-- Local linear algebra supplies
--
--   h <= o + sigma,
--
-- because an active transformed residue can disappear only at a singular
-- local matrix.  This file proves the exact composition
--
--   128 <= s * (o + sigma).
--
-- IMPORTANT AUTHORITY BOUNDARY
-- This module does not pretend to prove Borello--Sole's Fourier theorem or the
-- FIPS-specific support-counting/local-rank theorem.  Those are explicit
-- proof-bearing inputs here.  What is proved here is the nontrivial theorem
-- wiring that turns them into the robust singular-budget obstruction.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_; _+_; _*_)
import Data.Nat.Properties as NatP

supportBudgetLift :
  (sourceSupport harmonicSupport survivingSupport singularBudget : Nat) →
  128 ≤ sourceSupport * harmonicSupport →
  harmonicSupport ≤ survivingSupport + singularBudget →
  128 ≤ sourceSupport * (survivingSupport + singularBudget)
supportBudgetLift
  sourceSupport harmonicSupport survivingSupport singularBudget
  uncertainty128 killedOnlyAtSingular =
  NatP.≤-trans
    uncertainty128
    (NatP.*-monoʳ-≤ sourceSupport killedOnlyAtSingular)

record SingularBudgetUncertaintyCertificate : Set where
  constructor singular-budget-certificate
  field
    sourceSupport : Nat
    harmonicSupport : Nat
    survivingSupport : Nat
    singularBudget : Nat

    finiteFieldUncertainty128 :
      128 ≤ sourceSupport * harmonicSupport

    activeResiduesKilledOnlyAtSingularBlocks :
      harmonicSupport ≤ survivingSupport + singularBudget

open SingularBudgetUncertaintyCertificate public

singularBudgetUncertainty128 :
  (certificate : SingularBudgetUncertaintyCertificate) →
  128 ≤
    sourceSupport certificate *
    (survivingSupport certificate + singularBudget certificate)
singularBudgetUncertainty128 certificate =
  supportBudgetLift
    (sourceSupport certificate)
    (harmonicSupport certificate)
    (survivingSupport certificate)
    (singularBudget certificate)
    (finiteFieldUncertainty128 certificate)
    (activeResiduesKilledOnlyAtSingularBlocks certificate)

------------------------------------------------------------------------
-- Full-rank specialization: sigma = 0.
------------------------------------------------------------------------

record FullRankUncertaintyCertificate : Set where
  constructor full-rank-certificate
  field
    sourceSupport : Nat
    harmonicSupport : Nat
    survivingSupport : Nat

    finiteFieldUncertainty128 :
      128 ≤ sourceSupport * harmonicSupport

    noResidueLossUnderLocalInvertibility :
      harmonicSupport ≤ survivingSupport

open FullRankUncertaintyCertificate public

fullRankUncertainty128 :
  (certificate : FullRankUncertaintyCertificate) →
  128 ≤ sourceSupport certificate * survivingSupport certificate
fullRankUncertainty128 certificate =
  NatP.≤-trans
    (finiteFieldUncertainty128 certificate)
    (NatP.*-monoʳ-≤
      (sourceSupport certificate)
      (noResidueLossUnderLocalInvertibility certificate))
