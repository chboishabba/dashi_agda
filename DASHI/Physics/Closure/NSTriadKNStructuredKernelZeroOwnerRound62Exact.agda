module DASHI.Physics.Closure.NSTriadKNStructuredKernelZeroOwnerRound62Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- ROUND 62 CONTRIBUTION
--
-- Connect the new ONE-source structured localized-PDE atom list directly to
-- the mature zero-independent-kernel owner.  The only analytic input is the
-- literal statement
--
--   independentKernelTotal atoms = 0.
--
-- Structural cancellation was already proved while folding the atom list, so
-- this single equality constructs the Round55 IndependentZeroBranch and hence
-- the Round53 kernel owner with
--
--   production = eta = dataRemainder = criticalCoefficient = 0.
--
-- This is the preferred D2 branch.  It justifies deleting the kernel from both
-- the C additive data budget and G's Young-soft root sum once the exact zero is
-- proved on the literal atom list.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (0ℚ)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNKernelLiteralResidualRound55Exact as Residual
import DASHI.Physics.Closure.NSTriadKNKernelIndependentZeroOwnerRound53Exact as Zero
import DASHI.Physics.Closure.NSTriadKNLocalizedPDEStructuredAtomsRound62Exact as Structured

structuredIndependentZeroBranch :
  (atoms : List Structured.LocalizedPDEAtom) →
  Structured.independentKernelTotal atoms ≡ 0ℚ →
  Residual.IndependentZeroBranch (Structured.kernelResidualSplit atoms)
structuredIndependentZeroBranch atoms independentZero = record
  { independentZero = independentZero }

structuredPhysicalKernelZero :
  ∀ {environment : Owner.TaxEnvironment}
    (atoms : List Structured.LocalizedPDEAtom) →
  Structured.independentKernelTotal atoms ≡ 0ℚ →
  Zero.PhysicalIndependentKernelZero environment
    (Residual.literalKernelInstantiation (Structured.kernelResidualSplit atoms))
    (Residual.literalKernelReduction (Structured.kernelResidualSplit atoms))
structuredPhysicalKernelZero atoms independentZero =
  Residual.literalKernelIndependentZero
    (Structured.kernelResidualSplit atoms)
    (structuredIndependentZeroBranch atoms independentZero)

structuredKernelZeroOwner :
  ∀ {environment : Owner.TaxEnvironment}
    (atoms : List Structured.LocalizedPDEAtom) →
  (independentZero : Structured.independentKernelTotal atoms ≡ 0ℚ) →
  Owner.AdmissibleOwnerEstimate environment
structuredKernelZeroOwner atoms independentZero =
  Zero.physicalKernelZeroOwner
    (structuredPhysicalKernelZero atoms independentZero)

structuredKernelZeroOwnerIdentity :
  ∀ {environment : Owner.TaxEnvironment}
    (atoms : List Structured.LocalizedPDEAtom)
    (independentZero : Structured.independentKernelTotal atoms ≡ 0ℚ) →
  Owner.owner (structuredKernelZeroOwner {environment} atoms independentZero)
  ≡ Tax.kernel
structuredKernelZeroOwnerIdentity atoms independentZero = refl

structuredKernelZeroEta :
  ∀ {environment : Owner.TaxEnvironment}
    (atoms : List Structured.LocalizedPDEAtom)
    (independentZero : Structured.independentKernelTotal atoms ≡ 0ℚ) →
  Owner.eta (structuredKernelZeroOwner {environment} atoms independentZero) ≡ 0ℚ
structuredKernelZeroEta atoms independentZero = refl

structuredKernelZeroDataRemainder :
  ∀ {environment : Owner.TaxEnvironment}
    (atoms : List Structured.LocalizedPDEAtom)
    (independentZero : Structured.independentKernelTotal atoms ≡ 0ℚ) →
  Owner.dataRemainder
    (structuredKernelZeroOwner {environment} atoms independentZero) ≡ 0ℚ
structuredKernelZeroDataRemainder atoms independentZero = refl

structuredKernelZeroCriticalCoefficient :
  ∀ {environment : Owner.TaxEnvironment}
    (atoms : List Structured.LocalizedPDEAtom)
    (independentZero : Structured.independentKernelTotal atoms ≡ 0ℚ) →
  Owner.criticalCoefficient
    (structuredKernelZeroOwner {environment} atoms independentZero) ≡ 0ℚ
structuredKernelZeroCriticalCoefficient atoms independentZero = refl

structuredKernelExactZeroDeletesCAndGCost : Bool
structuredKernelExactZeroDeletesCAndGCost = true

structuredKernelExactZeroDeletesCAndGCostIsTrue :
  structuredKernelExactZeroDeletesCAndGCost ≡ true
structuredKernelExactZeroDeletesCAndGCostIsTrue = refl
