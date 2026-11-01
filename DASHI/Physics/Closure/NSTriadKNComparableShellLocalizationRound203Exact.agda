module DASHI.Physics.Closure.NSTriadKNComparableShellLocalizationRound203Exact where

------------------------------------------------------------------------
-- ROUND203 / PHYSICAL CC SHELL LOCALIZATION BEFORE COVARIANCE ESTIMATION
--
-- Round202 reduces arbitrary-data Package A to quantitative residual budgets
-- for the three physical classes FL / HH->L / CC.  For CC, the authoritative
-- Round25/63 classifier already contains more information than the tag alone:
--
--   not (j_p + Csep < j_q),
--   not (j_q + Csep < j_p),
--   and at least one of
--     not (j_k + Csep < j_p),
--     not (j_k + Csep < j_q).
--
-- This module turns those executable Bool failures into ordered-Nat evidence.
-- Hence every literal CC incidence carries the exact finite-collar data
--
--   j_q <= j_p + Csep,
--   j_p <= j_q + Csep,
--   (j_p <= j_k + Csep) OR (j_q <= j_k + Csep).
--
-- This is the correct first CC producer theorem: comparable interactions are
-- no longer an unstructured catch-all.  It deliberately does NOT claim that
-- the remaining same-collar Gram debt is nonpositive or already absorbed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

import DASHI.Physics.Closure.NSPeriodicNearTriadClassification as Near
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNPhysicalScaleTrichotomy as Scale
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as Support

-- Executable strict order is ordinary Nat strict order.  We only need the
-- fail-side conversion here: if m<n computes false, then n<=m.
natLessFalseToReverseLe :
  ∀ {m n : Nat} → Near.natLess m n ≡ false → n ≤ m
natLessFalseToReverseLe {zero} {zero} proof = z≤n
natLessFalseToReverseLe {zero} {suc n} ()
natLessFalseToReverseLe {suc m} {zero} proof = z≤n
natLessFalseToReverseLe {suc m} {suc n} proof =
  s≤s (natLessFalseToReverseLe proof)

record ComparableShellLocalization
    (tau : Physical.PhysicalTriadIncidence) : Set where
  constructor comparable-shell-localization
  field
    qNotFarAboveP :
      Shell.shellIndex (Physical.q tau)
      ≤ Shell.shellIndex (Physical.p tau) + Shell.Csep

    pNotFarAboveQ :
      Shell.shellIndex (Physical.p tau)
      ≤ Shell.shellIndex (Physical.q tau) + Shell.Csep

    oneInputNotFarAboveOutput :
      (Shell.shellIndex (Physical.p tau)
        ≤ Shell.shellIndex (Physical.k tau) + Shell.Csep)
      ⊎
      (Shell.shellIndex (Physical.q tau)
        ≤ Shell.shellIndex (Physical.k tau) + Shell.Csep)

open ComparableShellLocalization public

comparableConditionToShellLocalization :
  ∀ {tau} →
  Scale.ScaleCondition
    Support.literalShellPolicy tau Scale.comparable →
  ComparableShellLocalization tau
comparableConditionToShellLocalization
    (Scale.comparableCondition notPBelowQ notQBelowP outputWitness) =
  comparable-shell-localization
    (natLessFalseToReverseLe notPBelowQ)
    (natLessFalseToReverseLe notQBelowP)
    (outputSide outputWitness)
  where
  outputSide :
    ∀ {tau} →
    (Near.natLess
      (Shell.shellIndex (Physical.k tau) + Shell.Csep)
      (Shell.shellIndex (Physical.p tau)) ≡ false
     ⊎
     Near.natLess
      (Shell.shellIndex (Physical.k tau) + Shell.Csep)
      (Shell.shellIndex (Physical.q tau)) ≡ false) →
    (Shell.shellIndex (Physical.p tau)
      ≤ Shell.shellIndex (Physical.k tau) + Shell.Csep)
    ⊎
    (Shell.shellIndex (Physical.q tau)
      ≤ Shell.shellIndex (Physical.k tau) + Shell.Csep)
  outputSide (inj₁ pWitness) =
    inj₁ (natLessFalseToReverseLe pWitness)
  outputSide (inj₂ qWitness) =
    inj₂ (natLessFalseToReverseLe qWitness)

physicalComparableCertificateLocalizes :
  ∀ {tau} →
  Support.TriadicClassCertificate tau Support.CC →
  ComparableShellLocalization tau
physicalComparableCertificateLocalizes certificate =
  comparableConditionToShellLocalization (Support.classMeaning certificate)

-- The literal classifier collar remains the source of the constant.  We do
-- not silently replace it by a weaker or stronger shell convention.
round203ComparableUsesAuthoritativeCsep : Bool
round203ComparableUsesAuthoritativeCsep = true

round203ComparableInputPairLocalized : Bool
round203ComparableInputPairLocalized = true

round203ComparableAnchoredToOutputOnOneInput : Bool
round203ComparableAnchoredToOutputOnOneInput = true

round203ComparableResidualCovariancePaid : Bool
round203ComparableResidualCovariancePaid = false

round203PackageAClosed : Bool
round203PackageAClosed = false

round203ClayPromotion : Bool
round203ClayPromotion = false

round203ComparableInputPairLocalizedIsTrue :
  round203ComparableInputPairLocalized ≡ true
round203ComparableInputPairLocalizedIsTrue = refl

round203ComparableResidualCovariancePaidIsFalse :
  round203ComparableResidualCovariancePaid ≡ false
round203ComparableResidualCovariancePaidIsFalse = refl

round203PackageAClosedIsFalse : round203PackageAClosed ≡ false
round203PackageAClosedIsFalse = refl
