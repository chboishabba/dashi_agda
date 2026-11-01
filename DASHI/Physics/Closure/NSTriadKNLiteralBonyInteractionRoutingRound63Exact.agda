module DASHI.Physics.Closure.NSTriadKNLiteralBonyInteractionRoutingRound63Exact where

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
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- ROUND 63 B0 AUTHORITY CORRECTION
--
-- An earlier Round63 draft reimplemented the four-way Bony classifier using
-- weak inequalities j+3<=j'.  The mature physical five-source lane uses the
-- repository's AUTHORITATIVE executable predicate
--
--   natLess (j+3) j' = true,
--
-- i.e. the strict comparison j+3<j'.  The two formulations differ exactly on
-- the three-shell collar and therefore cannot be interchanged.
--
-- This file now delegates classification directly to
-- `NSTriadKNLuoPhysicalFiveClassSupportRound25Exact` and merely exposes a small
-- proof-relevant adapter.  In particular the Round62 witness
--
--   j(q)=0, j(p)=3, j(k)=3
--
-- is AUTHORITATIVELY comparable/CC, not HL.  This correction is important:
-- CC is a triadic Bony class, while the fifth `Com` source in Round25 is the
-- separately appended differentiated-commutator cell.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Agda.Builtin.Sigma using (_,_)
open import Data.Nat.Base using (∣_-_∣; _≤_)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as Support
import DASHI.Physics.Closure.NSTriadKNComRawHardLowPassCommonHatNoGoRound62Exact as Raw

data LiteralBonyClass (tau : Physical.PhysicalTriadIncidence) : Set where
  lowHigh :
    Support.TriadicClassCertificate tau Support.LH → LiteralBonyClass tau
  highLow :
    Support.TriadicClassCertificate tau Support.HL → LiteralBonyClass tau
  highHighToLow :
    Support.TriadicClassCertificate tau Support.HH → LiteralBonyClass tau
  comparable :
    Support.TriadicClassCertificate tau Support.CC → LiteralBonyClass tau

classifyLiteralBony :
  (tau : Physical.PhysicalTriadIncidence) → LiteralBonyClass tau
classifyLiteralBony tau with Support.classifyPhysicalTriad tau
... | Support.LH , certificate = lowHigh certificate
... | Support.HL , certificate = highLow certificate
... | Support.HH , certificate = highHighToLow certificate
... | Support.CC , certificate = comparable certificate

lowHighTracksInputWithinOne :
  ∀ {tau} →
  Support.TriadicClassCertificate tau Support.LH →
  ∣ Shell.shellIndex (Physical.k tau)
    - Shell.shellIndex (Physical.q tau) ∣ ≤ 1
lowHighTracksInputWithinOne = Support.lowHighOutputTracksHighOne

highLowTracksAdvectorWithinOne :
  ∀ {tau} →
  Support.TriadicClassCertificate tau Support.HL →
  ∣ Shell.shellIndex (Physical.k tau)
    - Shell.shellIndex (Physical.p tau) ∣ ≤ 1
highLowTracksAdvectorWithinOne = Support.highLowOutputTracksHighOne

highHighInputsWithinOne :
  ∀ {tau} →
  Support.TriadicClassCertificate tau Support.HH →
  ∣ Shell.shellIndex (Physical.p tau)
    - Shell.shellIndex (Physical.q tau) ∣ ≤ 1
highHighInputsWithinOne = Support.highHighInputsComparableOne

farPhysicalTriad : Physical.PhysicalTriadIncidence
farPhysicalTriad =
  Physical.physicalTriad Raw.farP Raw.farInput Raw.farOutput Raw.farResonance

farPShellIsThree :
  Shell.shellIndex Raw.farP ≡ suc (suc (suc zero))
farPShellIsThree = refl

farTriadAuthoritativeClassIsComparable :
  Support.triadicSourceClass farPhysicalTriad ≡ Support.CC
farTriadAuthoritativeClassIsComparable = refl

round62FarWitnessIsCCNotHL : Bool
round62FarWitnessIsCCNotHL = true

authoritativeStrictBonyClassifierReused : Bool
authoritativeStrictBonyClassifierReused = true

round62FarWitnessIsCCNotHLIsTrue :
  round62FarWitnessIsCCNotHL ≡ true
round62FarWitnessIsCCNotHLIsTrue = refl

authoritativeStrictBonyClassifierReusedIsTrue :
  authoritativeStrictBonyClassifierReused ≡ true
authoritativeStrictBonyClassifierReusedIsTrue = refl
