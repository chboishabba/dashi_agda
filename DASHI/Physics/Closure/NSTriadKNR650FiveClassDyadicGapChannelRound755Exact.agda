{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650FiveClassDyadicGapChannelRound755Exact where

------------------------------------------------------------------------
-- ROUND755 / ROUTE THE R748 DYADIC DIFFERENCES THROUGH THE EXISTING
--            TOTAL R25 PHYSICAL TRIAD CLASSIFIER
--
-- The Round25 classifier is total and unique on physical triads:
--
--   LH, HL, HH, CC.
--
-- We do NOT invent a new exhaustive shell partition.  Instead, for each
-- separated class we expose the one R748 coefficient whose shell orientation
-- is forced by the class certificate:
--
--   LH: p + Csep <= q
--       lambda~_p - lambda~_q
--         = - lambda~_p (2^(q-p gap) - 1)
--
--   HL: q + Csep <= p
--       lambda~_p - lambda~_q
--         = + lambda~_q (2^(p-q gap) - 1)
--
--   HH: k + Csep <= q
--       lambda~_k - lambda~_q
--         = - lambda~_k (2^(q-k gap) - 1)
--
-- Each canonical gap is >= Csep = 3.
--
-- The companion coefficient in each class is deliberately left signed unless
-- the class certificate forces its orientation.  CC receives no artificial
-- separation claim.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat.Base using (_≤_; _∸_)
import Data.Nat.Properties as NatP
open import Data.Rational.Base using (ℚ; 1ℚ; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as R25
import DASHI.Physics.Closure.NSTriadKNR650DyadicPairedProductionDifferenceRound748Exact as R748
import DASHI.Physics.Closure.NSTriadKNR650DyadicDifferenceGapFactorRound753Exact as R753

gapWitness :
  (lower higher : Nat) →
  lower ≤ higher →
  higher ≡ lower + (higher ∸ lower)
gapWitness lower higher lower≤higher =
  trans
    (sym (NatP.m∸n+n≡m lower≤higher))
    (NatP.+-comm (higher ∸ lower) lower)

separationGapAtLeast :
  ∀ {lower higher} →
  lower + Shell.Csep ≤ higher →
  Shell.Csep ≤ higher ∸ lower
separationGapAtLeast {lower} {higher} separated =
  let
    monotone :
      (lower + Shell.Csep) ∸ lower
      ≤ higher ∸ lower
    monotone =
      NatP.∸-monoˡ-≤ lower separated
  in
  subst
    (_≤ higher ∸ lower)
    (NatP.m+n∸m≡n lower Shell.Csep)
    monotone

lhGap : Physical.PhysicalTriadIncidence → Nat
lhGap tau =
  Shell.shellIndex (Physical.q tau)
    ∸ Shell.shellIndex (Physical.p tau)

hlGap : Physical.PhysicalTriadIncidence → Nat
hlGap tau =
  Shell.shellIndex (Physical.p tau)
    ∸ Shell.shellIndex (Physical.q tau)

hhKQGap : Physical.PhysicalTriadIncidence → Nat
hhKQGap tau =
  Shell.shellIndex (Physical.q tau)
    ∸ Shell.shellIndex (Physical.k tau)

lhGapAtLeastCsep :
  ∀ {tau} →
  R25.TriadicClassCertificate tau R25.LH →
  Shell.Csep ≤ lhGap tau
lhGapAtLeastCsep {tau} certificate =
  separationGapAtLeast
    (R25.lowHighWeakGap (R25.classMeaning certificate))

hlGapAtLeastCsep :
  ∀ {tau} →
  R25.TriadicClassCertificate tau R25.HL →
  Shell.Csep ≤ hlGap tau
hlGapAtLeastCsep {tau} certificate =
  separationGapAtLeast
    (R25.highLowWeakGap (R25.classMeaning certificate))

hhKQGapAtLeastCsep :
  ∀ {tau} →
  R25.TriadicClassCertificate tau R25.HH →
  Shell.Csep ≤ hhKQGap tau
hhKQGapAtLeastCsep {tau} certificate =
  separationGapAtLeast
    (proj₂
      (R25.highHighWeakGaps
        (R25.classMeaning certificate)))

lhSeparatedCoefficientExact :
  ∀ {tau} →
  R25.TriadicClassCertificate tau R25.LH →
  Z3.NonZeroMode (Physical.p tau) →
  Z3.NonZeroMode (Physical.q tau) →
  R748.selectedDyadicWeight (Physical.p tau)
    - R748.selectedDyadicWeight (Physical.q tau)
  ≡
  - (
    R748.selectedDyadicWeight (Physical.p tau)
      * (R753.shellWeight (lhGap tau) - 1ℚ)
    )
lhSeparatedCoefficientExact {tau}
    certificate pNonzero qNonzero =
  let
    pShell = Shell.shellIndex (Physical.p tau)
    qShell = Shell.shellIndex (Physical.q tau)
    gap = lhGap tau

    p≤q : pShell ≤ qShell
    p≤q =
      NatP.≤-trans
        (NatP.m≤m+n pShell Shell.Csep)
        (R25.lowHighWeakGap (R25.classMeaning certificate))

    qFromP : qShell ≡ pShell + gap
    qFromP = gapWitness pShell qShell p≤q

    qMinusP =
      R753.selectedDyadicWeightDifferenceGapFactor
        (Physical.p tau) (Physical.q tau)
        pNonzero qNonzero gap qFromP
  in
  trans
    (solve
      ( R748.selectedDyadicWeight (Physical.p tau)
      ∷ R748.selectedDyadicWeight (Physical.q tau)
      ∷ []))
    (cong -_ qMinusP)

hlSeparatedCoefficientExact :
  ∀ {tau} →
  R25.TriadicClassCertificate tau R25.HL →
  Z3.NonZeroMode (Physical.p tau) →
  Z3.NonZeroMode (Physical.q tau) →
  R748.selectedDyadicWeight (Physical.p tau)
    - R748.selectedDyadicWeight (Physical.q tau)
  ≡
  R748.selectedDyadicWeight (Physical.q tau)
    * (R753.shellWeight (hlGap tau) - 1ℚ)
hlSeparatedCoefficientExact {tau}
    certificate pNonzero qNonzero =
  let
    pShell = Shell.shellIndex (Physical.p tau)
    qShell = Shell.shellIndex (Physical.q tau)
    gap = hlGap tau

    q≤p : qShell ≤ pShell
    q≤p =
      NatP.≤-trans
        (NatP.m≤m+n qShell Shell.Csep)
        (R25.highLowWeakGap (R25.classMeaning certificate))

    pFromQ : pShell ≡ qShell + gap
    pFromQ = gapWitness qShell pShell q≤p
  in
  R753.selectedDyadicWeightDifferenceGapFactor
    (Physical.q tau) (Physical.p tau)
    qNonzero pNonzero gap pFromQ

hhSeparatedKQCoefficientExact :
  ∀ {tau} →
  R25.TriadicClassCertificate tau R25.HH →
  Z3.NonZeroMode (Physical.k tau) →
  Z3.NonZeroMode (Physical.q tau) →
  R748.selectedDyadicWeight (Physical.k tau)
    - R748.selectedDyadicWeight (Physical.q tau)
  ≡
  - (
    R748.selectedDyadicWeight (Physical.k tau)
      * (R753.shellWeight (hhKQGap tau) - 1ℚ)
    )
hhSeparatedKQCoefficientExact {tau}
    certificate kNonzero qNonzero =
  let
    kShell = Shell.shellIndex (Physical.k tau)
    qShell = Shell.shellIndex (Physical.q tau)
    gap = hhKQGap tau
    gaps = R25.highHighWeakGaps (R25.classMeaning certificate)

    k≤q : kShell ≤ qShell
    k≤q =
      NatP.≤-trans
        (NatP.m≤m+n kShell Shell.Csep)
        (proj₂ gaps)

    qFromK : qShell ≡ kShell + gap
    qFromK = gapWitness kShell qShell k≤q

    qMinusK =
      R753.selectedDyadicWeightDifferenceGapFactor
        (Physical.k tau) (Physical.q tau)
        kNonzero qNonzero gap qFromK
  in
  trans
    (solve
      ( R748.selectedDyadicWeight (Physical.k tau)
      ∷ R748.selectedDyadicWeight (Physical.q tau)
      ∷ []))
    (cong -_ qMinusK)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round755UsesExistingTotalUniquePhysicalClassifier : Bool
round755UsesExistingTotalUniquePhysicalClassifier = true

round755LHSeparatedCoefficientFactoredExactly : Bool
round755LHSeparatedCoefficientFactoredExactly = true

round755HLSeparatedCoefficientFactoredExactly : Bool
round755HLSeparatedCoefficientFactoredExactly = true

round755HHSeparatedCoefficientFactoredExactly : Bool
round755HHSeparatedCoefficientFactoredExactly = true

round755EverySeparatedGapAtLeastThree : Bool
round755EverySeparatedGapAtLeastThree = true

round755ComparableClassGivenFakeSeparation : Bool
round755ComparableClassGivenFakeSeparation = false

round755CompanionPairPowerSignAssumed : Bool
round755CompanionPairPowerSignAssumed = false

round755IntroducesEstimate : Bool
round755IntroducesEstimate = false

round755ClayPromotion : Bool
round755ClayPromotion = false

round755UsesExistingTotalUniquePhysicalClassifierIsTrue :
  round755UsesExistingTotalUniquePhysicalClassifier ≡ true
round755UsesExistingTotalUniquePhysicalClassifierIsTrue = refl

round755LHSeparatedCoefficientFactoredExactlyIsTrue :
  round755LHSeparatedCoefficientFactoredExactly ≡ true
round755LHSeparatedCoefficientFactoredExactlyIsTrue = refl

round755HLSeparatedCoefficientFactoredExactlyIsTrue :
  round755HLSeparatedCoefficientFactoredExactly ≡ true
round755HLSeparatedCoefficientFactoredExactlyIsTrue = refl

round755HHSeparatedCoefficientFactoredExactlyIsTrue :
  round755HHSeparatedCoefficientFactoredExactly ≡ true
round755HHSeparatedCoefficientFactoredExactlyIsTrue = refl

round755EverySeparatedGapAtLeastThreeIsTrue :
  round755EverySeparatedGapAtLeastThree ≡ true
round755EverySeparatedGapAtLeastThreeIsTrue = refl

round755ComparableClassGivenFakeSeparationIsFalse :
  round755ComparableClassGivenFakeSeparation ≡ false
round755ComparableClassGivenFakeSeparationIsFalse = refl

round755CompanionPairPowerSignAssumedIsFalse :
  round755CompanionPairPowerSignAssumed ≡ false
round755CompanionPairPowerSignAssumedIsFalse = refl

round755IntroducesEstimateIsFalse :
  round755IntroducesEstimate ≡ false
round755IntroducesEstimateIsFalse = refl

round755ClayPromotionIsFalse :
  round755ClayPromotion ≡ false
round755ClayPromotionIsFalse = refl
