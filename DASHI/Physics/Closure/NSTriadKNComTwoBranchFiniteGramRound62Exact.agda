module DASHI.Physics.Closure.NSTriadKNComTwoBranchFiniteGramRound62Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Result/context: finite Cauchy--Schwarz inequality.
-- DOI: not applicable to the original nineteenth-century results.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- DOI: 10.1007/BF02099744.
--
-- Author: Piero D'Ancona.
-- Title: "A Short Proof of Commutator Estimates".
-- DOI: 10.1007/s00041-018-9612-8.
-- Correction DOI: 10.1007/s00041-019-09724-7.
--
-- ROUND 62 CONTRIBUTION / AUTHORITY CORRECTION
--
-- This object is deliberately a RATIONAL MAJORANT CERTIFICATE, not the literal
-- physical odd-(P/Q) Fourier energy.  The physical coefficient carrier is a
-- constructive real/complex carrier; identifying it with Q would be wrong.
-- `NSTriadKNComBishopNormalizedMajorantRound62Exact` is the carrier-correct
-- physical boundary.
--
-- The useful finite algebra survives intact.  Given two explicit rational
-- branch-pair families and the four one-sided norm estimates
--
--   ||L_s||^2 <= strongGap,   ||R_s||^2 <= 1,
--   ||L_w||^2 <= weakGap,     ||R_w||^2 <= 1,
--
-- exact finite Cauchy--Schwarz proves the rational certificate mass is below
-- the six-three envelope.  With common-hat support and exact distances this
-- gives 17/64, 65/512, 65/512 and hence 133/256.  A physical theorem may use
-- these values as majorants only through an explicit ordered-real embedding.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNComCommonHatSupportLeafRound58 as Hat
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreMassLeafRound58 as Targets
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreAggregateRound60Exact as Aggregate
import DASHI.Physics.Closure.NSTriadKNComSameAdjacentActiveRound47Exact as Active
import DASHI.Physics.Closure.NSTriadKNLuoSixThreeCenteredCommutatorScaleExact as SixThree

record RationalTwoBranchGramCertificate : Set₁ where
  field
    support : Hat.PhysicalOddPQCommonHatIdentification
    strongPairs weakPairs : Nat → Nat → List L2.Pair

    shellDistance : Nat → Nat → Nat
    sameShellDistance : ∀ q → shellDistance q q ≡ zero
    forwardAdjacentDistance : ∀ q → shellDistance q (suc q) ≡ suc zero
    reverseAdjacentDistance : ∀ q → shellDistance (suc q) q ≡ suc zero

    inactiveCertificateZero : ∀ q r →
      Hat.supportActive support q r ≡ false →
      L2.square (L2.pairDot (strongPairs q r))
        + L2.square (L2.pairDot (weakPairs q r))
      ≡ 0ℚ

    strongLeftMassBound : ∀ q r →
      Hat.supportActive support q r ≡ true →
      L2.leftNormSquared (strongPairs q r)
      ≤ SixThree.strongBranchSquaredGap (shellDistance q r)

    strongRightContraction : ∀ q r →
      Hat.supportActive support q r ≡ true →
      L2.rightNormSquared (strongPairs q r) ≤ 1ℚ

    weakLeftMassBound : ∀ q r →
      Hat.supportActive support q r ≡ true →
      L2.leftNormSquared (weakPairs q r)
      ≤ SixThree.weakBranchSquaredGap (shellDistance q r)

    weakRightContraction : ∀ q r →
      Hat.supportActive support q r ≡ true →
      L2.rightNormSquared (weakPairs q r) ≤ 1ℚ

open RationalTwoBranchGramCertificate public

certificatePairProduct :
  RationalTwoBranchGramCertificate → Nat → Nat → ℚ
certificatePairProduct certificate q r =
  L2.square (L2.pairDot (strongPairs certificate q r))
  + L2.square (L2.pairDot (weakPairs certificate q r))

certificatePairProductNonnegative :
  (certificate : RationalTwoBranchGramCertificate) →
  ∀ q r → 0ℚ ≤ certificatePairProduct certificate q r
certificatePairProductNonnegative certificate q r =
  L2.addNonnegative
    (L2.squareNonnegative (L2.pairDot (strongPairs certificate q r)))
    (L2.squareNonnegative (L2.pairDot (weakPairs certificate q r)))

private
  branchPairBelowBudget :
    (pairs : List L2.Pair) → (budget : ℚ) →
    0ℚ ≤ budget →
    L2.leftNormSquared pairs ≤ budget →
    L2.rightNormSquared pairs ≤ 1ℚ →
    L2.square (L2.pairDot pairs) ≤ budget
  branchPairBelowBudget pairs budget budgetNN leftBound rightBound =
    ℚP.≤-trans
      (L2.finiteCauchySchwarzSquared pairs)
      (subst
        (λ upper →
          L2.leftNormSquared pairs * L2.rightNormSquared pairs ≤ upper)
        (ℚP.*-identityʳ budget)
        (L2.nonnegativeProductMonotone
          (L2.leftNormSquaredNonnegative pairs)
          (L2.rightNormSquaredNonnegative pairs)
          budgetNN ℚP.0≤1 leftBound rightBound))

strongPairBelowStrongGap :
  (certificate : RationalTwoBranchGramCertificate) → ∀ q r →
  Hat.supportActive (support certificate) q r ≡ true →
  L2.square (L2.pairDot (strongPairs certificate q r))
  ≤ SixThree.strongBranchSquaredGap (shellDistance certificate q r)
strongPairBelowStrongGap certificate q r active =
  branchPairBelowBudget
    (strongPairs certificate q r)
    (SixThree.strongBranchSquaredGap (shellDistance certificate q r))
    (SixThree.strongBranchSquaredNonnegative (shellDistance certificate q r))
    (strongLeftMassBound certificate q r active)
    (strongRightContraction certificate q r active)

weakPairBelowWeakGap :
  (certificate : RationalTwoBranchGramCertificate) → ∀ q r →
  Hat.supportActive (support certificate) q r ≡ true →
  L2.square (L2.pairDot (weakPairs certificate q r))
  ≤ SixThree.weakBranchSquaredGap (shellDistance certificate q r)
weakPairBelowWeakGap certificate q r active =
  branchPairBelowBudget
    (weakPairs certificate q r)
    (SixThree.weakBranchSquaredGap (shellDistance certificate q r))
    (SixThree.weakBranchSquaredNonnegative (shellDistance certificate q r))
    (weakLeftMassBound certificate q r active)
    (weakRightContraction certificate q r active)

activeCertificateBelowSixThree :
  (certificate : RationalTwoBranchGramCertificate) → ∀ q r →
  Hat.supportActive (support certificate) q r ≡ true →
  certificatePairProduct certificate q r
  ≤ SixThree.twoBranchSquaredGap (shellDistance certificate q r)
activeCertificateBelowSixThree certificate q r active =
  ℚP.+-mono-≤
    (strongPairBelowStrongGap certificate q r active)
    (weakPairBelowWeakGap certificate q r active)

sameCertificateBelowTarget :
  (certificate : RationalTwoBranchGramCertificate) → ∀ q →
  certificatePairProduct certificate q q ≤ Targets.sameShellTarget
sameCertificateBelowTarget certificate q
  with Hat.supportActive (support certificate) q q in activeProof
... | true =
  subst
    (λ upper → certificatePairProduct certificate q q ≤ upper)
    Active.sixThreeSameShellExact
    (subst
      (λ gap →
        certificatePairProduct certificate q q
        ≤ SixThree.twoBranchSquaredGap gap)
      (sameShellDistance certificate q)
      (activeCertificateBelowSixThree certificate q q activeProof))
... | false =
  subst
    (λ left → left ≤ Targets.sameShellTarget)
    (sym (inactiveCertificateZero certificate q q activeProof))
    Aggregate.sameTargetNonnegative

forwardCertificateBelowTarget :
  (certificate : RationalTwoBranchGramCertificate) → ∀ q →
  certificatePairProduct certificate q (suc q) ≤ Targets.adjacentShellTarget
forwardCertificateBelowTarget certificate q
  with Hat.supportActive (support certificate) q (suc q) in activeProof
... | true =
  subst
    (λ upper → certificatePairProduct certificate q (suc q) ≤ upper)
    Active.sixThreeAdjacentShellExact
    (subst
      (λ gap →
        certificatePairProduct certificate q (suc q)
        ≤ SixThree.twoBranchSquaredGap gap)
      (forwardAdjacentDistance certificate q)
      (activeCertificateBelowSixThree certificate q (suc q) activeProof))
... | false =
  subst
    (λ left → left ≤ Targets.adjacentShellTarget)
    (sym (inactiveCertificateZero certificate q (suc q) activeProof))
    Aggregate.adjacentTargetNonnegative

reverseCertificateBelowTarget :
  (certificate : RationalTwoBranchGramCertificate) → ∀ q →
  certificatePairProduct certificate (suc q) q ≤ Targets.adjacentShellTarget
reverseCertificateBelowTarget certificate q
  with Hat.supportActive (support certificate) (suc q) q in activeProof
... | true =
  subst
    (λ upper → certificatePairProduct certificate (suc q) q ≤ upper)
    Active.sixThreeAdjacentShellExact
    (subst
      (λ gap →
        certificatePairProduct certificate (suc q) q
        ≤ SixThree.twoBranchSquaredGap gap)
      (reverseAdjacentDistance certificate q)
      (activeCertificateBelowSixThree certificate (suc q) q activeProof))
... | false =
  subst
    (λ left → left ≤ Targets.adjacentShellTarget)
    (sym (inactiveCertificateZero certificate (suc q) q activeProof))
    Aggregate.adjacentTargetNonnegative

certificateBandwidthOneMass :
  RationalTwoBranchGramCertificate → Nat → ℚ
certificateBandwidthOneMass certificate q =
  certificatePairProduct certificate q q
  + certificatePairProduct certificate q (suc q)
  + certificatePairProduct certificate (suc q) q

certificateBandwidthOneMassBelow133Over256 :
  (certificate : RationalTwoBranchGramCertificate) → ∀ q →
  certificateBandwidthOneMass certificate q ≤ Aggregate.bandwidthOneTarget
certificateBandwidthOneMassBelow133Over256 certificate q =
  subst
    (λ upper → certificateBandwidthOneMass certificate q ≤ upper)
    Aggregate.targetArithmetic
    (ℚP.+-mono-≤
      (ℚP.+-mono-≤
        (sameCertificateBelowTarget certificate q)
        (forwardCertificateBelowTarget certificate q))
      (reverseCertificateBelowTarget certificate q))

rationalTwoBranchObjectIsOnlyMajorantCertificate : Bool
rationalTwoBranchObjectIsOnlyMajorantCertificate = true

finiteCauchyClosesRationalMajorantAlgebra : Bool
finiteCauchyClosesRationalMajorantAlgebra = true

rationalTwoBranchObjectIsOnlyMajorantCertificateIsTrue :
  rationalTwoBranchObjectIsOnlyMajorantCertificate ≡ true
rationalTwoBranchObjectIsOnlyMajorantCertificateIsTrue = refl

finiteCauchyClosesRationalMajorantAlgebraIsTrue :
  finiteCauchyClosesRationalMajorantAlgebra ≡ true
finiteCauchyClosesRationalMajorantAlgebraIsTrue = refl
