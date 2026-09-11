module DASHI.Wikimedia.IbrahimMonster3BDiagonalKernelPaidSignGaugeCorrectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.IbrahimMonster3BT1ComplementClass18LambdaZeroSnowballExact as Complement
import DASHI.Wikimedia.IbrahimMonster3BPhaseOrientationGaugeSnowballExact as Gauge
import DASHI.Wikimedia.IbrahimMonster3BPrimarySupplementKernelClass20SnowballExact as Kernel

------------------------------------------------------------------------
-- DIAGONAL KERNEL PAID / SIGN NAME GAUGE CORRECTION
--
-- The earlier frontier phrased the remaining quotient question as
--
--   is the Monster kernel <t1*t2> or <t1*t2^-1> ?
--
-- The subsequent source weld pays a stronger invariant statement:
--
--   * t1 is the normal Suzuki-side C3 and its complement lift is main class 18;
--   * classes 18,19,20 are the three lambda lifts over the same underlying
--     quotient class;
--   * class 20 is the unique nonidentity C3 class killed by qGtoN3B.
--
-- Hence the actual diagonal kernel subgroup is already SAME-OBJECT PAID as
--
--   K_M = {1} union main-class-20.
--
-- What remains is only the orientation-dependent NAME of this paid subgroup.
-- Choosing the other nonidentity generator of the extraspecial centre replaces
-- t2 by t2^-1 and interchanges the symbolic names
--
--   <t1*t2>  <->  <t1*t2^-1>.
--
-- Daniel Allcock independently describes the same central product as identifying
-- the scalar omega in 6.Suz with one of the two generators of the Heisenberg
-- centre, explicitly noting the two choices.  That corroborates the gauge
-- interpretation; it does not replace the Barraclough--Wilson/Bray--Wilson
-- concrete Monster quotient evidence.
------------------------------------------------------------------------

allcockMonstrousProposal : Attribution.AttributedSource
allcockMonstrousProposal = Attribution.mkNoDOISource
  "Daniel Allcock"
  "A Monstrous Proposal"
  "arXiv:math/0606043; conference contribution"
  "2006"
  "https://arxiv.org/abs/math/0606043"
  (Attribution.namedSourceKind "research article / conceptual cross-check")
  "independent conceptual source for the two possible identifications of the 6.Suz scalar omega with the two generators of the Heisenberg centre; no DOI asserted here"
  Attribution.publicAttribution

allcockAttribution = Snowball.canonicalSourceRoleSnowballReceipt allcockMonstrousProposal

allcockArxiv : String
allcockArxiv = "math/0606043"

------------------------------------------------------------------------
-- Invariant paid quotient object.
------------------------------------------------------------------------

record PaidMonsterDiagonalKernel : Set where
  constructor paid-monster-diagonal-kernel
  field
    mainTableIdentity : String
    identityClassPosition : Nat
    nonidentityKernelClassPosition : Nat
    nonidentityKernelClassIsTwenty : nonidentityKernelClassPosition ≡ 20
    complementT1ClassPosition : Nat
    complementT1ClassIsEighteen : complementT1ClassPosition ≡ 18
    otherDiagonalLiftClassPosition : Nat
    otherDiagonalLiftClassIsNineteen : otherDiagonalLiftClassPosition ≡ 19
    pairOfDiagonalLiftsPaid : Bool
    qGtoN3BKillsClassTwentyPaid : Bool
open PaidMonsterDiagonalKernel public

canonicalPaidMonsterDiagonalKernel : PaidMonsterDiagonalKernel
canonicalPaidMonsterDiagonalKernel = paid-monster-diagonal-kernel
  "3^1+12:6.Suz.2"
  1
  20 refl
  18 refl
  19 refl
  true true

------------------------------------------------------------------------
-- Naming/orientation is a separate fibre over the invariant subgroup.
------------------------------------------------------------------------

data T2OrientationChoice : Set where
  chooseLambdaOne chooseLambdaTwo : T2OrientationChoice

invertT2Orientation : T2OrientationChoice → T2OrientationChoice
invertT2Orientation chooseLambdaOne = chooseLambdaTwo
invertT2Orientation chooseLambdaTwo = chooseLambdaOne

invertT2OrientationInvolutive :
  (choice : T2OrientationChoice) →
  invertT2Orientation (invertT2Orientation choice) ≡ choice
invertT2OrientationInvolutive chooseLambdaOne = refl
invertT2OrientationInvolutive chooseLambdaTwo = refl

record DiagonalKernelNaming : Set where
  constructor diagonal-kernel-naming
  field
    orientation : T2OrientationChoice
    classTwentySymbolicName : String
    classNineteenSymbolicName : String
open DiagonalKernelNaming public

------------------------------------------------------------------------
-- WrongType / non-promotion boundaries.
------------------------------------------------------------------------

data PaidKernelRequiresAbsoluteSignName : Set where
data ClassTwentyCreatesCanonicalT2Generator : Set where
data AllcockTwoChoicesCreatesMonsterQuotientProof : Set where
data ArxivIdentifierCreatesActionIntertwiner : Set where
data OeisCreatesOrientation : Set where

paidKernelDoesNotRequireSignName : PaidKernelRequiresAbsoluteSignName → ⊥
paidKernelDoesNotRequireSignName ()

classTwentyDoesNotCreateCanonicalGenerator : ClassTwentyCreatesCanonicalT2Generator → ⊥
classTwentyDoesNotCreateCanonicalGenerator ()

allcockDoesNotReplaceMonsterQuotientProof :
  AllcockTwoChoicesCreatesMonsterQuotientProof → ⊥
allcockDoesNotReplaceMonsterQuotientProof ()

arxivDoesNotCreateIntertwiner : ArxivIdentifierCreatesActionIntertwiner → ⊥
arxivDoesNotCreateIntertwiner ()

oeisDoesNotCreateOrientation : OeisCreatesOrientation → ⊥
oeisDoesNotCreateOrientation ()

------------------------------------------------------------------------
-- Attribution/navigation coordinates.
------------------------------------------------------------------------

record DiagonalKernelGaugeExternalCoordinates : Set where
  constructor diagonal-kernel-gauge-external-coordinates
  field
    groupRepresentationQid : String
    finiteGroupQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    allcockArxivCoordinate : String
    oeisCoordinate : String
    oeisHasOrientationAuthority : Bool
open DiagonalKernelGaugeExternalCoordinates public

canonicalDiagonalKernelGaugeExternalCoordinates : DiagonalKernelGaugeExternalCoordinates
canonicalDiagonalKernelGaugeExternalCoordinates = diagonal-kernel-gauge-external-coordinates
  "Q1055807"
  "Q1057968"
  "512.22"
  "512.23"
  "math/0606043"
  "not applicable: generator orientation is not an integer-sequence object"
  false

------------------------------------------------------------------------
-- Corrected highest-alpha frontier.
------------------------------------------------------------------------

record DiagonalKernelGaugeFrontier : Set where
  constructor diagonal-kernel-gauge-frontier
  field
    complementT1Class18Paid : Bool
    twoDiagonalLiftClasses19And20Paid : Bool
    actualMonsterKernelClass20Paid : Bool
    invariantDiagonalKernelSubgroupPaid : Bool
    absoluteT2OrientationPaid : Bool
    symbolicT1T2VersusT1T2InverseNamePaid : Bool
    symbolicSignStillBlocksPairFamilyMonsterOccurrence : Bool
    nextResidual : String
open DiagonalKernelGaugeFrontier public

currentDiagonalKernelGaugeFrontier : DiagonalKernelGaugeFrontier
currentDiagonalKernelGaugeFrontier = diagonal-kernel-gauge-frontier
  true true true true
  false false false
  "do not route proof search through the absolute t1*t2 versus t1*t2^-1 name. The invariant quotient kernel is already paid as {identity} union main class 20. The next Monster-proof payment is execution of the source-written Suzuki/main full-character matcher to establish the 12a/b and 78a/b pair-family occurrence in the actual restricted Monster character. Recover makewords.mag/factor.c only if historical orientation/custody itself is the consumer. If an external convention later fixes the positive extraspecial generator t2, attach the corresponding symbolic sign as a coordinate choice without reopening the paid kernel subgroup."

complementFrontier : Complement.T1ComplementFrontier
complementFrontier = Complement.currentT1ComplementFrontier

kernelFrontier : Kernel.PrimarySupplementKernelFrontier
kernelFrontier = Kernel.currentPrimarySupplementKernelFrontier
