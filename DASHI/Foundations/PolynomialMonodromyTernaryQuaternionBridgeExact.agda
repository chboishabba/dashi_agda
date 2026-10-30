module DASHI.Foundations.PolynomialMonodromyTernaryQuaternionBridgeExact where

------------------------------------------------------------------------
-- POLYNOMIAL ROOT MONODROMY / BALANCED TERNARY / SPIN LIFT
--
-- Mathematical roots: Abel (1824), Galois (1830--1832), Riemann (1851),
-- and the classical braid-group monodromy construction.
-- Finite permutation group context: Dixon--Mortimer (1996).
-- Quaternion/Spin context: Hamilton (1843); the SU(2)->SO(3) cover.
--
-- DASHI contribution (2026-10-28): reuse existing finite S3, C3, ternary,
-- rational quaternion and Q8 owners; compose explicit finite witnesses.
--
-- WARNING: this is a source-written finite bridge.  It does NOT construct
-- continuous coefficient loops, identify a polynomial's full Galois group,
-- prove Abel--Ruffini, or prove a smooth Spin double-cover theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Empty using (⊥)
open import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; -_; _/_)
open import Data.Vec.Base using (Vec)

import Base369 as Base
import DASHI.Algebra.Trit as Trit
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Mode
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Perm
import DASHI.Foundations.TernaryPermutationS3LawsExact as S3
import DASHI.Foundations.TernaryPermutationCyclicSubgroupsExact as Cyclic
import DASHI.Cognition.PhaseEnrichedTrit as Phase
import DASHI.Algebra.FiniteQuaternionDoubleCover as Q8
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as CD

------------------------------------------------------------------------
-- 1. The six ABC orderings are the EXISTING S3, not six unrelated labels.
-- A braid generator and its inverse induce the same transposition in S3;
-- they are not equal as braid paths.  This carrier is monodromy IMAGE only.
------------------------------------------------------------------------

data BraidLoopGenerator : Set where
  swapAB swapBC undoSwapAB undoSwapBC : BraidLoopGenerator

permutationImage : BraidLoopGenerator → Perm.TriPermutation
permutationImage swapAB = Perm.permSwapLowMid
permutationImage swapBC = Perm.permSwapMidHigh
permutationImage undoSwapAB = Perm.permSwapLowMid
permutationImage undoSwapBC = Perm.permSwapMidHigh

braidImagesSatisfyYangBaxter :
  S3._∙_
    (S3._∙_ (permutationImage swapAB) (permutationImage swapBC))
    (permutationImage swapAB)
  ≡
  S3._∙_
    (S3._∙_ (permutationImage swapBC) (permutationImage swapAB))
    (permutationImage swapBC)
braidImagesSatisfyYangBaxter = refl

permutationCommutator :
  Perm.TriPermutation → Perm.TriPermutation → Perm.TriPermutation
permutationCommutator left right =
  S3._∙_
    (S3._∙_
      (S3._∙_ left right)
      (Perm.inversePermutation left))
    (Perm.inversePermutation right)

adjacentSwapsCommutatorIsThreeCycle :
  permutationCommutator
    (permutationImage swapAB) (permutationImage swapBC)
  ≡ Perm.permRotate2
adjacentSwapsCommutatorIsThreeCycle = refl

threeCycleHasOrderThree :
  S3._∙_ (S3._∙_ Perm.permRotate Perm.permRotate)
    Perm.permRotate
  ≡ Perm.permIdentity
threeCycleHasOrderThree = refl

c3RotationIsActualS3Subgroup :
  Cyclic.embedC3InS3 Phase.phase1 ≡ Perm.permRotate
c3RotationIsActualS3Subgroup = refl

c3CannotProduceAnAdjacentSwap :
  (phase : Phase.Phase3) →
  Cyclic.embedC3InS3 phase ≡ Perm.permSwapLowMid → ⊥
c3CannotProduceAnAdjacentSwap = Cyclic.c3ImageNeverSwapLowMid

------------------------------------------------------------------------
-- 2. A projected return is not a labelled return.
--
-- This is an exact finite model of an invariant coefficient descriptor with
-- a moving root ordering.  No complex parameter path is constructed here.
------------------------------------------------------------------------

record LabelledCoefficientState (Coefficient : Set) : Set where
  constructor labelled
  field
    coefficientDescriptor : Coefficient
    rootOrdering : Perm.TriPermutation

open LabelledCoefficientState public

transportRootLabels : ∀ {Coefficient : Set} →
  Perm.TriPermutation →
  LabelledCoefficientState Coefficient →
  LabelledCoefficientState Coefficient
transportRootLabels action (labelled coefficients ordering) =
  labelled coefficients (S3._∙_ action ordering)

coefficientReturnsAfterLabelMotion : ∀ {Coefficient : Set} →
  (action : Perm.TriPermutation) →
  (state : LabelledCoefficientState Coefficient) →
  coefficientDescriptor (transportRootLabels action state)
    ≡ coefficientDescriptor state
coefficientReturnsAfterLabelMotion action (labelled coefficients ordering) =
  refl

swapChangesIdentityLabelling : ∀ {Coefficient : Set} →
  (coefficients : Coefficient) →
  rootOrdering
    (transportRootLabels Perm.permSwapLowMid
      (labelled coefficients Perm.permIdentity))
  ≡ Perm.permIdentity → ⊥
swapChangesIdentityLabelling coefficients ()

------------------------------------------------------------------------
-- 3. The 3^5 versus 5^3 COMPARISON MUST RETAIN ITS BASE AND EXPONENT.
--
-- Five balanced-ternary positions have 243 possible words.
-- Three positions in the established five-mode carrier have 125 words.
-- No bijection, entropy equivalence or quintic radical formula is inferred.
------------------------------------------------------------------------

FiveBalancedTrits : Set
FiveBalancedTrits = Vec Trit.Trit 5

ThreeFiveModes : Set
ThreeFiveModes = Vec Mode.ComplementMode5 3

fiveTritArithmeticCount : Nat
fiveTritArithmeticCount = 3 * (3 * (3 * (3 * 3)))

threeFiveModeArithmeticCount : Nat
threeFiveModeArithmeticCount = 5 * (5 * 5)

fiveTritCountIs243 : fiveTritArithmeticCount ≡ 243
fiveTritCountIs243 = refl

threeFiveModeCountIs125 : threeFiveModeArithmeticCount ≡ 125
threeFiveModeCountIs125 = refl

differentArithmeticCounts :
  fiveTritArithmeticCount ≡ threeFiveModeArithmeticCount → ⊥
differentArithmeticCounts ()

------------------------------------------------------------------------
-- 4. A SPECIFIC rational unit quaternion gives the SAME C3 action on
-- {i,j,k} but remembers one additional CENTRAL sign.
--
-- u=(1+i+j+k)/2; its conjugation cycles i -> j -> k -> i.
-- u^3=-1 and u^6=+1.  Thus its spatial action closes after
-- three 120-degree steps (360 degrees), but its spin lift closes after
-- six such steps (720 degrees).  The angles are explanatory, not a
-- construction of the full continuous rotation path.
------------------------------------------------------------------------

half : ℚ
half = Int.+ 1 / 2

spinThirdTurn : Q.RationalQuaternion
spinThirdTurn = Q.quat half half half half

negativeUnitQuaternion : Q.RationalQuaternion
negativeUnitQuaternion = Q.quat (- 1ℚ) 0ℚ 0ℚ 0ℚ

spinSquare : Q.RationalQuaternion
spinSquare = Q._*q_ spinThirdTurn spinThirdTurn

spinCube : Q.RationalQuaternion
spinCube = Q._*q_ spinSquare spinThirdTurn

spinSix : Q.RationalQuaternion
spinSix = Q._*q_ spinCube spinCube

spinThirdTurnHasUnitNorm :
  CD.quaternionNormSq spinThirdTurn ≡ 1ℚ
spinThirdTurnHasUnitNorm = refl

spinThreeStepsCentralMinus :
  spinCube ≡ negativeUnitQuaternion
spinThreeStepsCentralMinus = refl

spinSixStepsIdentity :
  spinSix ≡ Q.oneQ
spinSixStepsIdentity = refl

imaginaryBasis : Base.TriTruth → Q.RationalQuaternion
imaginaryBasis Base.tri-low = Q.quat 0ℚ 1ℚ 0ℚ 0ℚ
imaginaryBasis Base.tri-mid = Q.quat 0ℚ 0ℚ 1ℚ 0ℚ
imaginaryBasis Base.tri-high = Q.quat 0ℚ 0ℚ 0ℚ 1ℚ

rotateImaginaryBasis : Q.RationalQuaternion → Q.RationalQuaternion
rotateImaginaryBasis value =
  Q._*q_
    (Q._*q_ spinThirdTurn value)
    (CD.quaternionConjugate spinThirdTurn)

spinConjugationIntertwinesABCThreeCycle :
  (name : Base.TriTruth) →
  rotateImaginaryBasis (imaginaryBasis name)
  ≡ imaginaryBasis (Perm.applyPermutation Perm.permRotate name)
spinConjugationIntertwinesABCThreeCycle Base.tri-low = refl
spinConjugationIntertwinesABCThreeCycle Base.tri-mid = refl
spinConjugationIntertwinesABCThreeCycle Base.tri-high = refl

------------------------------------------------------------------------
-- 5. The existing finite Q8 -> V4 quotient is a SEPARATE double-cover
-- witness.  Q8 lacks the half-integral element spinThirdTurn above.
-- The full binary tetrahedral / A4 order-3/order-6 central quotient is
-- already treated by OggSSPP2BinaryTetrahedralRigidificationQuotientExact.
------------------------------------------------------------------------

finiteQ8CentralSignIsInvisible :
  Q8.rho Q8.plusOne ≡ Q8.rho Q8.minusOne
finiteQ8CentralSignIsInvisible = refl

finiteQ8MinusSignNeedsTwoApplications :
  Q8.q8Multiply Q8.minusOne Q8.minusOne ≡ Q8.plusOne
finiteQ8MinusSignNeedsTwoApplications = refl

data ClaimScope : Set where
  finiteRootPermutation
    finiteRationalSpinLift
    geometricCoefficientMonodromy
    fullSmoothSpinCover
    generalQuinticAbelRuffini : ClaimScope

isEstablishedHere : ClaimScope → Bool
isEstablishedHere finiteRootPermutation = true
isEstablishedHere finiteRationalSpinLift = true
isEstablishedHere geometricCoefficientMonodromy = false
isEstablishedHere fullSmoothSpinCover = false
isEstablishedHere generalQuinticAbelRuffini = false

actualComplexMonodromyNotConstructed :
  isEstablishedHere geometricCoefficientMonodromy ≡ false
actualComplexMonodromyNotConstructed = refl

quinticUnsolvabilityNotConstructed :
  isEstablishedHere generalQuinticAbelRuffini ≡ false
quinticUnsolvabilityNotConstructed = refl

------------------------------------------------------------------------
-- ORIGINAL VIDEO M10 / ORIENTATION MAX-CUT.
--
-- Permuting the positive quaternion axes i,j,k by an ODD S3 root-label
-- permutation reverses the oriented product ij=k. Inner conjugation by
-- a unit quaternion is multiplicative, so it cannot implement such an
-- axis-only permutation. A corrected odd swap must negate one axis.
--
-- The actual 180-degree signed swap below is induced on i,j,k by a
-- rational invertible quaternion i+j, with inverse -(i+j)/2. It is a
-- finite exact algebraic witness, NOT an SO(3) path/Spin(3) cover.
-- Classical Hamilton algebra, original Q multiplication owner.
-- Source-written; exact-head Agda kernel acceptance pending.
------------------------------------------------------------------------

positiveI positiveJ positiveK : Q.RationalQuaternion
positiveI = imaginaryBasis Base.tri-low
positiveJ = imaginaryBasis Base.tri-mid
positiveK = imaginaryBasis Base.tri-high

iTimesJIsK : Q._*q_ positiveI positiveJ ≡ positiveK
iTimesJIsK = refl

jTimesIIsNegativeK : Q._*q_ positiveJ positiveI ≡ Q.negQ positiveK
jTimesIIsNegativeK = refl

jTimesKIsI : Q._*q_ positiveJ positiveK ≡ positiveI
jTimesKIsI = refl

kTimesJIsNegativeI : Q._*q_ positiveK positiveJ ≡ Q.negQ positiveI
kTimesJIsNegativeI = refl

kTimesIIsJ : Q._*q_ positiveK positiveI ≡ positiveJ
kTimesIIsJ = refl

iTimesKIsNegativeJ : Q._*q_ positiveI positiveK ≡ Q.negQ positiveJ
iTimesKIsNegativeJ = refl

positiveINotNegative : positiveI ≡ Q.negQ positiveI → ⊥
positiveINotNegative eq with cong Q.q1 eq
... | ()

positiveJNotNegative : positiveJ ≡ Q.negQ positiveJ → ⊥
positiveJNotNegative eq with cong Q.q2 eq
... | ()

positiveKNotNegative : positiveK ≡ Q.negQ positiveK → ⊥
positiveKNotNegative eq with cong Q.q3 eq
... | ()

-- One reusable no-go closes ALL three odd positive-axis swaps.
positiveSwapOfQuaternionAxesImpossible :
  (u v w : Q.RationalQuaternion) →
  Q._*q_ u v ≡ w →
  Q._*q_ v u ≡ Q.negQ w →
  (w ≡ Q.negQ w → ⊥) →
  (F : Q.RationalQuaternion → Q.RationalQuaternion) →
  ((x y : Q.RationalQuaternion) →
    F (Q._*q_ x y) ≡ Q._*q_ (F x) (F y)) →
  F u ≡ v → F v ≡ u → F w ≡ w → ⊥
positiveSwapOfQuaternionAxesImpossible
    u v w uvIsW vuIsNegW nonzero F productMap Fu Fv Fw =
  nonzero
    (trans (sym Fw)
      (trans (cong F (sym uvIsW))
        (trans (productMap u v)
          (trans (cong₂ Q._*q_ Fu Fv) vuIsNegW))))

positiveSwapIJImpossible :
  (F : Q.RationalQuaternion → Q.RationalQuaternion) →
  ((x y : Q.RationalQuaternion) →
    F (Q._*q_ x y) ≡ Q._*q_ (F x) (F y)) →
  F positiveI ≡ positiveJ →
  F positiveJ ≡ positiveI →
  F positiveK ≡ positiveK → ⊥
positiveSwapIJImpossible =
  positiveSwapOfQuaternionAxesImpossible positiveI positiveJ positiveK
    iTimesJIsK jTimesIIsNegativeK positiveKNotNegative

positiveSwapJKImpossible :
  (F : Q.RationalQuaternion → Q.RationalQuaternion) →
  ((x y : Q.RationalQuaternion) →
    F (Q._*q_ x y) ≡ Q._*q_ (F x) (F y)) →
  F positiveJ ≡ positiveK →
  F positiveK ≡ positiveJ →
  F positiveI ≡ positiveI → ⊥
positiveSwapJKImpossible =
  positiveSwapOfQuaternionAxesImpossible positiveJ positiveK positiveI
    jTimesKIsI kTimesJIsNegativeI positiveINotNegative

positiveSwapIKImpossible :
  (F : Q.RationalQuaternion → Q.RationalQuaternion) →
  ((x y : Q.RationalQuaternion) →
    F (Q._*q_ x y) ≡ Q._*q_ (F x) (F y)) →
  F positiveK ≡ positiveI →
  F positiveI ≡ positiveK →
  F positiveJ ≡ positiveJ → ⊥
positiveSwapIKImpossible =
  positiveSwapOfQuaternionAxesImpossible positiveK positiveI positiveJ
    kTimesIIsJ iTimesKIsNegativeJ positiveJNotNegative

-- The orientation correction is an EXACT witness on the original
-- quaternion carrier, not an invented abstract signed-permutation table.
spinSignedSwapIJ : Q.RationalQuaternion
spinSignedSwapIJ = Q.quat 0ℚ 1ℚ 1ℚ 0ℚ

spinSignedSwapIJInverse : Q.RationalQuaternion
spinSignedSwapIJInverse =
  Q.quat 0ℚ (- half) (- half) 0ℚ

spinSignedSwapIJRightInverse :
  Q._*q_ spinSignedSwapIJ spinSignedSwapIJInverse ≡ Q.oneQ
spinSignedSwapIJRightInverse = refl

spinSignedSwapIJLeftInverse :
  Q._*q_ spinSignedSwapIJInverse spinSignedSwapIJ ≡ Q.oneQ
spinSignedSwapIJLeftInverse = refl

rotateBySignedSwapIJ : Q.RationalQuaternion → Q.RationalQuaternion
rotateBySignedSwapIJ value =
  Q._*q_ (Q._*q_ spinSignedSwapIJ value) spinSignedSwapIJInverse

signedSwapIJMapsIToJ :
  rotateBySignedSwapIJ positiveI ≡ positiveJ
signedSwapIJMapsIToJ = refl

signedSwapIJMapsJToI :
  rotateBySignedSwapIJ positiveJ ≡ positiveI
signedSwapIJMapsJToI = refl

signedSwapIJMustNegateK :
  rotateBySignedSwapIJ positiveK ≡ Q.negQ positiveK
signedSwapIJMustNegateK = refl

------------------------------------------------------------------------
-- M10 consumer: an ENTIRE positive-axis S3 action cannot act by
-- multiplication-preserving quaternion maps. It contains an odd swap.
-- The C3 subaction survives and has the exact q^3 = -1 lift above.
------------------------------------------------------------------------

record FullPositiveQuaternionS3Action : Set₁ where
  field
    action : Perm.TriPermutation →
      Q.RationalQuaternion → Q.RationalQuaternion
    preservesQuaternionProduct :
      (p : Perm.TriPermutation) (x y : Q.RationalQuaternion) →
      action p (Q._*q_ x y) ≡
      Q._*q_ (action p x) (action p y)
    positiveBasisPermutation :
      (p : Perm.TriPermutation) (a : Base.TriTruth) →
      action p (imaginaryBasis a) ≡
      imaginaryBasis (Perm.applyPermutation p a)

noFullPositiveQuaternionS3Action :
  FullPositiveQuaternionS3Action → ⊥
noFullPositiveQuaternionS3Action full =
  positiveSwapIJImpossible
    (FullPositiveQuaternionS3Action.action full Perm.permSwapLowMid)
    (FullPositiveQuaternionS3Action.preservesQuaternionProduct
      full Perm.permSwapLowMid)
    (FullPositiveQuaternionS3Action.positiveBasisPermutation
      full Perm.permSwapLowMid Base.tri-low)
    (FullPositiveQuaternionS3Action.positiveBasisPermutation
      full Perm.permSwapLowMid Base.tri-mid)
    (FullPositiveQuaternionS3Action.positiveBasisPermutation
      full Perm.permSwapLowMid Base.tri-high)
