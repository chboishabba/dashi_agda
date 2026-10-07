module DASHI.Cognition.Teleodynamics.ExceptionalE8Order3CentralizerTransportExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import DASHI.Algebra.Trit using (Trit)

import DASHI.Cognition.Teleodynamics.ExceptionalE6Mod3FiniteGeometryExact as E6
import DASHI.Cognition.Teleodynamics.ExceptionalE6E8PluckerDualityExact as P
import DASHI.Cognition.Teleodynamics.ExceptionalE8Order3SameObjectSymplecticExact as E8Q

------------------------------------------------------------------------
-- E8 ORDER-THREE CENTRALIZER TRANSPORT
--
-- The two explicit Weyl words below commute with w = c^10.  Local exact
-- enumeration verifies that together with w they generate the full centralizer
-- C_W(E8)(w), of order 155520.  Transport through the SAME-OBJECT quotient U
-- gives all Sp4(3), with kernel exactly <w> of order three.
--
-- On projective symplectic lines, the Sp4(3) action has the expected central
-- kernel {+I,-I}, so the effective 40-line permutation group has order 25920.
-- Do not identify that projective action with the full 51840-element E6 null
-- geometry automorphism action without an additional duality/outer involution.
------------------------------------------------------------------------

record Matrix4F3 : Set where
  constructor m4
  field
    a00 a01 a02 a03
    a10 a11 a12 a13
    a20 a21 a22 a23
    a30 a31 a32 a33 : Trit
open Matrix4F3 public

-- Transported image of WORD_A =
-- s2 s7 s1 s2 s4 s1 s4 s3 s4 s7.
centralizerTransportA : Matrix4F3
centralizerTransportA = m4
  P.pos P.zer P.zer P.zer
  P.zer P.pos P.pos P.pos
  P.pos P.zer P.zer P.pos
  P.neg P.zer P.neg P.pos

-- Transported image of WORD_B =
-- s5 s3 s4 s2 s6 s2 s7 s4 s1 s7 s0 s1 s0 s5
-- s2 s7 s5 s3 s7 s5 s2 s6 s5 s4 s5 s7 s6 s5.
centralizerTransportB : Matrix4F3
centralizerTransportB = m4
  P.pos P.pos P.zer P.neg
  P.neg P.neg P.pos P.zer
  P.pos P.pos P.zer P.zer
  P.neg P.zer P.neg P.pos

record E8CentralizerTransportComputationReceipt : Set where
  constructor e8-centralizer-transport-computation-receipt
  field
    grade : E6.EvidenceGrade
    e8WeylOrder : Nat
    wConjugacyOrbitSize : Nat
    fullCentralizerOrder : Nat
    explicitCommutingGeneratorCount : Nat
    explicitLiftGeneratedOrder : Nat
    transportedImageOrder : Nat
    expectedSp4ThreeOrder : Nat
    transportKernelOrder : Nat
    transportKernelIsExactlyW : Bool
    allTransportFibresSizeThree : Bool
    conjugacyOrbitForcesFullCentralizer : Bool
    transportedGeneratorsPreserveStandardSymplecticForm : Bool
    localPythonReproduced : Bool
    provenance : String
open E8CentralizerTransportComputationReceipt public

canonicalE8CentralizerTransportComputationReceipt :
  E8CentralizerTransportComputationReceipt
canonicalE8CentralizerTransportComputationReceipt =
  e8-centralizer-transport-computation-receipt
    E6.localFiniteComputation
    696729600 4480 155520
    2 155520 51840 51840 3
    true true true true true
    "local exact enumeration: conjugacy orbit of w has 4480 elements; explicit commuting words with w generate 155520 lifts; quotient transport is all Sp4(3) and has kernel exactly <w>"

record ProjectiveLineActionComputationReceipt : Set where
  constructor projective-line-action-computation-receipt
  field
    grade : E6.EvidenceGrade
    symplecticLineCount : Nat
    sp4Order : Nat
    projectiveKernelOrder : Nat
    projectiveKernelIsPlusMinusIdentity : Bool
    effectiveLineActionOrder : Nat
    fullE6NullGeometryOrder : Nat
    centralizerLineActionAlreadyEqualsFullE6NullAction : Bool
    localPythonReproduced : Bool
    provenance : String
open ProjectiveLineActionComputationReceipt public

canonicalProjectiveLineActionComputationReceipt :
  ProjectiveLineActionComputationReceipt
canonicalProjectiveLineActionComputationReceipt =
  projective-line-action-computation-receipt
    E6.localFiniteComputation
    40 51840 2 true 25920 51840 false true
    "Sp4(3) acts on the 40 totally isotropic projective lines with kernel {+I,-I}; an additional duality/outer involution is required before comparison with the full 51840 E6 null-geometry action"

-- Abstract exact-sequence interface.  This is the theorem shape consumed by
-- downstream hyperfabric code; concrete group multiplication remains owned by
-- the E8 Weyl implementation rather than reconstructed here.
record CentralizerExactSequence : Set₁ where
  field
    Centralizer : Set
    Sp4 : Set
    wKernel : Centralizer → Set
    transport : Centralizer → Sp4
    transportKernelExactlyW : (g : Centralizer) → Set
    transportSurjective : (s : Sp4) → Set
    provenance : String
open CentralizerExactSequence public

record CentralizerHyperformTransportBoundary : Set where
  constructor centralizer-hyperform-transport-boundary
  field
    sameObjectQuotientConsumed : Bool
    fullCentralizerOrderPaidLocally : Bool
    fullSp4ImagePaidLocally : Bool
    kernelExactlyCyclicThreePaidLocally : Bool
    projectiveKernelPlusMinusIdentityPaidLocally : Bool
    fullE6NullActionIdentifiedWithCentralizerLineAction : Bool
    missingOuterDualityKeptExplicit : Bool
    centralizerTransportPromotedToFullWeylE8Action : Bool

canonicalCentralizerHyperformTransportBoundary :
  CentralizerHyperformTransportBoundary
canonicalCentralizerHyperformTransportBoundary =
  centralizer-hyperform-transport-boundary
    true true true true true false true false
