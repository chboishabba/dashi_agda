module DASHI.Physics.YangMills.BalabanWilsonTransferBlockingExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Martin Lüscher,
-- "Construction of a Selfadjoint, Strictly Positive Transfer Matrix for
-- Euclidean Lattice Gauge Theories", Communications in Mathematical Physics
-- 54 (1977), 283--292. DOI: 10.1007/BF01614090.
--
-- Konrad Osterwalder and Erhard Seiler,
-- "Gauge Field Theories on a Lattice", Annals of Physics 110 (1978),
-- 440--471. DOI: 10.1016/0003-4916(78)90039-8.
--
-- Pietro Menotti and Andrea Pelissetto,
-- "General Proof of Osterwalder-Schrader Positivity for the Wilson Action",
-- Communications in Mathematical Physics 113 (1987), 369--373.
-- DOI: 10.1007/BF01221251.
--
-- DASHI CONTRIBUTION
--
-- Distinguish three notions which had been too easy to conflate:
--
--   (1) reflection positivity of the Wilson Euclidean measure;
--   (2) positivity/self-adjointness of the canonical Wilson transfer operator;
--   (3) positivity of the auxiliary Bałaban block-RG transition object.
--
-- Lüscher and Osterwalder--Seiler establish (1) -> (2) for the Wilson theory.
-- That DOES NOT by itself identify (2) with (3).  What the repository already
-- proves, however, is that reflection positivity descends through any blocking
-- whose coarse OS form is literally the pullback of the fine OS form.
--
-- This module composes such blockings exactly.  Therefore finite-scale OS2 is
-- reduced to ONE source-facing theorem at each RG step:
--
--   coarse OS form = pullback of the previous Wilson OS form.
--
-- No entrywise-positive-kernel shortcut is used, and no Bałaban RG kernel is
-- asserted to equal Lüscher's transfer matrix without a same-object theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.FiniteReflectionPositivity as RP
import DASHI.Physics.YangMills.ReflectionPositiveBlocking as Block

composeReflectionPositiveBlocking :
  ∀ {Fine Middle Coarse Scalar : Set}
    {scalar : RP.PositiveAdditiveScalar Scalar}
    {fine : RP.FiniteReflectionPositive Fine Scalar scalar}
    (first : Block.ReflectionPositiveBlocking
      Fine Middle Scalar scalar fine)
    (second : Block.ReflectionPositiveBlocking
      Middle Coarse Scalar scalar
      (Block.blockedReflectionPositive first)) →
  Block.ReflectionPositiveBlocking Fine Coarse Scalar scalar fine
composeReflectionPositiveBlocking first second = record
  { Block.ReflectionPositiveBlocking.liftObservable =
      λ coarse →
        Block.liftObservable first (Block.liftObservable second coarse)
  ; Block.ReflectionPositiveBlocking.coarseOSForm =
      Block.coarseOSForm second
  ; Block.ReflectionPositiveBlocking.coarseFormPullback = λ coarse →
      trans
        (Block.coarseFormPullback second coarse)
        (Block.coarseFormPullback first
          (Block.liftObservable second coarse))
  }

coarseReflectionPositiveAfterTwoCompatibleBlocks :
  ∀ {Fine Middle Coarse Scalar : Set}
    {scalar : RP.PositiveAdditiveScalar Scalar}
    {fine : RP.FiniteReflectionPositive Fine Scalar scalar}
    (first : Block.ReflectionPositiveBlocking
      Fine Middle Scalar scalar fine)
    (second : Block.ReflectionPositiveBlocking
      Middle Coarse Scalar scalar
      (Block.blockedReflectionPositive first)) →
  RP.FiniteReflectionPositive Coarse Scalar scalar
coarseReflectionPositiveAfterTwoCompatibleBlocks first second =
  Block.blockedReflectionPositive
    (composeReflectionPositiveBlocking first second)

composedLiftObservableExact :
  ∀ {Fine Middle Coarse Scalar : Set}
    {scalar : RP.PositiveAdditiveScalar Scalar}
    {fine : RP.FiniteReflectionPositive Fine Scalar scalar}
    (first : Block.ReflectionPositiveBlocking
      Fine Middle Scalar scalar fine)
    (second : Block.ReflectionPositiveBlocking
      Middle Coarse Scalar scalar
      (Block.blockedReflectionPositive first))
    coarse →
  Block.liftObservable
    (composeReflectionPositiveBlocking first second) coarse
  ≡ Block.liftObservable first (Block.liftObservable second coarse)
composedLiftObservableExact first second coarse = refl

reflectionPositiveBlockingCompositionLevel : ProofLevel
reflectionPositiveBlockingCompositionLevel = machineChecked

luscherWilsonTransferMatrixStrictPositivityLevel : ProofLevel
luscherWilsonTransferMatrixStrictPositivityLevel = standardImported

osterwalderSeilerWilsonReflectionPositivityLevel : ProofLevel
osterwalderSeilerWilsonReflectionPositivityLevel = standardImported

menottiPelissettoSitePlaneWilsonReflectionPositivityLevel : ProofLevel
menottiPelissettoSitePlaneWilsonReflectionPositivityLevel = standardImported

literalBalabanBlockingOSPullbackLevel : ProofLevel
literalBalabanBlockingOSPullbackLevel = conditional

balabanRGKernelIsLuscherTransferCompressionLevel : ProofLevel
balabanRGKernelIsLuscherTransferCompressionLevel = conditional
