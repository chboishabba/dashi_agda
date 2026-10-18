{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSelectedWilsonBasisLinkJetNormExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (1ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33QuaternionAdjointNormSquaredExact as AdjointNorm
import DASHI.Physics.YangMills.BalabanStrongCouplingLiteralQuaternionAtomNormExact as Atom
import DASHI.Physics.YangMills.BalabanSelectedWilsonBasisInsertionNormExact as BasisInsertion

basisField :
  Coordinates.PhysicalSU2Coordinate4 → Coordinates.PhysicalSU2BondField4
basisField target =
  Coordinates.decodePhysicalSU2 (Basis.physicalBasis target)

pureInsertionNormSqExact :
  ∀ field axis site →
  Norm.normSq
    (Q.pureQuaternion (Physical.insertionAt field axis site))
  ≡ Q.vectorNormSq (Physical.insertionAt field axis site)
pureInsertionNormSqExact field axis site = refl

positiveValueNormSqExact :
  ∀ background field site axis →
  Norm.normSq
    (Q.factorValue (Physical.positiveLinkJet background field site axis))
  ≡ 1ℚ
positiveValueNormSqExact background field site axis =
  AdjointNorm.physicalLinkNormSqExact background (pair site axis)

inverseValueNormSqExact :
  ∀ background field site axis →
  Norm.normSq
    (Q.factorValue (Physical.inverseLinkJet background field site axis))
  ≡ 1ℚ
inverseValueNormSqExact background field site axis =
  AdjointNorm.physicalInverseLinkNormSqExact background (pair site axis)

positiveFirstNormSqExact :
  ∀ background field site axis →
  Norm.normSq
    (Q.factorFirst (Physical.positiveLinkJet background field site axis))
  ≡ Q.vectorNormSq (Physical.insertionAt field axis site)
positiveFirstNormSqExact background field site axis =
  trans
    (Norm.normSqMultiplyExact
      (Physical.link background (pair site axis))
      (Q.pureQuaternion (Physical.insertionAt field axis site)))
    (trans
      (cong
        (Norm.normSq (Physical.link background (pair site axis)) *_)
        (pureInsertionNormSqExact field axis site))
      (subst
        (λ selected →
          selected * Q.vectorNormSq (Physical.insertionAt field axis site)
          ≡ Q.vectorNormSq (Physical.insertionAt field axis site))
        (sym (AdjointNorm.physicalLinkNormSqExact
          background (pair site axis)))
        (ℚRing.solve-∀
          (Q.vectorNormSq (Physical.insertionAt field axis site)))))

inverseFirstNormSqExact :
  ∀ background field site axis →
  Norm.normSq
    (Q.factorFirst (Physical.inverseLinkJet background field site axis))
  ≡ Q.vectorNormSq (Physical.insertionAt field axis site)
inverseFirstNormSqExact background field site axis =
  let
    insertion =
      Q.pureQuaternion (Physical.insertionAt field axis site)
    inverse =
      Physical.inverseLink background (pair site axis)
  in
  trans
    (Norm.normSqMultiplyExact (Q.negQ insertion) inverse)
    (trans
      (cong (_* Norm.normSq inverse)
        (Atom.normSqNegExact insertion))
      (trans
        (cong (Norm.normSq insertion *_)
          (AdjointNorm.physicalInverseLinkNormSqExact
            background (pair site axis)))
        (trans
          (ℚRing.solve-∀ (Norm.normSq insertion))
          (pureInsertionNormSqExact field axis site))))

positiveBasisFirstNormSqBelowOne :
  ∀ background target site axis →
  Norm.normSq
    (Q.factorFirst
      (Physical.positiveLinkJet background (basisField target) site axis))
  ≤ 1ℚ
positiveBasisFirstNormSqBelowOne background target site axis =
  subst
    (λ lower → lower ≤ 1ℚ)
    (sym (positiveFirstNormSqExact
      background (basisField target) site axis))
    (BasisInsertion.basisInsertionNormSqBelowOne target axis site)

inverseBasisFirstNormSqBelowOne :
  ∀ background target site axis →
  Norm.normSq
    (Q.factorFirst
      (Physical.inverseLinkJet background (basisField target) site axis))
  ≤ 1ℚ
inverseBasisFirstNormSqBelowOne background target site axis =
  subst
    (λ lower → lower ≤ 1ℚ)
    (sym (inverseFirstNormSqExact
      background (basisField target) site axis))
    (BasisInsertion.basisInsertionNormSqBelowOne target axis site)

selectedWilsonBasisLinkJetNormLevel : ProofLevel
selectedWilsonBasisLinkJetNormLevel = machineChecked
