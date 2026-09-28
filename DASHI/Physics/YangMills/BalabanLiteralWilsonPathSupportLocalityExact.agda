{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralWilsonPathSupportLocalityExact where

------------------------------------------------------------------------
-- LITERAL FINITE-BOND SUPPORT OF RATIONAL SU(2) WILSON PATHS/CYLINDERS
--
-- A Wilson path observable depends only on the oriented links encountered by
-- the finite path.  We expose the exact recursive agreement relation and prove
-- holonomy/Wilson-value extensionality from it.  This is the concrete support
-- theorem needed by the two-mark cluster extension; it does not yet assert
-- that an RG/polymer cluster term is local to that support.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact
  using (SignedAxis4)

import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2BondCarrierExact as Carrier
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2ExactGroupLaws as Group
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanLiteralRationalSU2WilsonBoundedAlgebraExact as Wilson

data PathLinkAgreement
    {n : Nat}
    (left right : Carrier.RationalSU2BondData n)
    : Periodic.PeriodicBlock n →
      List SignedAxis4 →
      Set where
  empty :
    ∀ {site} →
    PathLinkAgreement left right site []

  step :
    ∀ {site direction directions} →
    Bond.orientedLink (Carrier.realization left) site direction
      ≡
    Bond.orientedLink (Carrier.realization right) site direction →
    PathLinkAgreement left right
      (Bond.walkStep site direction) directions →
    PathLinkAgreement left right
      site (direction ∷ directions)

pathHolonomyAgreesOnTraversedLinks :
  ∀ {n}
    {left right : Carrier.RationalSU2BondData n}
    site directions →
  PathLinkAgreement left right site directions →
  Bond.pathHolonomy (Carrier.realization left) site directions
  ≡
  Bond.pathHolonomy (Carrier.realization right) site directions
pathHolonomyAgreesOnTraversedLinks site [] empty = refl
pathHolonomyAgreesOnTraversedLinks
    {left = left} {right = right}
    site (direction ∷ directions)
    (step headAgreement tailAgreement) =
  cong₂
    (Bond.multiply Group.rationalSU2ExactLinkGroup)
    headAgreement
    (pathHolonomyAgreesOnTraversedLinks
      (Bond.walkStep site direction)
      directions
      tailAgreement)

literalWilsonPathAgreesOnTraversedLinks :
  ∀ {n}
    (path : Wilson.RationalWilsonPath n)
    {left right : Carrier.RationalSU2BondData n} →
  PathLinkAgreement left right
    (Wilson.base path)
    (Wilson.directions path) →
  Wilson.literalWilsonPathObservable path left
  ≡
  Wilson.literalWilsonPathObservable path right
literalWilsonPathAgreesOnTraversedLinks path agreement =
  cong SU2.realPart
    (pathHolonomyAgreesOnTraversedLinks
      (Wilson.base path)
      (Wilson.directions path)
      agreement)

data CylinderPathAgreement
    {n : Nat}
    (left right : Carrier.RationalSU2BondData n)
    : List (Wilson.RationalWilsonPath n) →
      Set where
  emptyCylinder :
    CylinderPathAgreement left right []

  stepCylinder :
    ∀ {path paths} →
    PathLinkAgreement left right
      (Wilson.base path)
      (Wilson.directions path) →
    CylinderPathAgreement left right paths →
    CylinderPathAgreement left right (path ∷ paths)

productWilsonObservable :
  ∀ {n} →
  List (Wilson.RationalWilsonPath n) →
  Wilson.RationalWilsonObservable n
productWilsonObservable [] =
  Wilson.oneObservable
productWilsonObservable (path ∷ paths) =
  Wilson.multiplyObservable
    (Wilson.literalWilsonPathObservable path)
    (productWilsonObservable paths)

literalWilsonCylinderAgreesOnTraversedLinks :
  ∀ {n}
    (paths : List (Wilson.RationalWilsonPath n))
    {left right : Carrier.RationalSU2BondData n} →
  CylinderPathAgreement left right paths →
  productWilsonObservable paths left
  ≡
  productWilsonObservable paths right
literalWilsonCylinderAgreesOnTraversedLinks [] emptyCylinder = refl
literalWilsonCylinderAgreesOnTraversedLinks
    (path ∷ paths)
    (stepCylinder pathAgreement restAgreement) =
  cong₂ _*_
    (literalWilsonPathAgreesOnTraversedLinks path pathAgreement)
    (literalWilsonCylinderAgreesOnTraversedLinks paths restAgreement)

literalWilsonPathSupportLocalityLevel : ProofLevel
literalWilsonPathSupportLocalityLevel = machineChecked

literalWilsonCylinderSupportLocalityLevel : ProofLevel
literalWilsonCylinderSupportLocalityLevel = machineChecked
