module DASHI.Physics.Closure.NSTriadKNQuarticSignedNearFarDecomposition where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Venue/year: Grundlehren der mathematischen Wissenschaften 343,
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
-- Uses: Chapter 2, Bony decomposition and dyadic interaction classes.
-- Relationship: adapts the paraproduct taxonomy to exact signed periodic
-- triad fibres.  The seven-class equality is DASHI-specific.  Chart switches
-- are deliberately outside the physical classifier.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_)

data SignedCubicClass : Set where
  near lowHigh highLow farLow farHigh transition residual :
    SignedCubicClass

record ExactSignedNearFarDecomposition {c s r : Level} :
    Set (lsuc (c ⊔ s ⊔ r)) where
  field
    Cutoff : Set c
    State : Set s
    Triad : Set s
    SignedScalar : Set r

    addSigned : SignedScalar → SignedScalar → SignedScalar
    zeroValue : SignedScalar

    classifier : Triad → SignedCubicClass
    InPhysicalFiber : Cutoff → State → Triad → Set

    physicalClassClassifierExclusive : ∀ triad c₁ c₂ →
      classifier triad ≡ c₁ →
      classifier triad ≡ c₂ →
      c₁ ≡ c₂

    ClassMember : SignedCubicClass → Triad → Set
    classMemberSound : ∀ class triad →
      ClassMember class triad →
      classifier triad ≡ class
    classMemberComplete : ∀ class triad →
      classifier triad ≡ class →
      ClassMember class triad

    classFiltersPairwiseDisjoint : ∀ c₁ c₂ triad →
      (c₁ ≡ c₂ → ⊥) →
      ClassMember c₁ triad →
      ClassMember c₂ triad →
      ⊥

    classFiltersCoverEveryPhysicalTriad : ∀ N state triad →
      InPhysicalFiber N state triad →
      ClassMember (classifier triad) triad

    DuplicateFreePhysicalFiber : Cutoff → State → Set
    DuplicateFreeClassFiber :
      SignedCubicClass → Cutoff → State → Set
    classFiltersPreserveNoDuplicates : ∀ class N state →
      DuplicateFreePhysicalFiber N state →
      DuplicateFreeClassFiber class N state

    realityMate : Triad → Triad
    classFiltersRealityOrbitCompatible : ∀ triad →
      classifier (realityMate triad) ≡ classifier triad

    fullCubicSigned : Cutoff → State → SignedScalar
    classSigned :
      SignedCubicClass → Cutoff → State → SignedScalar

    fullCubicSignedSevenClassPartition : ∀ N state →
      fullCubicSigned N state
      ≡
      addSigned
        (classSigned near N state)
        (addSigned
          (classSigned lowHigh N state)
          (addSigned
            (classSigned highLow N state)
            (addSigned
              (classSigned farLow N state)
              (addSigned
                (classSigned farHigh N state)
                (addSigned
                  (classSigned transition N state)
                  (classSigned residual N state))))))

open ExactSignedNearFarDecomposition public

physicalClassClassifierTotal :
  ∀ {c s r}
    (D : ExactSignedNearFarDecomposition {c} {s} {r}) →
  Triad D → SignedCubicClass
physicalClassClassifierTotal D = classifier D

record QuantitativeNearFarBounds
    {c s r : Level}
    (D : ExactSignedNearFarDecomposition {c} {s} {r}) :
    Set (lsuc (c ⊔ s ⊔ r)) where
  field
    magnitude : SignedScalar D → Nat
    dissipation controlledRemainder :
      Cutoff D → State D → Nat

    nearNumerator nearDenominator : Nat
    lowHighNumerator lowHighDenominator : Nat
    highLowNumerator highLowDenominator : Nat
    farLowNumerator farLowDenominator : Nat
    farHighNumerator farHighDenominator : Nat
    transitionNumerator transitionDenominator : Nat

    nearSignedClassBound : ∀ N state →
      nearDenominator * magnitude (classSigned D near N state)
      ≤
      nearNumerator * dissipation N state
      + nearDenominator * controlledRemainder N state

    lowHighSignedClassBound : ∀ N state →
      lowHighDenominator * magnitude (classSigned D lowHigh N state)
      ≤
      lowHighNumerator * dissipation N state
      + lowHighDenominator * controlledRemainder N state

    highLowSignedClassBound : ∀ N state →
      highLowDenominator * magnitude (classSigned D highLow N state)
      ≤
      highLowNumerator * dissipation N state
      + highLowDenominator * controlledRemainder N state

    farLowSignedCommutatorBound : ∀ N state →
      farLowDenominator * magnitude (classSigned D farLow N state)
      ≤
      farLowNumerator * dissipation N state
      + farLowDenominator * controlledRemainder N state

    farHighSignedTailBound : ∀ N state →
      farHighDenominator * magnitude (classSigned D farHigh N state)
      ≤
      farHighNumerator * dissipation N state
      + farHighDenominator * controlledRemainder N state

    transitionSignedClassBound : ∀ N state →
      transitionDenominator
      * magnitude (classSigned D transition N state)
      ≤
      transitionNumerator * controlledRemainder N state

    FixedChartInterval : Cutoff D → State D → Set
    fixedChartResidualClassVanishes : ∀ N state →
      FixedChartInterval N state →
      classSigned D residual N state ≡ zeroValue D

    triangleMagnitude : ∀ x y →
      magnitude (addSigned D x y) ≤ magnitude x + magnitude y

    signedClassBoundsAssemble : ∀ N state →
      magnitude (fullCubicSigned D N state)
      ≤
      magnitude (classSigned D near N state)
      + (magnitude (classSigned D lowHigh N state)
      + (magnitude (classSigned D highLow N state)
      + (magnitude (classSigned D farLow N state)
      + (magnitude (classSigned D farHigh N state)
      + (magnitude (classSigned D transition N state)
      + magnitude (classSigned D residual N state))))))

    FavourableClass :
      SignedCubicClass → Cutoff D → State D → Set
    RetainedWithSign :
      SignedCubicClass → Cutoff D → State D → Set
    beneficialSignedClassesRetained : ∀ class N state →
      FavourableClass class N state →
      RetainedWithSign class N state

open QuantitativeNearFarBounds public

data ChartSwitch {c s r : Level}
    (D : ExactSignedNearFarDecomposition {c} {s} {r}) :
    Set (c ⊔ s) where
  switch : Cutoff D → State D → ChartSwitch D

record ChartSwitchJumpControl
    {c s r : Level}
    (D : ExactSignedNearFarDecomposition {c} {s} {r}) :
    Set (lsuc (c ⊔ s ⊔ r)) where
  field
    oldValue newValue : ChartSwitch D → SignedScalar D
    _≤S_ : SignedScalar D → SignedScalar D → Set r
    chartSwitchSeparatedFromContinuousDerivative : ∀ event →
      _≤S_ (newValue event) (oldValue event)

open ChartSwitchJumpControl public

exactSevenClassTargetImplemented : Bool
exactSevenClassTargetImplemented = true

exactSevenClassTargetImplementedIsTrue :
  exactSevenClassTargetImplemented ≡ true
exactSevenClassTargetImplementedIsTrue = refl

literalSignedSevenClassEqualityClosed : Bool
literalSignedSevenClassEqualityClosed = false

literalSignedSevenClassEqualityClosedIsFalse :
  literalSignedSevenClassEqualityClosed ≡ false
literalSignedSevenClassEqualityClosedIsFalse = refl
