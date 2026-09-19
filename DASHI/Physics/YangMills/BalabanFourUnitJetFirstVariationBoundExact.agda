{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFourUnitJetFirstVariationBoundExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_; ∣_∣; NonNegative; Positive; nonNegative; positive)
open import Data.Sum.Base using (inj₁; inj₂)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonJetExact as Jet
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonFirstVariationExact as First
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur

record UnitFirstJetBound (jet : Jet.QuaternionFactorJet) : Set where
  field
    valueNormSqIsOne : Norm.normSq (Jet.factorValue jet) ≡ 1ℚ
    firstNormSqBelowOne : Norm.normSq (Jet.factorFirst jet) ≤ 1ℚ

open UnitFirstJetBound public

atom0 atom1 atom2 atom3 :
  Jet.QuaternionFactorJet → Jet.QuaternionFactorJet →
  Jet.QuaternionFactorJet → Jet.QuaternionFactorJet →
  Jet.RationalQuaternion
atom0 j0 j1 j2 j3 =
  Jet.factorFirst j0 Jet.*q
    Jet.orderedValueProduct (j1 ∷ j2 ∷ j3 ∷ [])
atom1 j0 j1 j2 j3 =
  Jet.factorValue j0 Jet.*q
    (Jet.factorFirst j1 Jet.*q
      Jet.orderedValueProduct (j2 ∷ j3 ∷ []))
atom2 j0 j1 j2 j3 =
  Jet.factorValue j0 Jet.*q
    (Jet.factorValue j1 Jet.*q
      (Jet.factorFirst j2 Jet.*q
        Jet.orderedValueProduct (j3 ∷ [])))
atom3 j0 j1 j2 j3 =
  Jet.factorValue j0 Jet.*q
    (Jet.factorValue j1 Jet.*q
      (Jet.factorValue j2 Jet.*q
        (Jet.factorFirst j3 Jet.*q Jet.oneQ)))

firstVariationTermsFour :
  ∀ j0 j1 j2 j3 →
  Jet.firstVariationTerms (Jet.fourFactorJets j0 j1 j2 j3)
  ≡ atom0 j0 j1 j2 j3
      ∷ atom1 j0 j1 j2 j3
      ∷ atom2 j0 j1 j2 j3
      ∷ atom3 j0 j1 j2 j3
      ∷ []
firstVariationTermsFour j0 j1 j2 j3 = refl

orderedValueNormOne1 :
  ∀ j →
  UnitFirstJetBound j →
  Norm.normSq (Jet.orderedValueProduct (j ∷ [])) ≡ 1ℚ
orderedValueNormOne1 j bound
  rewrite Norm.normSqMultiplyExact (Jet.factorValue j) Jet.oneQ
        | valueNormSqIsOne bound =
  ℚRing.solve []

orderedValueNormOne2 :
  ∀ j0 j1 →
  UnitFirstJetBound j0 → UnitFirstJetBound j1 →
  Norm.normSq (Jet.orderedValueProduct (j0 ∷ j1 ∷ [])) ≡ 1ℚ
orderedValueNormOne2 j0 j1 b0 b1
  rewrite Norm.normSqMultiplyExact
      (Jet.factorValue j0) (Jet.orderedValueProduct (j1 ∷ []))
        | valueNormSqIsOne b0
        | orderedValueNormOne1 j1 b1 =
  ℚRing.solve []

orderedValueNormOne3 :
  ∀ j0 j1 j2 →
  UnitFirstJetBound j0 → UnitFirstJetBound j1 → UnitFirstJetBound j2 →
  Norm.normSq (Jet.orderedValueProduct (j0 ∷ j1 ∷ j2 ∷ [])) ≡ 1ℚ
orderedValueNormOne3 j0 j1 j2 b0 b1 b2
  rewrite Norm.normSqMultiplyExact
      (Jet.factorValue j0) (Jet.orderedValueProduct (j1 ∷ j2 ∷ []))
        | valueNormSqIsOne b0
        | orderedValueNormOne2 j1 j2 b1 b2 =
  ℚRing.solve []

atom0NormBelowOne :
  ∀ j0 j1 j2 j3 →
  UnitFirstJetBound j0 → UnitFirstJetBound j1 →
  UnitFirstJetBound j2 → UnitFirstJetBound j3 →
  Norm.normSq (atom0 j0 j1 j2 j3) ≤ 1ℚ
atom0NormBelowOne j0 j1 j2 j3 b0 b1 b2 b3 =
  subst
    (λ value → value ≤ 1ℚ)
    (trans
      (Norm.normSqMultiplyExact
        (Jet.factorFirst j0)
        (Jet.orderedValueProduct (j1 ∷ j2 ∷ j3 ∷ [])))
      (cong (Norm.normSq (Jet.factorFirst j0) *_)
        (orderedValueNormOne3 j1 j2 j3 b1 b2 b3)))
    (firstNormSqBelowOne b0)

atom1NormBelowOne :
  ∀ j0 j1 j2 j3 →
  UnitFirstJetBound j0 → UnitFirstJetBound j1 →
  UnitFirstJetBound j2 → UnitFirstJetBound j3 →
  Norm.normSq (atom1 j0 j1 j2 j3) ≤ 1ℚ
atom1NormBelowOne j0 j1 j2 j3 b0 b1 b2 b3 =
  let
    innerExact :
      Norm.normSq
        (Jet.factorFirst j1 Jet.*q
          Jet.orderedValueProduct (j2 ∷ j3 ∷ []))
      ≡ Norm.normSq (Jet.factorFirst j1)
    innerExact =
      trans
        (Norm.normSqMultiplyExact
          (Jet.factorFirst j1)
          (Jet.orderedValueProduct (j2 ∷ j3 ∷ [])))
        (trans
          (cong (Norm.normSq (Jet.factorFirst j1) *_)
            (orderedValueNormOne2 j2 j3 b2 b3))
          (ℚRing.solve-∀ (Norm.normSq (Jet.factorFirst j1))))
  in
  subst
    (λ value → value ≤ 1ℚ)
    (trans
      (Norm.normSqMultiplyExact
        (Jet.factorValue j0)
        (Jet.factorFirst j1 Jet.*q
          Jet.orderedValueProduct (j2 ∷ j3 ∷ [])))
      (trans
        (cong (_* Norm.normSq
          (Jet.factorFirst j1 Jet.*q
            Jet.orderedValueProduct (j2 ∷ j3 ∷ [])))
          (valueNormSqIsOne b0))
        (trans
          (ℚRing.solve-∀
            (Norm.normSq
              (Jet.factorFirst j1 Jet.*q
                Jet.orderedValueProduct (j2 ∷ j3 ∷ []))))
          innerExact)))
    (firstNormSqBelowOne b1)

atom2NormBelowOne :
  ∀ j0 j1 j2 j3 →
  UnitFirstJetBound j0 → UnitFirstJetBound j1 →
  UnitFirstJetBound j2 → UnitFirstJetBound j3 →
  Norm.normSq (atom2 j0 j1 j2 j3) ≤ 1ℚ
atom2NormBelowOne j0 j1 j2 j3 b0 b1 b2 b3
  rewrite Norm.normSqMultiplyExact
      (Jet.factorValue j0)
      (Jet.factorValue j1 Jet.*q
        (Jet.factorFirst j2 Jet.*q
          Jet.orderedValueProduct (j3 ∷ [])))
        | Norm.normSqMultiplyExact
      (Jet.factorValue j1)
      (Jet.factorFirst j2 Jet.*q
        Jet.orderedValueProduct (j3 ∷ []))
        | Norm.normSqMultiplyExact
      (Jet.factorFirst j2)
      (Jet.orderedValueProduct (j3 ∷ []))
        | valueNormSqIsOne b0
        | valueNormSqIsOne b1
        | orderedValueNormOne1 j3 b3 =
  firstNormSqBelowOne b2

atom3NormBelowOne :
  ∀ j0 j1 j2 j3 →
  UnitFirstJetBound j0 → UnitFirstJetBound j1 →
  UnitFirstJetBound j2 → UnitFirstJetBound j3 →
  Norm.normSq (atom3 j0 j1 j2 j3) ≤ 1ℚ
atom3NormBelowOne j0 j1 j2 j3 b0 b1 b2 b3
  rewrite Norm.normSqMultiplyExact
      (Jet.factorValue j0)
      (Jet.factorValue j1 Jet.*q
        (Jet.factorValue j2 Jet.*q
          (Jet.factorFirst j3 Jet.*q Jet.oneQ)))
        | Norm.normSqMultiplyExact
      (Jet.factorValue j1)
      (Jet.factorValue j2 Jet.*q
        (Jet.factorFirst j3 Jet.*q Jet.oneQ))
        | Norm.normSqMultiplyExact
      (Jet.factorValue j2)
      (Jet.factorFirst j3 Jet.*q Jet.oneQ)
        | Norm.normSqMultiplyExact (Jet.factorFirst j3) Jet.oneQ
        | valueNormSqIsOne b0
        | valueNormSqIsOne b1
        | valueNormSqIsOne b2 =
  firstNormSqBelowOne b3

squareBelowOneImpliesAbsoluteBelowOne :
  ∀ value →
  value * value ≤ 1ℚ →
  ∣ value ∣ ≤ 1ℚ
squareBelowOneImpliesAbsoluteBelowOne value squareBound
  with ℚP.≤-total ∣ value ∣ 1ℚ
... | inj₁ already = already
... | inj₂ oneBelow =
  let
    absoluteSquareBound : ∣ value ∣ * ∣ value ∣ ≤ 1ℚ * 1ℚ
    absoluteSquareBound =
      subst
        (λ lower → lower ≤ 1ℚ * 1ℚ)
        (sym (Schur.absoluteSquareExact value))
        (subst
          (λ upper → value * value ≤ upper)
          (ℚRing.solve [])
          squareBound)
    absolutePositive : 0ℚ < ∣ value ∣
    absolutePositive = ℚP.<-≤-trans (ℚP.positive⁻¹ 1ℚ) oneBelow
    instance
      absPositive : Positive ∣ value ∣
      absPositive = positive absolutePositive
    oneNonnegative : 0ℚ ≤ 1ℚ
    oneNonnegative = ℚP.nonNegative⁻¹ 1ℚ

    instance
      oneNN : NonNegative 1ℚ
      oneNN = nonNegative oneNonnegative

    lowerProduct : 1ℚ * 1ℚ ≤ 1ℚ * ∣ value ∣
    lowerProduct = ℚP.*-monoˡ-≤-nonNeg 1ℚ oneBelow

    mixed : ∣ value ∣ * ∣ value ∣ ≤ ∣ value ∣ * 1ℚ
    mixed =
      ℚP.≤-trans absoluteSquareBound
        (subst
          (λ upper → 1ℚ * 1ℚ ≤ upper)
          (ℚP.*-comm 1ℚ ∣ value ∣)
          lowerProduct)
  in
  ℚP.*-cancelˡ-≤-pos ∣ value ∣ mixed

atomScalarAbsoluteBelowOne :
  ∀ atom →
  Norm.normSq atom ≤ 1ℚ →
  ∣ First.wilsonAtomContribution atom ∣ ≤ 1ℚ
atomScalarAbsoluteBelowOne atom normBound =
  squareBelowOneImpliesAbsoluteBelowOne
    (First.wilsonAtomContribution atom)
    (subst
      (λ left → left ≤ 1ℚ)
      (ℚRing.solve-∀ (Jet.q0 atom))
      (ℚP.≤-trans
        (Norm.scalarPartSquareBelowNormSq atom)
        normBound))

fourAtomScalarSumAbsoluteBelowFour :
  ∀ a0 a1 a2 a3 →
  ∣ a0 ∣ ≤ 1ℚ → ∣ a1 ∣ ≤ 1ℚ →
  ∣ a2 ∣ ≤ 1ℚ → ∣ a3 ∣ ≤ 1ℚ →
  ∣ a0 + (a1 + (a2 + a3)) ∣ ≤ (+ 4 / 1)
fourAtomScalarSumAbsoluteBelowFour a0 a1 a2 a3 b0 b1 b2 b3 =
  let
    triangle0 =
      ℚP.∣p+q∣≤∣p∣+∣q∣ a0 (a1 + (a2 + a3))
    triangle1 =
      ℚP.∣p+q∣≤∣p∣+∣q∣ a1 (a2 + a3)
    triangle2 =
      ℚP.∣p+q∣≤∣p∣+∣q∣ a2 a3
    inner :
      ∣ a2 + a3 ∣ ≤ 1ℚ + 1ℚ
    inner = ℚP.≤-trans triangle2 (ℚP.+-mono-≤ b2 b3)
    middle :
      ∣ a1 + (a2 + a3) ∣ ≤ 1ℚ + (1ℚ + 1ℚ)
    middle =
      ℚP.≤-trans triangle1
        (ℚP.+-mono-≤ b1 inner)
    raw :
      ∣ a0 + (a1 + (a2 + a3)) ∣
      ≤ 1ℚ + (1ℚ + (1ℚ + 1ℚ))
    raw =
      ℚP.≤-trans triangle0
        (ℚP.+-mono-≤ b0 middle)
  in
  subst
    (λ upper →
      ∣ a0 + (a1 + (a2 + a3)) ∣ ≤ upper)
    (ℚRing.solve [])
    raw

fourUnitJetWilsonFirstVariationAbsoluteBelowFour :
  ∀ j0 j1 j2 j3 →
  UnitFirstJetBound j0 → UnitFirstJetBound j1 →
  UnitFirstJetBound j2 → UnitFirstJetBound j3 →
  ∣ First.wilsonFirstVariationNumerator
      (Jet.fourFactorJets j0 j1 j2 j3) ∣
  ≤ (+ 4 / 1)
fourUnitJetWilsonFirstVariationAbsoluteBelowFour
    j0 j1 j2 j3 b0 b1 b2 b3 =
  let
    t0 = atom0 j0 j1 j2 j3
    t1 = atom1 j0 j1 j2 j3
    t2 = atom2 j0 j1 j2 j3
    t3 = atom3 j0 j1 j2 j3

    atomSumExact :
      First.wilsonFirstVariationAtomSum
        (Jet.fourFactorJets j0 j1 j2 j3)
      ≡ First.wilsonAtomContribution t0
        + (First.wilsonAtomContribution t1
        + (First.wilsonAtomContribution t2
        + First.wilsonAtomContribution t3))
    atomSumExact
      rewrite firstVariationTermsFour j0 j1 j2 j3 = refl
  in
  subst
    (λ value → ∣ value ∣ ≤ (+ 4 / 1))
    (sym
      (trans
        (First.fourLinkWilsonFirstVariationIsFourScalarAtoms
          j0 j1 j2 j3)
        atomSumExact))
    (fourAtomScalarSumAbsoluteBelowFour
      (First.wilsonAtomContribution t0)
      (First.wilsonAtomContribution t1)
      (First.wilsonAtomContribution t2)
      (First.wilsonAtomContribution t3)
      (atomScalarAbsoluteBelowOne t0
        (atom0NormBelowOne j0 j1 j2 j3 b0 b1 b2 b3))
      (atomScalarAbsoluteBelowOne t1
        (atom1NormBelowOne j0 j1 j2 j3 b0 b1 b2 b3))
      (atomScalarAbsoluteBelowOne t2
        (atom2NormBelowOne j0 j1 j2 j3 b0 b1 b2 b3))
      (atomScalarAbsoluteBelowOne t3
        (atom3NormBelowOne j0 j1 j2 j3 b0 b1 b2 b3)))

fourUnitJetFirstVariationBoundLevel : ProofLevel
fourUnitJetFirstVariationBoundLevel = machineChecked
