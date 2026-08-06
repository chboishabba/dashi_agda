module DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- DASHI CONTRIBUTION
--
-- Compute the finite-coordinate second variation of a squared residual rather
-- than accepting the gauge and block-constraint Hessians as unrelated
-- operators.  For a second jet
--
--   F(t) = F0 + t F1 + t^2 F2 / 2,
--
-- direct polynomial expansion gives
--
--   d^2/dt^2 [ ||F(t)||^2 / 2 ] at 0
--     = ||F1||^2 + <F0,F2>.
--
-- Pointwise exact gauge fixing F0=0 and exact block constraint C0=0 therefore
-- remove the residual/second-derivative terms and leave the positive squares
--
--   ||DF[h]||^2 + ||DQ[h]||^2.
--
-- The module composes these exact finite formulas with the existing literal
-- sixteen-atom Wilson plaquette second variation.  What remains physical is
-- identification of the selected background jets and the five quantitative
-- remainder bounds, not Hessian additivity or the squared-residual chain rule.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (map)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33QuaternionProductSecondVariationExact as Product
import DASHI.Physics.YangMills.BalabanP33WilsonPlaquetteScalarSecondVariationExact as Wilson

sumRational : List ℚ → ℚ
sumRational [] = 0ℚ
sumRational (value ∷ values) = value + sumRational values

sumRationalCong :
  ∀ {A : Set} (left right : A → ℚ) values →
  (∀ value → left value ≡ right value) →
  sumRational (map left values) ≡ sumRational (map right values)
sumRationalCong left right [] pointwise = refl
sumRationalCong left right (value ∷ values) pointwise =
  cong₂ _+_ (pointwise value)
    (sumRationalCong left right values pointwise)

record ScalarSecondJet : Set where
  constructor scalarJet
  field
    jetValue jetFirst jetSecond : ℚ

open ScalarSecondJet public

secondJetCurve : ScalarSecondJet → ℚ → ℚ
secondJetCurve jet time =
  jetValue jet
  + (time * jetFirst jet
    + ((+ 1 / 2) * time * time) * jetSecond jet)

halfSquaredCurve : ScalarSecondJet → ℚ → ℚ
halfSquaredCurve jet time =
  (+ 1 / 2) * secondJetCurve jet time * secondJetCurve jet time

secondVariationContribution : ScalarSecondJet → ℚ
secondVariationContribution jet =
  jetFirst jet * jetFirst jet
  + jetValue jet * jetSecond jet

------------------------------------------------------------------------
-- Exact coefficient calculation.  The left side is the coefficient of t^2 in
-- the expanded half square; multiplying it by two gives the second variation.
------------------------------------------------------------------------

halfSquareQuadraticCoefficient : ScalarSecondJet → ℚ
halfSquareQuadraticCoefficient jet =
  (+ 1 / 2)
    * (jetFirst jet * jetFirst jet
      + jetValue jet * jetSecond jet)

secondVariationIsTwiceQuadraticCoefficient : ∀ jet →
  secondVariationContribution jet
  ≡ (+ 2 / 1) * halfSquareQuadraticCoefficient jet
secondVariationIsTwiceQuadraticCoefficient (scalarJet value first second) =
  ℚRing.solve-∀ value first second

halfSquareExpansionExact : ∀ jet time →
  halfSquaredCurve jet time
  ≡ (+ 1 / 2) * jetValue jet * jetValue jet
    + (time * (jetValue jet * jetFirst jet)
      + (time * time * halfSquareQuadraticCoefficient jet
        + (time * time * time
          * ((+ 1 / 2) * jetFirst jet * jetSecond jet)
          + (time * time * time * time
            * ((+ 1 / 8) * jetSecond jet * jetSecond jet)))))
halfSquareExpansionExact (scalarJet value first second) time =
  ℚRing.solve-∀ value first second time

record FiniteResidualSecondJet (Index : Set) : Set₁ where
  field
    coordinates : List Index
    componentJet : Index → ScalarSecondJet

open FiniteResidualSecondJet public

residualSecondVariation :
  ∀ {Index} → FiniteResidualSecondJet Index → ℚ
residualSecondVariation residual =
  sumRational
    (map
      (λ index → secondVariationContribution (componentJet residual index))
      (coordinates residual))

residualFirstNormSquared :
  ∀ {Index} → FiniteResidualSecondJet Index → ℚ
residualFirstNormSquared residual =
  sumRational
    (map
      (λ index →
        jetFirst (componentJet residual index)
        * jetFirst (componentJet residual index))
      (coordinates residual))

residualPairingWithSecond :
  ∀ {Index} → FiniteResidualSecondJet Index → ℚ
residualPairingWithSecond residual =
  sumRational
    (map
      (λ index →
        jetValue (componentJet residual index)
        * jetSecond (componentJet residual index))
      (coordinates residual))

residualSecondVariationSplitExact :
  ∀ {Index} (residual : FiniteResidualSecondJet Index) →
  residualSecondVariation residual
  ≡ residualFirstNormSquared residual
    + residualPairingWithSecond residual
residualSecondVariationSplitExact residual =
  let
    distribute : ∀ values →
      sumRational
        (map
          (λ index →
            jetFirst (componentJet residual index)
              * jetFirst (componentJet residual index)
            + jetValue (componentJet residual index)
              * jetSecond (componentJet residual index))
          values)
      ≡ sumRational
          (map
            (λ index →
              jetFirst (componentJet residual index)
                * jetFirst (componentJet residual index))
            values)
        + sumRational
          (map
            (λ index →
              jetValue (componentJet residual index)
                * jetSecond (componentJet residual index))
            values)
    distribute [] = ℚRing.solve []
    distribute (index ∷ indices) =
      trans
        (cong
          (λ tail →
            (jetFirst (componentJet residual index)
              * jetFirst (componentJet residual index)
            + jetValue (componentJet residual index)
              * jetSecond (componentJet residual index)) + tail)
          (distribute indices))
        (ℚRing.solve-∀
          (jetFirst (componentJet residual index)
            * jetFirst (componentJet residual index))
          (jetValue (componentJet residual index)
            * jetSecond (componentJet residual index))
          (sumRational
            (map
              (λ later →
                jetFirst (componentJet residual later)
                  * jetFirst (componentJet residual later))
              indices))
          (sumRational
            (map
              (λ later →
                jetValue (componentJet residual later)
                  * jetSecond (componentJet residual later))
              indices)))
  in distribute (coordinates residual)

record ExactResidualBackground {Index : Set}
    (residual : FiniteResidualSecondJet Index) : Set₁ where
  field
    residualZero : ∀ index →
      jetValue (componentJet residual index) ≡ 0ℚ

open ExactResidualBackground public

residualPairingVanishesAtExactBackground :
  ∀ {Index} (residual : FiniteResidualSecondJet Index) →
  ExactResidualBackground residual →
  residualPairingWithSecond residual ≡ 0ℚ
residualPairingVanishesAtExactBackground residual exact =
  let
    vanish : ∀ values →
      sumRational
        (map
          (λ index →
            jetValue (componentJet residual index)
            * jetSecond (componentJet residual index))
          values)
      ≡ 0ℚ
    vanish [] = refl
    vanish (index ∷ indices) =
      trans
        (cong₂ _+_
          (cong
            (λ value → value * jetSecond (componentJet residual index))
            (residualZero exact index))
          (vanish indices))
        (ℚRing.solve [])
  in vanish (coordinates residual)

residualSecondVariationAtExactBackground :
  ∀ {Index} (residual : FiniteResidualSecondJet Index) →
  ExactResidualBackground residual →
  residualSecondVariation residual
  ≡ residualFirstNormSquared residual
residualSecondVariationAtExactBackground residual exact =
  trans
    (residualSecondVariationSplitExact residual)
    (trans
      (cong
        (λ remainder → residualFirstNormSquared residual + remainder)
        (residualPairingVanishesAtExactBackground residual exact))
      (ℚRing.solve-∀ (residualFirstNormSquared residual)))

------------------------------------------------------------------------
-- Literal Wilson + gauge-fixing + block-constraint second variation.
------------------------------------------------------------------------

record PlaquetteSecondJet : Set where
  constructor plaquetteJet
  field
    link0 link1 link2 link3 : Product.QuaternionFactorJet

open PlaquetteSecondJet public

plaquetteWilsonSecondVariation : PlaquetteSecondJet → ℚ
plaquetteWilsonSecondVariation plaquette =
  Wilson.wilsonSecondVariationNumerator
    (Product.fourFactorJets
      (link0 plaquette) (link1 plaquette)
      (link2 plaquette) (link3 plaquette))

record LiteralPhysicalSecondVariation
    (Plaquette GaugeIndex ConstraintIndex : Set) : Set₁ where
  field
    plaquettes : List Plaquette
    plaquetteJetData : Plaquette → PlaquetteSecondJet
    gaugeResidual : FiniteResidualSecondJet GaugeIndex
    constraintResidual : FiniteResidualSecondJet ConstraintIndex

open LiteralPhysicalSecondVariation public

wilsonSecondVariation :
  ∀ {Plaquette GaugeIndex ConstraintIndex} →
  LiteralPhysicalSecondVariation Plaquette GaugeIndex ConstraintIndex → ℚ
wilsonSecondVariation dataSet =
  sumRational
    (map
      (λ plaquette →
        plaquetteWilsonSecondVariation (plaquetteJetData dataSet plaquette))
      (plaquettes dataSet))

literalTotalSecondVariation :
  ∀ {Plaquette GaugeIndex ConstraintIndex} →
  LiteralPhysicalSecondVariation Plaquette GaugeIndex ConstraintIndex → ℚ
literalTotalSecondVariation dataSet =
  wilsonSecondVariation dataSet
  + (residualSecondVariation (gaugeResidual dataSet)
    + residualSecondVariation (constraintResidual dataSet))

literalTotalSecondVariationSplitExact :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (dataSet : LiteralPhysicalSecondVariation
      Plaquette GaugeIndex ConstraintIndex) →
  literalTotalSecondVariation dataSet
  ≡ wilsonSecondVariation dataSet
    + (residualFirstNormSquared (gaugeResidual dataSet)
      + residualPairingWithSecond (gaugeResidual dataSet)
      + (residualFirstNormSquared (constraintResidual dataSet)
        + residualPairingWithSecond (constraintResidual dataSet)))
literalTotalSecondVariationSplitExact dataSet =
  trans
    (cong₂ _+_ refl
      (cong₂ _+_
        (residualSecondVariationSplitExact (gaugeResidual dataSet))
        (residualSecondVariationSplitExact (constraintResidual dataSet))))
    (ℚRing.solve-∀
      (wilsonSecondVariation dataSet)
      (residualFirstNormSquared (gaugeResidual dataSet))
      (residualPairingWithSecond (gaugeResidual dataSet))
      (residualFirstNormSquared (constraintResidual dataSet))
      (residualPairingWithSecond (constraintResidual dataSet)))

literalTotalSecondVariationAtExactBackground :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (dataSet : LiteralPhysicalSecondVariation
      Plaquette GaugeIndex ConstraintIndex) →
  ExactResidualBackground (gaugeResidual dataSet) →
  ExactResidualBackground (constraintResidual dataSet) →
  literalTotalSecondVariation dataSet
  ≡ wilsonSecondVariation dataSet
    + (residualFirstNormSquared (gaugeResidual dataSet)
      + residualFirstNormSquared (constraintResidual dataSet))
literalTotalSecondVariationAtExactBackground
    dataSet gaugeExact constraintExact =
  trans
    (cong₂ _+_ refl
      (cong₂ _+_
        (residualSecondVariationAtExactBackground
          (gaugeResidual dataSet) gaugeExact)
        (residualSecondVariationAtExactBackground
          (constraintResidual dataSet) constraintExact)))
    refl

literalSquaredResidualSecondVariationLevel : ProofLevel
literalSquaredResidualSecondVariationLevel = machineChecked

literalGaugeConstraintBackgroundCollapseLevel : ProofLevel
literalGaugeConstraintBackgroundCollapseLevel = machineChecked

literalWilsonGaugeConstraintHessianAssemblyLevel : ProofLevel
literalWilsonGaugeConstraintHessianAssemblyLevel = machineChecked

physicalBackgroundJetIdentificationLevel : ProofLevel
physicalBackgroundJetIdentificationLevel = conditional
