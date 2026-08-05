module DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintCancellationExact where

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
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- The literal exact-background gauge-fixing and CMP109 constraint Hessians are
-- the positive first-derivative squares
--
--   ||D F[h]||^2,  ||D Q[h]||^2.
--
-- The reference Hodge form already accepts arbitrary nonnegative gauge and
-- block-penalty energies.  Selecting those two literal squares as the reference
-- penalties makes them cancel exactly in the signed Hessian remainder:
--
--   [H_W + ||DF||^2 + ||DQ||^2]
--     - [H_diff + ||DF||^2 + ||DQ||^2]
--   = H_W - H_diff.
--
-- Consequently the physical 1/32 coercivity producer no longer needs five
-- independently bounded remainder channels.  At an exact gauge/constraint
-- background it suffices to prove the one signed Wilson comparison
--
--   -(1/32)||h||^2 <= H_W''[h,h] - H_diff[h,h].
--
-- This is an exact cancellation theorem, not an estimate and not a change of
-- normalization.  It materially reduces the remaining coercivity cut while
-- preserving the literal Wilson, gauge-fixing and CMP109 second variations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map)
open import Data.Rational using
  (ℚ; 0ℚ; _+_; _*_; -_; _-_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact as Hodge
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33

------------------------------------------------------------------------
-- Literal positive residual energies.
------------------------------------------------------------------------

gaugeFirstEnergy :
  ∀ {Plaquette GaugeIndex ConstraintIndex} →
  Jets.LiteralPhysicalSecondVariation
    Plaquette GaugeIndex ConstraintIndex → ℚ
gaugeFirstEnergy data =
  Jets.residualFirstNormSquared (Jets.gaugeResidual data)

constraintFirstEnergy :
  ∀ {Plaquette GaugeIndex ConstraintIndex} →
  Jets.LiteralPhysicalSecondVariation
    Plaquette GaugeIndex ConstraintIndex → ℚ
constraintFirstEnergy data =
  Jets.residualFirstNormSquared (Jets.constraintResidual data)

residualFirstNormSquaredNonnegative :
  ∀ {Index} (residual : Jets.FiniteResidualSecondJet Index) →
  0ℚ ≤ Jets.residualFirstNormSquared residual
residualFirstNormSquaredNonnegative residual =
  sumSquaresNonnegative (Jets.coordinates residual)
  where
  sumSquaresNonnegative : ∀ indices →
    0ℚ ≤ Jets.sumRational
      (map
        (λ index →
          Jets.jetFirst (Jets.componentJet residual index)
          * Jets.jetFirst (Jets.componentJet residual index))
        indices)
  sumSquaresNonnegative [] = ℚP.≤-refl
  sumSquaresNonnegative (index ∷ indices) =
    let
      squareNonnegative :
        0ℚ ≤ Jets.jetFirst (Jets.componentJet residual index)
          * Jets.jetFirst (Jets.componentJet residual index)
      squareNonnegative =
        FiniteL2.squareNonnegative
          (Jets.jetFirst (Jets.componentJet residual index))

      tailNonnegative = sumSquaresNonnegative indices
    in
    subst
      (λ lower →
        lower ≤
          Jets.jetFirst (Jets.componentJet residual index)
            * Jets.jetFirst (Jets.componentJet residual index)
          + Jets.sumRational
              (map
                (λ later →
                  Jets.jetFirst (Jets.componentJet residual later)
                    * Jets.jetFirst (Jets.componentJet residual later))
                indices))
      (sym (ℚP.+-identityˡ 0ℚ))
      (ℚP.+-mono-≤ squareNonnegative tailNonnegative)

gaugeFirstEnergyNonnegative :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (data : Jets.LiteralPhysicalSecondVariation
      Plaquette GaugeIndex ConstraintIndex) →
  0ℚ ≤ gaugeFirstEnergy data
gaugeFirstEnergyNonnegative data =
  residualFirstNormSquaredNonnegative (Jets.gaugeResidual data)

constraintFirstEnergyNonnegative :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (data : Jets.LiteralPhysicalSecondVariation
      Plaquette GaugeIndex ConstraintIndex) →
  0ℚ ≤ constraintFirstEnergy data
constraintFirstEnergyNonnegative data =
  residualFirstNormSquaredNonnegative (Jets.constraintResidual data)

------------------------------------------------------------------------
-- Matched reference form and exact cancellation.
------------------------------------------------------------------------

matchedReferenceEnergy :
  ∀ {Plaquette GaugeIndex ConstraintIndex} →
  Hodge.RationalBondField4 →
  Jets.LiteralPhysicalSecondVariation
    Plaquette GaugeIndex ConstraintIndex → ℚ
matchedReferenceEnergy field data =
  Hodge.referenceHodgeEnergy
    field (gaugeFirstEnergy data) (constraintFirstEnergy data)

matchedExactHessian :
  ∀ {Plaquette GaugeIndex ConstraintIndex} →
  Jets.LiteralPhysicalSecondVariation
    Plaquette GaugeIndex ConstraintIndex → ℚ
matchedExactHessian data =
  Jets.wilsonSecondVariation data
  + (gaugeFirstEnergy data + constraintFirstEnergy data)

matchedSignedRemainder :
  ∀ {Plaquette GaugeIndex ConstraintIndex} →
  Hodge.RationalBondField4 →
  Jets.LiteralPhysicalSecondVariation
    Plaquette GaugeIndex ConstraintIndex → ℚ
matchedSignedRemainder field data =
  matchedExactHessian data - matchedReferenceEnergy field data

matchedGaugeConstraintCancellationExact :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (field : Hodge.RationalBondField4)
    (data : Jets.LiteralPhysicalSecondVariation
      Plaquette GaugeIndex ConstraintIndex) →
  matchedSignedRemainder field data
  ≡ Jets.wilsonSecondVariation data
      - Hodge.bondReferenceDifferenceEnergy field
matchedGaugeConstraintCancellationExact field data =
  ℚRing.solve-∀
    (Jets.wilsonSecondVariation data)
    (Hodge.bondReferenceDifferenceEnergy field)
    (gaugeFirstEnergy data)
    (constraintFirstEnergy data)

matchedReferenceRecomposesExactHessian :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (field : Hodge.RationalBondField4)
    (data : Jets.LiteralPhysicalSecondVariation
      Plaquette GaugeIndex ConstraintIndex) →
  P33.physicalHessianEnergy
    (matchedReferenceEnergy field data)
    (matchedSignedRemainder field data)
  ≡ matchedExactHessian data
matchedReferenceRecomposesExactHessian field data =
  ℚRing.solve-∀
    (matchedReferenceEnergy field data)
    (matchedExactHessian data)

literalTotalEqualsMatchedExactHessian :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (data : Jets.LiteralPhysicalSecondVariation
      Plaquette GaugeIndex ConstraintIndex) →
  Jets.ExactResidualBackground (Jets.gaugeResidual data) →
  Jets.ExactResidualBackground (Jets.constraintResidual data) →
  Jets.literalTotalSecondVariation data ≡ matchedExactHessian data
literalTotalEqualsMatchedExactHessian data gaugeExact constraintExact =
  Jets.literalTotalSecondVariationAtExactBackground
    data gaugeExact constraintExact

------------------------------------------------------------------------
-- Coercivity now depends only on the Wilson-minus-difference remainder.
------------------------------------------------------------------------

literalHessianCoerciveFromWilsonDifference :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (field : Hodge.RationalBondField4)
    (data : Jets.LiteralPhysicalSecondVariation
      Plaquette GaugeIndex ConstraintIndex) →
  Hodge.BondComponentMeanZero field →
  Jets.ExactResidualBackground (Jets.gaugeResidual data) →
  Jets.ExactResidualBackground (Jets.constraintResidual data) →
  - (P33.p33PhysicalFloor * Hodge.bondNormSq field)
    ≤ Jets.wilsonSecondVariation data
        - Hodge.bondReferenceDifferenceEnergy field →
  P33.p33PhysicalFloor * Hodge.bondNormSq field
    ≤ Jets.literalTotalSecondVariation data
literalHessianCoerciveFromWilsonDifference
    field data meanZero gaugeExact constraintExact wilsonDifferenceLower =
  let
    matchedLower :
      - (P33.p33PhysicalFloor * Hodge.bondNormSq field)
      ≤ matchedSignedRemainder field data
    matchedLower =
      subst
        (λ remainder →
          - (P33.p33PhysicalFloor * Hodge.bondNormSq field)
          ≤ remainder)
        (sym (matchedGaugeConstraintCancellationExact field data))
        wilsonDifferenceLower

    referenceCoercive :
      P33.p33PhysicalFloor * Hodge.bondNormSq field
      ≤ P33.physicalHessianEnergy
          (matchedReferenceEnergy field data)
          (matchedSignedRemainder field data)
    referenceCoercive =
      P33.path4SignedRemainderCoercive
        field
        (gaugeFirstEnergy data)
        (constraintFirstEnergy data)
        (matchedSignedRemainder field data)
        meanZero
        (gaugeFirstEnergyNonnegative data)
        (constraintFirstEnergyNonnegative data)
        matchedLower

    matchedCoercive :
      P33.p33PhysicalFloor * Hodge.bondNormSq field
      ≤ matchedExactHessian data
    matchedCoercive =
      subst
        (λ upper →
          P33.p33PhysicalFloor * Hodge.bondNormSq field ≤ upper)
        (matchedReferenceRecomposesExactHessian field data)
        referenceCoercive
  in
  subst
    (λ upper →
      P33.p33PhysicalFloor * Hodge.bondNormSq field ≤ upper)
    (sym (literalTotalEqualsMatchedExactHessian
      data gaugeExact constraintExact))
    matchedCoercive

literalGaugeConstraintCancellationLevel : ProofLevel
literalGaugeConstraintCancellationLevel = machineChecked

literalWilsonOnlyRemainderLevel : ProofLevel
literalWilsonOnlyRemainderLevel = machineChecked

literalWilsonDifferenceCoercivityLevel : ProofLevel
literalWilsonDifferenceCoercivityLevel = machineChecked
