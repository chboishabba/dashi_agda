module DASHI.Physics.YangMills.BalabanPath13PreconditionedAverageGaugeOrthogonalityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- DASHI CONTRIBUTION
--
-- Close the source-scale flat cross term.  The preconditioned normalized
-- block-average adjoint is constant in the site coordinate for each Lie
-- component and positive bond direction.  The literal L=13 flat gauge adjoint
-- is the negative periodic gradient.  On each 13-cycle the sum of a forward
-- difference telescopes exactly to zero.  Hence
--
--   < (169 Q)^* alpha , L_g,0^* gamma > = 0
--
-- on the actual 342732-coordinate state carrier.
--
-- This is not inferred from a side-four integration-by-parts theorem; the
-- 13-cycle is expanded directly on the source-faithful carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; trans; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact
open import DASHI.Physics.YangMills.BalabanPhysicalAxisPartitionExact
import DASHI.Physics.YangMills.BalabanPath13PhysicalFibreMatchExact as Match
import DASHI.Physics.YangMills.BalabanPath13NormalizedAxisAverageExact as Side13
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanClayGate4CMP109MinimalAdmissibleRepositoryScaleExact as Minimal
import DASHI.Physics.YangMills.BalabanCMP109L13BlockAverageAdjointFloorExact as Average
import DASHI.Physics.YangMills.BalabanCMP109L13ConstraintRowPreconditionerExact as Precondition
import DASHI.Physics.YangMills.BalabanPath13FlatGaugeAdjointMatrixExact as Flat

shiftForwardInsertAxis13 :
  ∀ axis coordinate transverse →
  Flat.shiftForward13 axis (insertAxis axis coordinate transverse)
  ≡ insertAxis axis (Flat.cyclicNext coordinate) transverse
shiftForwardInsertAxis13 zeroᵢ coordinate (pair x1 (pair x2 x3)) = refl
shiftForwardInsertAxis13 (sucᵢ zeroᵢ) coordinate
    (pair x0 (pair x2 x3)) = refl
shiftForwardInsertAxis13 (sucᵢ (sucᵢ zeroᵢ)) coordinate
    (pair x0 (pair x1 x3)) = refl
shiftForwardInsertAxis13 (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) coordinate
    (pair x0 (pair x1 x2)) = refl

periodicForwardDifferenceFibreSum13 :
  ∀ field axis transverse →
  sumRational (allCyclicIndices Side13.side13)
    (λ coordinate →
      field (insertAxis axis (Flat.cyclicNext coordinate) transverse)
      - field (insertAxis axis coordinate transverse))
  ≡ 0ℚ
periodicForwardDifferenceFibreSum13 field axis transverse =
  ℚRing.solve-∀
    (field (insertAxis axis Match.index0 transverse))
    (field (insertAxis axis Match.index1 transverse))
    (field (insertAxis axis Match.index2 transverse))
    (field (insertAxis axis Match.index3 transverse))
    (field (insertAxis axis Match.index4 transverse))
    (field (insertAxis axis Match.index5 transverse))
    (field (insertAxis axis Match.index6 transverse))
    (field (insertAxis axis Match.index7 transverse))
    (field (insertAxis axis Match.index8 transverse))
    (field (insertAxis axis Match.index9 transverse))
    (field (insertAxis axis Match.index10 transverse))
    (field (insertAxis axis Match.index11 transverse))
    (field (insertAxis axis Match.index12 transverse))

periodicForwardDifferenceGlobalSum13 :
  ∀ field axis →
  globalSiteSum (λ site → Flat.forwardDifference13 axis field site)
  ≡ 0ℚ
periodicForwardDifferenceGlobalSum13 field axis =
  trans
    (sym
      (axisPartitionSumMatchesGlobal axis
        (λ site → Flat.forwardDifference13 axis field site)))
    (trans
      (sumRationalCong
        (physicalTransverseCoordinates Side13.side13)
        (λ transverse →
          sumRational (allCyclicIndices Side13.side13)
            (λ coordinate →
              Flat.forwardDifference13 axis field
                (insertAxis axis coordinate transverse)))
        (λ transverse → 0ℚ)
        (λ transverse →
          trans
            (sumRationalCong
              (allCyclicIndices Side13.side13) _ _
              (λ coordinate →
                cong
                  (λ target →
                    field target
                    - field (insertAxis axis coordinate transverse))
                  (shiftForwardInsertAxis13 axis coordinate transverse)))
            (periodicForwardDifferenceFibreSum13 field axis transverse)))
      (zeroSum (physicalTransverseCoordinates Side13.side13)))
  where
  zeroSum : ∀ {A : Set} (values : Agda.Builtin.List.List A) →
    sumRational values (λ _ → 0ℚ) ≡ 0ℚ
  zeroSum Agda.Builtin.List.[] = refl
  zeroSum (Agda.Builtin.List._∷_ value values)
    rewrite zeroSum values = refl

constantTimesPeriodicDifferenceSumZero13 :
  ∀ coefficient field axis →
  globalSiteSum
    (λ site → coefficient * (- Flat.forwardDifference13 axis field site))
  ≡ 0ℚ
constantTimesPeriodicDifferenceSumZero13 coefficient field axis =
  trans
    (sumRationalScale coefficient
      (physicalBlockSites Side13.side13)
      (λ site → - Flat.forwardDifference13 axis field site))
    (trans
      (cong (coefficient *_)
        (sumRationalNegate
          (physicalBlockSites Side13.side13)
          (λ site → Flat.forwardDifference13 axis field site)))
      (trans
        (cong (λ value → coefficient * (- value))
          (periodicForwardDifferenceGlobalSum13 field axis))
        (ℚRing.solve-∀ coefficient)))

preconditionedAverageGaugeInner :
  Average.RowVector → Flat.GaugeMultiplier13 → ℚ
preconditionedAverageGaugeInner alpha gamma =
  Physical.physicalCoordinateDot
    (Precondition.preconditionedBlockAverageAdjoint alpha)
    (Flat.flatGaugeAdjoint13 gamma)

preconditionedAverageGaugeInnerExactZero :
  ∀ alpha gamma →
  preconditionedAverageGaugeInner alpha gamma ≡ 0ℚ
preconditionedAverageGaugeInnerExactZero alpha gamma =
  trans
    (sumCartesian
      Physical.lieCoordinates3
      (Physical.physicalBondCells Side13.side13)
      (λ state →
        Precondition.preconditionedBlockAverageAdjoint alpha state
        * Flat.flatGaugeAdjoint13 gamma state))
    (trans
      (sumRationalCong
        Physical.lieCoordinates3 _ (λ _ → 0ℚ)
        (λ coordinate →
          trans
            (sumCartesian
              (allCyclicIndices four)
              (physicalBlockSites Side13.side13)
              (λ cell →
                Precondition.preconditionedBlockAverageAdjoint alpha
                  (pair coordinate cell)
                * Flat.flatGaugeAdjoint13 gamma
                  (pair coordinate cell)))
            (trans
              (sumRationalCong
                (allCyclicIndices four) _ (λ _ → 0ℚ)
                (λ axis →
                  let
                    coefficient =
                      Precondition.oneHundredSixtyNine
                      * Minimal.siteWeightℚ
                      * alpha (pair coordinate axis)
                  in
                  trans
                    (sumRationalCong
                      (physicalBlockSites Side13.side13) _ _
                      (λ site →
                        trans
                          (cong
                            (coefficient *_)
                            (Flat.flatGaugeAdjointPointwiseExact
                              gamma coordinate axis site))
                          (ℚRing.solve-∀
                            Precondition.oneHundredSixtyNine
                            Minimal.siteWeightℚ
                            (alpha (pair coordinate axis))
                            (Flat.forwardDifference13 axis
                              (Flat.multiplierField13 gamma coordinate) site))))
                    (constantTimesPeriodicDifferenceSumZero13
                      coefficient
                      (Flat.multiplierField13 gamma coordinate)
                      axis)))
              zeroAxes)))
      zeroCoordinates))
  where
  zeroAxes :
    sumRational (allCyclicIndices four) (λ _ → 0ℚ) ≡ 0ℚ
  zeroAxes = refl

  zeroCoordinates :
    sumRational Physical.lieCoordinates3 (λ _ → 0ℚ) ≡ 0ℚ
  zeroCoordinates = refl

path13PreconditionedAverageFlatGaugeOrthogonalityLevel : ProofLevel
path13PreconditionedAverageFlatGaugeOrthogonalityLevel = machineChecked
