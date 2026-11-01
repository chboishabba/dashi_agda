module DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Sum the literal plaquette W-local inequality over the repository's actual
-- 1,536 plaquettes.  The input is not an anonymous scalar remainder: it is the
-- pointwise lower bound on the actual background-minus-identity Wilson second
-- variation, with the actual four-slot diagonal charge q_p and twelve-pair
-- cross charge C_p.
--
-- Exact cartesian Fubini, periodic reindexing, and the checked incidence
-- identities
--
--   sum_p q_p = 6 ||h||^2,
--   sum_p C_p = 18 ||h||^2
--
-- yield exactly
--
--   H_W(A;h)-H_W(1;h) >= -(13/24) rho ||h||^2.
--
-- Thus after the local signed producer is supplied there is no remaining
-- combinatorial or coefficient socket between W-local and W-global.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; _+_; _-_; _*_; -_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanPhysicalAxisPartitionExact as Partition
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeSignedLowerExact as GaugeBudget
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonIncidenceExact as Incidence

sumRationalMonotone :
  ∀ {A : Set} (values : List A) (left right : A → ℚ) →
  (∀ value → left value ≤ right value) →
  Sums.sumRational values left ≤ Sums.sumRational values right
sumRationalMonotone [] left right pointwise = ℚP.≤-refl
sumRationalMonotone (value ∷ values) left right pointwise =
  ℚP.+-mono-≤
    (pointwise value)
    (sumRationalMonotone values left right pointwise)

sumRationalSubtract :
  ∀ {A : Set} (values : List A) (left right : A → ℚ) →
  Sums.sumRational values (λ value → left value - right value)
  ≡ Sums.sumRational values left - Sums.sumRational values right
sumRationalSubtract [] left right = ℚRing.solve []
sumRationalSubtract (value ∷ values) left right
  rewrite sumRationalSubtract values left right =
  ℚRing.solve-∀
    (left value) (right value)
    (Sums.sumRational values left)
    (Sums.sumRational values right)

sumRationalLinear2 :
  ∀ {A : Set} firstScale secondScale
    (values : List A) (first second : A → ℚ) →
  Sums.sumRational values
    (λ value → firstScale * first value + secondScale * second value)
  ≡ firstScale * Sums.sumRational values first
    + secondScale * Sums.sumRational values second
sumRationalLinear2 firstScale secondScale [] first second =
  ℚRing.solve-∀ firstScale secondScale
sumRationalLinear2 firstScale secondScale (value ∷ values) first second
  rewrite sumRationalLinear2
    firstScale secondScale values first second =
  ℚRing.solve-∀
    firstScale secondScale
    (first value) (second value)
    (Sums.sumRational values first)
    (Sums.sumRational values second)

plaquetteDiagonalCharge :
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 → ℚ
plaquetteDiagonalCharge fieldValue (pair site axes) =
  Incidence.plaquetteDiagonalCharge fieldValue
    (Physical.pairLeft axes) (Physical.pairRight axes) site

plaquetteCrossCharge :
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 → ℚ
plaquetteCrossCharge fieldValue (pair site axes) =
  Incidence.plaquetteCrossCharge fieldValue
    (Physical.pairLeft axes) (Physical.pairRight axes) site

pairDiagonalFromPlaquettes :
  Coordinates.PhysicalSU2BondField4 → Physical.AxisPair6 → ℚ
pairDiagonalFromPlaquettes fieldValue axes =
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ site → plaquetteDiagonalCharge fieldValue (pair site axes))

pairCrossFromPlaquettes :
  Coordinates.PhysicalSU2BondField4 → Physical.AxisPair6 → ℚ
pairCrossFromPlaquettes fieldValue axes =
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ site → plaquetteCrossCharge fieldValue (pair site axes))

pairDiagonalFromPlaquettesExact : ∀ fieldValue axes →
  pairDiagonalFromPlaquettes fieldValue axes
  ≡ Incidence.pairDiagonalIncidence fieldValue
      (Physical.pairLeft axes) (Physical.pairRight axes)
pairDiagonalFromPlaquettesExact fieldValue axes =
  trans
    (Partition.globalSiteSumMatchesCoordinateSum4
      (λ site →
        Incidence.plaquetteDiagonalCharge fieldValue
          (Physical.pairLeft axes) (Physical.pairRight axes) site))
    refl

pairCrossFromPlaquettesExact : ∀ fieldValue axes →
  pairCrossFromPlaquettes fieldValue axes
  ≡ Incidence.pairCrossIncidence fieldValue
      (Physical.pairLeft axes) (Physical.pairRight axes)
pairCrossFromPlaquettesExact fieldValue axes =
  trans
    (Partition.globalSiteSumMatchesCoordinateSum4
      (λ site →
        Incidence.plaquetteCrossCharge fieldValue
          (Physical.pairLeft axes) (Physical.pairRight axes) site))
    refl

plaquetteDiagonalGlobal :
  Coordinates.PhysicalSU2BondField4 → ℚ
plaquetteDiagonalGlobal fieldValue =
  Sums.sumRational Physical.plaquettes4
    (plaquetteDiagonalCharge fieldValue)

plaquetteCrossGlobal :
  Coordinates.PhysicalSU2BondField4 → ℚ
plaquetteCrossGlobal fieldValue =
  Sums.sumRational Physical.plaquettes4
    (plaquetteCrossCharge fieldValue)

plaquetteDiagonalGlobalIsIncidence : ∀ fieldValue →
  plaquetteDiagonalGlobal fieldValue
  ≡ Incidence.physicalWilsonDiagonalIncidence fieldValue
plaquetteDiagonalGlobalIsIncidence fieldValue =
  trans
    (Fubini.sumCartesian
      (Block.physicalBlockSites Path4.side4)
      Physical.axisPairs6
      (plaquetteDiagonalCharge fieldValue))
    (trans
      (Fubini.sumSwap
        (Block.physicalBlockSites Path4.side4)
        Physical.axisPairs6
        (λ site axes → plaquetteDiagonalCharge fieldValue (pair site axes)))
      (trans
        (Sums.sumRationalCong
          Physical.axisPairs6
          (pairDiagonalFromPlaquettes fieldValue)
          (λ axes →
            Incidence.pairDiagonalIncidence fieldValue
              (Physical.pairLeft axes) (Physical.pairRight axes))
          (pairDiagonalFromPlaquettesExact fieldValue))
        (ℚRing.solve-∀
          (Incidence.pairDiagonalIncidence fieldValue
            Periodic.axis0 Periodic.axis1)
          (Incidence.pairDiagonalIncidence fieldValue
            Periodic.axis0 Periodic.axis2)
          (Incidence.pairDiagonalIncidence fieldValue
            Periodic.axis0 Periodic.axis3)
          (Incidence.pairDiagonalIncidence fieldValue
            Periodic.axis1 Periodic.axis2)
          (Incidence.pairDiagonalIncidence fieldValue
            Periodic.axis1 Periodic.axis3)
          (Incidence.pairDiagonalIncidence fieldValue
            Periodic.axis2 Periodic.axis3))))

plaquetteCrossGlobalIsIncidence : ∀ fieldValue →
  plaquetteCrossGlobal fieldValue
  ≡ Incidence.physicalWilsonCrossIncidence fieldValue
plaquetteCrossGlobalIsIncidence fieldValue =
  trans
    (Fubini.sumCartesian
      (Block.physicalBlockSites Path4.side4)
      Physical.axisPairs6
      (plaquetteCrossCharge fieldValue))
    (trans
      (Fubini.sumSwap
        (Block.physicalBlockSites Path4.side4)
        Physical.axisPairs6
        (λ site axes → plaquetteCrossCharge fieldValue (pair site axes)))
      (trans
        (Sums.sumRationalCong
          Physical.axisPairs6
          (pairCrossFromPlaquettes fieldValue)
          (λ axes →
            Incidence.pairCrossIncidence fieldValue
              (Physical.pairLeft axes) (Physical.pairRight axes))
          (pairCrossFromPlaquettesExact fieldValue))
        (ℚRing.solve-∀
          (Incidence.pairCrossIncidence fieldValue
            Periodic.axis0 Periodic.axis1)
          (Incidence.pairCrossIncidence fieldValue
            Periodic.axis0 Periodic.axis2)
          (Incidence.pairCrossIncidence fieldValue
            Periodic.axis0 Periodic.axis3)
          (Incidence.pairCrossIncidence fieldValue
            Periodic.axis1 Periodic.axis2)
          (Incidence.pairCrossIncidence fieldValue
            Periodic.axis1 Periodic.axis3)
          (Incidence.pairCrossIncidence fieldValue
            Periodic.axis2 Periodic.axis3))))

rhoOverThirtySix rhoOverOneFortyFour : ℚ
rhoOverThirtySix = (+ 1 / 36) * GaugeBudget.rho
rhoOverOneFortyFour = (+ 1 / 144) * GaugeBudget.rho

plaquetteWilsonBudget :
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 → ℚ
plaquetteWilsonBudget fieldValue plaquette =
  rhoOverThirtySix * plaquetteCrossCharge fieldValue plaquette
  + rhoOverOneFortyFour * plaquetteDiagonalCharge fieldValue plaquette

record PhysicalWilsonSignedLocal
    (background : Physical.RationalSU2Background4)
    (fieldValue : Coordinates.PhysicalSU2BondField4) : Set where
  field
    plaquetteLower : ∀ plaquette →
      - plaquetteWilsonBudget fieldValue plaquette
      ≤ Physical.plaquetteWilsonSecondVariation
          background fieldValue plaquette
        - Physical.plaquetteWilsonSecondVariation
          Physical.identityBackground fieldValue plaquette

open PhysicalWilsonSignedLocal public

summedPlaquetteBudgetExact : ∀ fieldValue →
  Sums.sumRational Physical.plaquettes4
    (λ plaquette → - plaquetteWilsonBudget fieldValue plaquette)
  ≡ - (rhoOverThirtySix * plaquetteCrossGlobal fieldValue
      + rhoOverOneFortyFour * plaquetteDiagonalGlobal fieldValue)
summedPlaquetteBudgetExact fieldValue =
  trans
    (Sums.sumRationalNegate
      Physical.plaquettes4 (plaquetteWilsonBudget fieldValue))
    (cong -_
      (sumRationalLinear2
        rhoOverThirtySix rhoOverOneFortyFour
        Physical.plaquettes4
        (plaquetteCrossCharge fieldValue)
        (plaquetteDiagonalCharge fieldValue)))

summedPlaquetteDefectExact : ∀ background fieldValue →
  Sums.sumRational Physical.plaquettes4
    (λ plaquette →
      Physical.plaquetteWilsonSecondVariation background fieldValue plaquette
      - Physical.plaquetteWilsonSecondVariation
          Physical.identityBackground fieldValue plaquette)
  ≡ Physical.physicalWilsonDefect background fieldValue
summedPlaquetteDefectExact background fieldValue =
  trans
    (sumRationalSubtract
      Physical.plaquettes4
      (Physical.plaquetteWilsonSecondVariation background fieldValue)
      (Physical.plaquetteWilsonSecondVariation
        Physical.identityBackground fieldValue))
    refl

physicalWilsonSignedGlobalBeforeIncidence :
  ∀ background fieldValue →
  PhysicalWilsonSignedLocal background fieldValue →
  - (rhoOverThirtySix * plaquetteCrossGlobal fieldValue
      + rhoOverOneFortyFour * plaquetteDiagonalGlobal fieldValue)
  ≤ Physical.physicalWilsonDefect background fieldValue
physicalWilsonSignedGlobalBeforeIncidence background fieldValue local =
  let
    summed = sumRationalMonotone
      Physical.plaquettes4
      (λ plaquette → - plaquetteWilsonBudget fieldValue plaquette)
      (λ plaquette →
        Physical.plaquetteWilsonSecondVariation background fieldValue plaquette
        - Physical.plaquetteWilsonSecondVariation
            Physical.identityBackground fieldValue plaquette)
      (plaquetteLower local)
  in
  subst
    (λ lower → lower ≤ Physical.physicalWilsonDefect background fieldValue)
    (sym (summedPlaquetteBudgetExact fieldValue))
    (subst
      (λ upper →
        Sums.sumRational Physical.plaquettes4
          (λ plaquette → - plaquetteWilsonBudget fieldValue plaquette)
        ≤ upper)
      (summedPlaquetteDefectExact background fieldValue)
      summed)

physicalWilsonGlobalCoefficientExact : ∀ fieldValue →
  rhoOverThirtySix * plaquetteCrossGlobal fieldValue
    + rhoOverOneFortyFour * plaquetteDiagonalGlobal fieldValue
  ≡ (+ 13 / 24) * GaugeBudget.rho
      * Coordinates.physicalSU2BondNormSq fieldValue
physicalWilsonGlobalCoefficientExact fieldValue
  rewrite plaquetteCrossGlobalIsIncidence fieldValue
        | plaquetteDiagonalGlobalIsIncidence fieldValue
        | Incidence.physicalWilsonCrossIncidenceExact fieldValue
        | Incidence.physicalWilsonDiagonalIncidenceExact fieldValue =
  ℚRing.solve-∀
    (Coordinates.physicalSU2BondNormSq fieldValue)

physicalWilsonSignedGlobalThirteenTwentyFourths :
  ∀ background fieldValue →
  PhysicalWilsonSignedLocal background fieldValue →
  - ((+ 13 / 24) * GaugeBudget.rho
      * Coordinates.physicalSU2BondNormSq fieldValue)
  ≤ Physical.physicalWilsonDefect background fieldValue
physicalWilsonSignedGlobalThirteenTwentyFourths
    background fieldValue local =
  subst
    (λ coefficient →
      - coefficient ≤ Physical.physicalWilsonDefect background fieldValue)
    (physicalWilsonGlobalCoefficientExact fieldValue)
    (physicalWilsonSignedGlobalBeforeIncidence background fieldValue local)

physicalWilsonWLocalToGlobalLevel : ProofLevel
physicalWilsonWLocalToGlobalLevel = machineChecked

physicalWilsonThirteenTwentyFourthsLevel : ProofLevel
physicalWilsonThirteenTwentyFourthsLevel = machineChecked
