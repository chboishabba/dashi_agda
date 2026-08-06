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
plaquetteDiagonalCharge field (pair site axes) =
  Incidence.plaquetteDiagonalCharge field
    (Physical.pairLeft axes) (Physical.pairRight axes) site

plaquetteCrossCharge :
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 → ℚ
plaquetteCrossCharge field (pair site axes) =
  Incidence.plaquetteCrossCharge field
    (Physical.pairLeft axes) (Physical.pairRight axes) site

pairDiagonalFromPlaquettes :
  Coordinates.PhysicalSU2BondField4 → Physical.AxisPair6 → ℚ
pairDiagonalFromPlaquettes field axes =
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ site → plaquetteDiagonalCharge field (pair site axes))

pairCrossFromPlaquettes :
  Coordinates.PhysicalSU2BondField4 → Physical.AxisPair6 → ℚ
pairCrossFromPlaquettes field axes =
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ site → plaquetteCrossCharge field (pair site axes))

pairDiagonalFromPlaquettesExact : ∀ field axes →
  pairDiagonalFromPlaquettes field axes
  ≡ Incidence.pairDiagonalIncidence field
      (Physical.pairLeft axes) (Physical.pairRight axes)
pairDiagonalFromPlaquettesExact field axes =
  trans
    (Partition.globalSiteSumMatchesCoordinateSum4
      (λ site →
        Incidence.plaquetteDiagonalCharge field
          (Physical.pairLeft axes) (Physical.pairRight axes) site))
    refl

pairCrossFromPlaquettesExact : ∀ field axes →
  pairCrossFromPlaquettes field axes
  ≡ Incidence.pairCrossIncidence field
      (Physical.pairLeft axes) (Physical.pairRight axes)
pairCrossFromPlaquettesExact field axes =
  trans
    (Partition.globalSiteSumMatchesCoordinateSum4
      (λ site →
        Incidence.plaquetteCrossCharge field
          (Physical.pairLeft axes) (Physical.pairRight axes) site))
    refl

plaquetteDiagonalGlobal :
  Coordinates.PhysicalSU2BondField4 → ℚ
plaquetteDiagonalGlobal field =
  Sums.sumRational Physical.plaquettes4
    (plaquetteDiagonalCharge field)

plaquetteCrossGlobal :
  Coordinates.PhysicalSU2BondField4 → ℚ
plaquetteCrossGlobal field =
  Sums.sumRational Physical.plaquettes4
    (plaquetteCrossCharge field)

plaquetteDiagonalGlobalIsIncidence : ∀ field →
  plaquetteDiagonalGlobal field
  ≡ Incidence.physicalWilsonDiagonalIncidence field
plaquetteDiagonalGlobalIsIncidence field =
  trans
    (Fubini.sumCartesian
      (Block.physicalBlockSites Path4.side4)
      Physical.axisPairs6
      (plaquetteDiagonalCharge field))
    (trans
      (Fubini.sumSwap
        (Block.physicalBlockSites Path4.side4)
        Physical.axisPairs6
        (λ site axes → plaquetteDiagonalCharge field (pair site axes)))
      (trans
        (Sums.sumRationalCong
          Physical.axisPairs6
          (pairDiagonalFromPlaquettes field)
          (λ axes →
            Incidence.pairDiagonalIncidence field
              (Physical.pairLeft axes) (Physical.pairRight axes))
          (pairDiagonalFromPlaquettesExact field))
        (ℚRing.solve-∀
          (Incidence.pairDiagonalIncidence field
            Periodic.axis0 Periodic.axis1)
          (Incidence.pairDiagonalIncidence field
            Periodic.axis0 Periodic.axis2)
          (Incidence.pairDiagonalIncidence field
            Periodic.axis0 Periodic.axis3)
          (Incidence.pairDiagonalIncidence field
            Periodic.axis1 Periodic.axis2)
          (Incidence.pairDiagonalIncidence field
            Periodic.axis1 Periodic.axis3)
          (Incidence.pairDiagonalIncidence field
            Periodic.axis2 Periodic.axis3))))

plaquetteCrossGlobalIsIncidence : ∀ field →
  plaquetteCrossGlobal field
  ≡ Incidence.physicalWilsonCrossIncidence field
plaquetteCrossGlobalIsIncidence field =
  trans
    (Fubini.sumCartesian
      (Block.physicalBlockSites Path4.side4)
      Physical.axisPairs6
      (plaquetteCrossCharge field))
    (trans
      (Fubini.sumSwap
        (Block.physicalBlockSites Path4.side4)
        Physical.axisPairs6
        (λ site axes → plaquetteCrossCharge field (pair site axes)))
      (trans
        (Sums.sumRationalCong
          Physical.axisPairs6
          (pairCrossFromPlaquettes field)
          (λ axes →
            Incidence.pairCrossIncidence field
              (Physical.pairLeft axes) (Physical.pairRight axes))
          (pairCrossFromPlaquettesExact field))
        (ℚRing.solve-∀
          (Incidence.pairCrossIncidence field
            Periodic.axis0 Periodic.axis1)
          (Incidence.pairCrossIncidence field
            Periodic.axis0 Periodic.axis2)
          (Incidence.pairCrossIncidence field
            Periodic.axis0 Periodic.axis3)
          (Incidence.pairCrossIncidence field
            Periodic.axis1 Periodic.axis2)
          (Incidence.pairCrossIncidence field
            Periodic.axis1 Periodic.axis3)
          (Incidence.pairCrossIncidence field
            Periodic.axis2 Periodic.axis3))))

rhoOverThirtySix rhoOverOneFortyFour : ℚ
rhoOverThirtySix = (+ 1 / 36) * GaugeBudget.rho
rhoOverOneFortyFour = (+ 1 / 144) * GaugeBudget.rho

plaquetteWilsonBudget :
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 → ℚ
plaquetteWilsonBudget field plaquette =
  rhoOverThirtySix * plaquetteCrossCharge field plaquette
  + rhoOverOneFortyFour * plaquetteDiagonalCharge field plaquette

record PhysicalWilsonSignedLocal
    (background : Physical.RationalSU2Background4)
    (field : Coordinates.PhysicalSU2BondField4) : Set where
  field
    plaquetteLower : ∀ plaquette →
      - plaquetteWilsonBudget field plaquette
      ≤ Physical.plaquetteWilsonSecondVariation
          background field plaquette
        - Physical.plaquetteWilsonSecondVariation
          Physical.identityBackground field plaquette

open PhysicalWilsonSignedLocal public

summedPlaquetteBudgetExact : ∀ field →
  Sums.sumRational Physical.plaquettes4
    (λ plaquette → - plaquetteWilsonBudget field plaquette)
  ≡ - (rhoOverThirtySix * plaquetteCrossGlobal field
      + rhoOverOneFortyFour * plaquetteDiagonalGlobal field)
summedPlaquetteBudgetExact field =
  trans
    (Sums.sumRationalNegate
      Physical.plaquettes4 (plaquetteWilsonBudget field))
    (cong -_
      (sumRationalLinear2
        rhoOverThirtySix rhoOverOneFortyFour
        Physical.plaquettes4
        (plaquetteCrossCharge field)
        (plaquetteDiagonalCharge field)))

summedPlaquetteDefectExact : ∀ background field →
  Sums.sumRational Physical.plaquettes4
    (λ plaquette →
      Physical.plaquetteWilsonSecondVariation background field plaquette
      - Physical.plaquetteWilsonSecondVariation
          Physical.identityBackground field plaquette)
  ≡ Physical.physicalWilsonDefect background field
summedPlaquetteDefectExact background field =
  trans
    (sumRationalSubtract
      Physical.plaquettes4
      (Physical.plaquetteWilsonSecondVariation background field)
      (Physical.plaquetteWilsonSecondVariation
        Physical.identityBackground field))
    refl

physicalWilsonSignedGlobalBeforeIncidence :
  ∀ background field →
  PhysicalWilsonSignedLocal background field →
  - (rhoOverThirtySix * plaquetteCrossGlobal field
      + rhoOverOneFortyFour * plaquetteDiagonalGlobal field)
  ≤ Physical.physicalWilsonDefect background field
physicalWilsonSignedGlobalBeforeIncidence background field local =
  let
    summed = sumRationalMonotone
      Physical.plaquettes4
      (λ plaquette → - plaquetteWilsonBudget field plaquette)
      (λ plaquette →
        Physical.plaquetteWilsonSecondVariation background field plaquette
        - Physical.plaquetteWilsonSecondVariation
            Physical.identityBackground field plaquette)
      (plaquetteLower local)
  in
  subst
    (λ lower → lower ≤ Physical.physicalWilsonDefect background field)
    (sym (summedPlaquetteBudgetExact field))
    (subst
      (λ upper →
        Sums.sumRational Physical.plaquettes4
          (λ plaquette → - plaquetteWilsonBudget field plaquette)
        ≤ upper)
      (summedPlaquetteDefectExact background field)
      summed)

physicalWilsonGlobalCoefficientExact : ∀ field →
  rhoOverThirtySix * plaquetteCrossGlobal field
    + rhoOverOneFortyFour * plaquetteDiagonalGlobal field
  ≡ (+ 13 / 24) * GaugeBudget.rho
      * Coordinates.physicalSU2BondNormSq field
physicalWilsonGlobalCoefficientExact field
  rewrite plaquetteCrossGlobalIsIncidence field
        | plaquetteDiagonalGlobalIsIncidence field
        | Incidence.physicalWilsonCrossIncidenceExact field
        | Incidence.physicalWilsonDiagonalIncidenceExact field =
  ℚRing.solve-∀
    (Coordinates.physicalSU2BondNormSq field)

physicalWilsonSignedGlobalThirteenTwentyFourths :
  ∀ background field →
  PhysicalWilsonSignedLocal background field →
  - ((+ 13 / 24) * GaugeBudget.rho
      * Coordinates.physicalSU2BondNormSq field)
  ≤ Physical.physicalWilsonDefect background field
physicalWilsonSignedGlobalThirteenTwentyFourths
    background field local =
  subst
    (λ coefficient →
      - coefficient ≤ Physical.physicalWilsonDefect background field)
    (physicalWilsonGlobalCoefficientExact field)
    (physicalWilsonSignedGlobalBeforeIncidence background field local)

physicalWilsonWLocalToGlobalLevel : ProofLevel
physicalWilsonWLocalToGlobalLevel = machineChecked

physicalWilsonThirteenTwentyFourthsLevel : ProofLevel
physicalWilsonThirteenTwentyFourthsLevel = machineChecked
