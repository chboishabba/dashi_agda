module DASHI.Physics.YangMills.BalabanP33PhysicalPairDeepLowerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson, "Confinement of Quarks".
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field".
-- DOI: 10.1007/BF01240355.
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong
-- Coupling". DOI: 10.1007/s00220-022-04609-1.
--
-- DASHI CONTRIBUTION
--
-- Close the finite part of Gate I.  The literal selected-background radius is
-- instantiated on all sixteen named placements.  The six quadratic subset
-- terms are paid by the correlated channel at exactly rho/256 per cross
-- charge, while the four cubic terms and the quartic term fit below rho/144
-- per diagonal charge with the previously checked positive slack.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; -_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33WilsonPlaquetteSecondVariationPlacementsExact as Placement
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonNamedAtomSumExact as NamedSum
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonCorrelatedDeepPartitionExact as Split
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonLinearNonlinearPartitionExact as Partition
import DASHI.Physics.YangMills.BalabanP33PhysicalSelectedFactorEnvelopeExact as PhysicalEnvelope
import DASHI.Physics.YangMills.BalabanP33WilsonPairEnvelopeExact as Pair
import DASHI.Physics.YangMills.BalabanP33WilsonDeepRemainderEnvelopeExact as Deep
import DASHI.Physics.YangMills.BalabanP33WilsonPairDeepBudgetExact as Coeff
import DASHI.Physics.YangMills.BalabanStrongCouplingSixteenAtomIncidenceBudgetExact as Budget
import DASHI.Physics.YangMills.BalabanStrongCouplingLiteralQuaternionScalarBudgetExact as Charges
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as Wilson
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonIncidenceExact as Incidence
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Radius
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2

sumMapMonotone :
  ∀ {A : Set} (values : List A) (left right : A → ℚ) →
  (∀ value → left value ≤ right value) →
  NamedSum.sumMap values left ≤ NamedSum.sumMap values right
sumMapMonotone [] left right pointwise = ℚP.≤-refl
sumMapMonotone (value ∷ values) left right pointwise =
  ℚP.+-mono-≤ (pointwise value)
    (sumMapMonotone values left right pointwise)

sumMapScale :
  ∀ {A : Set} scale (values : List A) (term : A → ℚ) →
  NamedSum.sumMap values (λ value → scale * term value)
  ≡ scale * NamedSum.sumMap values term
sumMapScale scale [] term = ℚRing.solve-∀ scale
sumMapScale scale (value ∷ values) term
  rewrite sumMapScale scale values term =
  ℚRing.solve-∀ scale (term value) (NamedSum.sumMap values term)

placementBudget :
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 →
  Placement.PlaquetteSecondVariationPlacement4 → ℚ
placementBudget field plaquette placement =
  let
    n0 = PhysicalEnvelope.slotInsertionNorm field plaquette Placement.slot0
    n1 = PhysicalEnvelope.slotInsertionNorm field plaquette Placement.slot1
    n2 = PhysicalEnvelope.slotInsertionNorm field plaquette Placement.slot2
    n3 = PhysicalEnvelope.slotInsertionNorm field plaquette Placement.slot3
  in Budget.placementYoungBudget placement n0 n1 n2 n3

localInsertionCharge :
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 → ℚ
localInsertionCharge field plaquette =
  PhysicalEnvelope.slotInsertionNorm field plaquette Placement.slot0
  + PhysicalEnvelope.slotInsertionNorm field plaquette Placement.slot1
  + PhysicalEnvelope.slotInsertionNorm field plaquette Placement.slot2
  + PhysicalEnvelope.slotInsertionNorm field plaquette Placement.slot3

placementBudgetSumExact : ∀ field plaquette →
  NamedSum.sumMap Placement.plaquetteSecondVariationPlacements4
    (placementBudget field plaquette)
  ≡ (+ 4 / 1) * localInsertionCharge field plaquette
placementBudgetSumExact field plaquette =
  let
    n0 = PhysicalEnvelope.slotInsertionNorm field plaquette Placement.slot0
    n1 = PhysicalEnvelope.slotInsertionNorm field plaquette Placement.slot1
    n2 = PhysicalEnvelope.slotInsertionNorm field plaquette Placement.slot2
    n3 = PhysicalEnvelope.slotInsertionNorm field plaquette Placement.slot3
  in Budget.sixteenPlacementBudgetExact n0 n1 n2 n3

localChargeIsPlaquetteDiagonal : ∀ field site axes →
  localInsertionCharge field (pair site axes)
  ≡ Wilson.plaquetteDiagonalCharge field (pair site axes)
localChargeIsPlaquetteDiagonal field site axes =
  ℚRing.solve-∀
    (Incidence.linkInsertionCharge field (Physical.pairLeft axes) site)
    (Incidence.linkInsertionCharge field (Physical.pairRight axes)
      (Periodic.shiftForward (Physical.pairLeft axes) site))
    (Incidence.linkInsertionCharge field (Physical.pairLeft axes)
      (Periodic.shiftForward (Physical.pairRight axes) site))
    (Incidence.linkInsertionCharge field (Physical.pairRight axes) site)

placementPairWilsonPart :
  Physical.RationalSU2Background4 → Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 → Placement.PlaquetteSecondVariationPlacement4 → ℚ
placementPairWilsonPart background field plaquette placement =
  let factors = Partition.physicalPlacementSelectedFactors
        background field plaquette placement
  in
  Telescope.wilsonScalar
    (Split.fourFactorPairPart
      (Partition.a0 factors) (Partition.a1 factors)
      (Partition.a2 factors) (Partition.a3 factors)
      (Partition.b0 factors) (Partition.b1 factors)
      (Partition.b2 factors) (Partition.b3 factors))

physicalPlaquettePairWilsonPart :
  Physical.RationalSU2Background4 → Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 → ℚ
physicalPlaquettePairWilsonPart background field plaquette =
  NamedSum.sumMap Placement.plaquetteSecondVariationPlacements4
    (placementPairWilsonPart background field plaquette)

placementPairLower : ∀ background field plaquette placement →
  Radius.RelaxedInverseLinkRadius background →
  - ((+ 6 / 1) * (Coeff.epsilon * Coeff.epsilon))
      * placementBudget field plaquette placement
  ≤ placementPairWilsonPart background field plaquette placement
placementPairLower background field plaquette placement radius =
  let
    env = PhysicalEnvelope.physicalPlacementEnvelope
      background field plaquette placement radius
    n0 = PhysicalEnvelope.slotInsertionNorm field plaquette Placement.slot0
    n1 = PhysicalEnvelope.slotInsertionNorm field plaquette Placement.slot1
    n2 = PhysicalEnvelope.slotInsertionNorm field plaquette Placement.slot2
    n3 = PhysicalEnvelope.slotInsertionNorm field plaquette Placement.slot3
    averageExact = Charges.placementYoungBudgetIsChargeAverage
      placement n0 n1 n2 n3
  in
  subst
    (λ selected →
      - ((+ 6 / 1) * (Coeff.epsilon * Coeff.epsilon)) * selected
      ≤ placementPairWilsonPart background field plaquette placement)
    (sym averageExact)
    (Pair.pairRemainderLower env)

physicalPairLowerLocalCharge : ∀ background field plaquette →
  Radius.RelaxedInverseLinkRadius background →
  - Coeff.allPlacementPairCoefficient
      * localInsertionCharge field plaquette
  ≤ physicalPlaquettePairWilsonPart background field plaquette
physicalPairLowerLocalCharge background field plaquette radius =
  let
    summed = sumMapMonotone
      Placement.plaquetteSecondVariationPlacements4
      (λ placement →
        - ((+ 6 / 1) * (Coeff.epsilon * Coeff.epsilon))
          * placementBudget field plaquette placement)
      (placementPairWilsonPart background field plaquette)
      (λ placement → placementPairLower background field plaquette placement radius)
    scale = - ((+ 6 / 1) * (Coeff.epsilon * Coeff.epsilon))
    sumExact = trans
      (sumMapScale scale Placement.plaquetteSecondVariationPlacements4
        (placementBudget field plaquette))
      (trans
        (cong (scale *_) (placementBudgetSumExact field plaquette))
        (ℚRing.solve-∀ Coeff.epsilon
          (localInsertionCharge field plaquette)))
  in
  subst
    (λ lower → lower ≤ physicalPlaquettePairWilsonPart background field plaquette)
    sumExact summed

physicalPairWilsonLower : ∀ background field site axes →
  Radius.RelaxedInverseLinkRadius background →
  - ((+ 1 / 256) * Coeff.rho
      * Wilson.plaquetteCrossCharge field (pair site axes))
  ≤ physicalPlaquettePairWilsonPart background field (pair site axes)
physicalPairWilsonLower background field site axes radius =
  let
    local = physicalPairLowerLocalCharge
      background field (pair site axes) radius
    diagonalExact = localChargeIsPlaquetteDiagonal field site axes
    crossExact = Incidence.plaquetteCrossChargeIsThreeDiagonal
      field (Physical.pairLeft axes) (Physical.pairRight axes) site
    coefficientExact :
      Coeff.allPlacementPairCoefficient
        * localInsertionCharge field (pair site axes)
      ≡ (+ 1 / 256) * Coeff.rho
          * Wilson.plaquetteCrossCharge field (pair site axes)
    coefficientExact =
      trans
        (cong (Coeff.allPlacementPairCoefficient *_)
          diagonalExact)
        (subst
          (λ cross →
            Coeff.allPlacementPairCoefficient
              * Wilson.plaquetteDiagonalCharge field (pair site axes)
            ≡ (+ 1 / 256) * Coeff.rho * cross)
          (sym crossExact)
          (ℚRing.solve-∀
            (Wilson.plaquetteDiagonalCharge field (pair site axes))))
  in
  subst
    (λ coefficient →
      - coefficient ≤ physicalPlaquettePairWilsonPart
        background field (pair site axes))
    coefficientExact local

placementDeepLower : ∀ background field plaquette placement →
  Radius.RelaxedInverseLinkRadius background →
  - Coeff.deepPlacementCoefficient * placementBudget field plaquette placement
  ≤ Split.placementDeepWilsonRemainder background field plaquette placement
placementDeepLower background field plaquette placement radius =
  let
    env = PhysicalEnvelope.physicalPlacementEnvelope
      background field plaquette placement radius
    n0 = PhysicalEnvelope.slotInsertionNorm field plaquette Placement.slot0
    n1 = PhysicalEnvelope.slotInsertionNorm field plaquette Placement.slot1
    n2 = PhysicalEnvelope.slotInsertionNorm field plaquette Placement.slot2
    n3 = PhysicalEnvelope.slotInsertionNorm field plaquette Placement.slot3
    averageExact = Charges.placementYoungBudgetIsChargeAverage
      placement n0 n1 n2 n3
  in
  subst
    (λ selected →
      - Coeff.deepPlacementCoefficient * selected
      ≤ Split.placementDeepWilsonRemainder background field plaquette placement)
    (sym averageExact)
    (Deep.deepRemainderLower env)

physicalDeepLowerCoefficient : ∀ background field plaquette →
  Radius.RelaxedInverseLinkRadius background →
  - Coeff.allPlacementDeepCoefficient * localInsertionCharge field plaquette
  ≤ Split.physicalPlaquetteDeepWilsonRemainder background field plaquette
physicalDeepLowerCoefficient background field plaquette radius =
  let
    summed = sumMapMonotone
      Placement.plaquetteSecondVariationPlacements4
      (λ placement →
        - Coeff.deepPlacementCoefficient * placementBudget field plaquette placement)
      (Split.placementDeepWilsonRemainder background field plaquette)
      (λ placement → placementDeepLower background field plaquette placement radius)
    scale = - Coeff.deepPlacementCoefficient
    sumExact = trans
      (sumMapScale scale Placement.plaquetteSecondVariationPlacements4
        (placementBudget field plaquette))
      (trans
        (cong (scale *_) (placementBudgetSumExact field plaquette))
        (ℚRing.solve-∀ Coeff.deepPlacementCoefficient
          (localInsertionCharge field plaquette)))
  in
  subst
    (λ lower → lower ≤ Split.physicalPlaquetteDeepWilsonRemainder
      background field plaquette)
    sumExact summed

physicalDeepWilsonRemainderLower : ∀ background field site axes →
  Radius.RelaxedInverseLinkRadius background →
  - (Wilson.rhoOverOneFortyFour
      * Wilson.plaquetteDiagonalCharge field (pair site axes))
  ≤ Split.physicalPlaquetteDeepWilsonRemainder
      background field (pair site axes)
physicalDeepWilsonRemainderLower background field site axes radius =
  let
    local = physicalDeepLowerCoefficient
      background field (pair site axes) radius
    q = localInsertionCharge field (pair site axes)
    qNN : 0ℚ ≤ q
    qNN =
      let
        i0 = PhysicalEnvelope.slotInsertion field (pair site axes) Placement.slot0
        i1 = PhysicalEnvelope.slotInsertion field (pair site axes) Placement.slot1
        i2 = PhysicalEnvelope.slotInsertion field (pair site axes) Placement.slot2
        i3 = PhysicalEnvelope.slotInsertion field (pair site axes) Placement.slot3
      in
      FiniteL2.addNonnegative
        (FiniteL2.addNonnegative
          (FiniteL2.addNonnegative
            (Norm.normSqNonnegative i0)
            (Norm.normSqNonnegative i1))
          (Norm.normSqNonnegative i2))
        (Norm.normSqNonnegative i3)

    scaledCoefficient :
      Coeff.allPlacementDeepCoefficient * q
      ≤ Coeff.diagonalTargetCoefficient * q
    scaledCoefficient = Norm.scaleNonnegative q qNN
      Coeff.deepCoefficientBelowDiagonalTarget

    negativeOrder :
      - (Coeff.diagonalTargetCoefficient * q)
      ≤ - (Coeff.allPlacementDeepCoefficient * q)
    negativeOrder = ℚP.neg-mono-≤ scaledCoefficient

    diagonalExact = localChargeIsPlaquetteDiagonal field site axes
  in
  subst
    (λ diagonal →
      - (Wilson.rhoOverOneFortyFour * diagonal)
      ≤ Split.physicalPlaquetteDeepWilsonRemainder
          background field (pair site axes))
    diagonalExact
    (ℚP.≤-trans negativeOrder local)

physicalPairLowerLevel : ProofLevel
physicalPairLowerLevel = machineChecked

physicalDeepLowerLevel : ProofLevel
physicalDeepLowerLevel = machineChecked
