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
placementBudget fieldValue plaquette placement =
  let
    n0 = PhysicalEnvelope.slotInsertionNorm fieldValue plaquette Placement.slot0
    n1 = PhysicalEnvelope.slotInsertionNorm fieldValue plaquette Placement.slot1
    n2 = PhysicalEnvelope.slotInsertionNorm fieldValue plaquette Placement.slot2
    n3 = PhysicalEnvelope.slotInsertionNorm fieldValue plaquette Placement.slot3
  in Budget.placementYoungBudget placement n0 n1 n2 n3

localInsertionCharge :
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 → ℚ
localInsertionCharge fieldValue plaquette =
  PhysicalEnvelope.slotInsertionNorm fieldValue plaquette Placement.slot0
  + PhysicalEnvelope.slotInsertionNorm fieldValue plaquette Placement.slot1
  + PhysicalEnvelope.slotInsertionNorm fieldValue plaquette Placement.slot2
  + PhysicalEnvelope.slotInsertionNorm fieldValue plaquette Placement.slot3

placementBudgetSumExact : ∀ fieldValue plaquette →
  NamedSum.sumMap Placement.plaquetteSecondVariationPlacements4
    (placementBudget fieldValue plaquette)
  ≡ (+ 4 / 1) * localInsertionCharge fieldValue plaquette
placementBudgetSumExact fieldValue plaquette =
  let
    n0 = PhysicalEnvelope.slotInsertionNorm fieldValue plaquette Placement.slot0
    n1 = PhysicalEnvelope.slotInsertionNorm fieldValue plaquette Placement.slot1
    n2 = PhysicalEnvelope.slotInsertionNorm fieldValue plaquette Placement.slot2
    n3 = PhysicalEnvelope.slotInsertionNorm fieldValue plaquette Placement.slot3
  in Budget.sixteenPlacementBudgetExact n0 n1 n2 n3

localChargeIsPlaquetteDiagonal : ∀ fieldValue site axes →
  localInsertionCharge fieldValue (pair site axes)
  ≡ Wilson.plaquetteDiagonalCharge fieldValue (pair site axes)
localChargeIsPlaquetteDiagonal fieldValue site axes =
  ℚRing.solve-∀
    (Incidence.linkInsertionCharge fieldValue (Physical.pairLeft axes) site)
    (Incidence.linkInsertionCharge fieldValue (Physical.pairRight axes)
      (Periodic.shiftForward (Physical.pairLeft axes) site))
    (Incidence.linkInsertionCharge fieldValue (Physical.pairLeft axes)
      (Periodic.shiftForward (Physical.pairRight axes) site))
    (Incidence.linkInsertionCharge fieldValue (Physical.pairRight axes) site)

placementPairWilsonPart :
  Physical.RationalSU2Background4 → Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 → Placement.PlaquetteSecondVariationPlacement4 → ℚ
placementPairWilsonPart background fieldValue plaquette placement =
  let factors = Partition.physicalPlacementSelectedFactors
        background fieldValue plaquette placement
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
physicalPlaquettePairWilsonPart background fieldValue plaquette =
  NamedSum.sumMap Placement.plaquetteSecondVariationPlacements4
    (placementPairWilsonPart background fieldValue plaquette)

placementPairLower : ∀ background fieldValue plaquette placement →
  Radius.RelaxedInverseLinkRadius background →
  - ((+ 6 / 1) * (Coeff.epsilon * Coeff.epsilon))
      * placementBudget fieldValue plaquette placement
  ≤ placementPairWilsonPart background fieldValue plaquette placement
placementPairLower background fieldValue plaquette placement radius =
  let
    env = PhysicalEnvelope.physicalPlacementEnvelope
      background fieldValue plaquette placement radius
    n0 = PhysicalEnvelope.slotInsertionNorm fieldValue plaquette Placement.slot0
    n1 = PhysicalEnvelope.slotInsertionNorm fieldValue plaquette Placement.slot1
    n2 = PhysicalEnvelope.slotInsertionNorm fieldValue plaquette Placement.slot2
    n3 = PhysicalEnvelope.slotInsertionNorm fieldValue plaquette Placement.slot3
    averageExact = Charges.placementYoungBudgetIsChargeAverage
      placement n0 n1 n2 n3
  in
  subst
    (λ selected →
      - ((+ 6 / 1) * (Coeff.epsilon * Coeff.epsilon)) * selected
      ≤ placementPairWilsonPart background fieldValue plaquette placement)
    (sym averageExact)
    (Pair.pairRemainderLower env)

physicalPairLowerLocalCharge : ∀ background fieldValue plaquette →
  Radius.RelaxedInverseLinkRadius background →
  - Coeff.allPlacementPairCoefficient
      * localInsertionCharge fieldValue plaquette
  ≤ physicalPlaquettePairWilsonPart background fieldValue plaquette
physicalPairLowerLocalCharge background fieldValue plaquette radius =
  let
    summed = sumMapMonotone
      Placement.plaquetteSecondVariationPlacements4
      (λ placement →
        - ((+ 6 / 1) * (Coeff.epsilon * Coeff.epsilon))
          * placementBudget fieldValue plaquette placement)
      (placementPairWilsonPart background fieldValue plaquette)
      (λ placement → placementPairLower background fieldValue plaquette placement radius)
    scale = - ((+ 6 / 1) * (Coeff.epsilon * Coeff.epsilon))
    sumExact = trans
      (sumMapScale scale Placement.plaquetteSecondVariationPlacements4
        (placementBudget fieldValue plaquette))
      (trans
        (cong (scale *_) (placementBudgetSumExact fieldValue plaquette))
        (ℚRing.solve-∀ Coeff.epsilon
          (localInsertionCharge fieldValue plaquette)))
  in
  subst
    (λ lower → lower ≤ physicalPlaquettePairWilsonPart background fieldValue plaquette)
    sumExact summed

physicalPairWilsonLower : ∀ background fieldValue site axes →
  Radius.RelaxedInverseLinkRadius background →
  - ((+ 1 / 256) * Coeff.rho
      * Wilson.plaquetteCrossCharge fieldValue (pair site axes))
  ≤ physicalPlaquettePairWilsonPart background fieldValue (pair site axes)
physicalPairWilsonLower background fieldValue site axes radius =
  let
    local = physicalPairLowerLocalCharge
      background fieldValue (pair site axes) radius
    diagonalExact = localChargeIsPlaquetteDiagonal fieldValue site axes
    crossExact = Incidence.plaquetteCrossChargeIsThreeDiagonal
      fieldValue (Physical.pairLeft axes) (Physical.pairRight axes) site
    coefficientExact :
      Coeff.allPlacementPairCoefficient
        * localInsertionCharge fieldValue (pair site axes)
      ≡ (+ 1 / 256) * Coeff.rho
          * Wilson.plaquetteCrossCharge fieldValue (pair site axes)
    coefficientExact =
      trans
        (cong (Coeff.allPlacementPairCoefficient *_)
          diagonalExact)
        (subst
          (λ cross →
            Coeff.allPlacementPairCoefficient
              * Wilson.plaquetteDiagonalCharge fieldValue (pair site axes)
            ≡ (+ 1 / 256) * Coeff.rho * cross)
          (sym crossExact)
          (ℚRing.solve-∀
            (Wilson.plaquetteDiagonalCharge fieldValue (pair site axes))))
  in
  subst
    (λ coefficient →
      - coefficient ≤ physicalPlaquettePairWilsonPart
        background fieldValue (pair site axes))
    coefficientExact local

placementDeepLower : ∀ background fieldValue plaquette placement →
  Radius.RelaxedInverseLinkRadius background →
  - Coeff.deepPlacementCoefficient * placementBudget fieldValue plaquette placement
  ≤ Split.placementDeepWilsonRemainder background fieldValue plaquette placement
placementDeepLower background fieldValue plaquette placement radius =
  let
    env = PhysicalEnvelope.physicalPlacementEnvelope
      background fieldValue plaquette placement radius
    n0 = PhysicalEnvelope.slotInsertionNorm fieldValue plaquette Placement.slot0
    n1 = PhysicalEnvelope.slotInsertionNorm fieldValue plaquette Placement.slot1
    n2 = PhysicalEnvelope.slotInsertionNorm fieldValue plaquette Placement.slot2
    n3 = PhysicalEnvelope.slotInsertionNorm fieldValue plaquette Placement.slot3
    averageExact = Charges.placementYoungBudgetIsChargeAverage
      placement n0 n1 n2 n3
  in
  subst
    (λ selected →
      - Coeff.deepPlacementCoefficient * selected
      ≤ Split.placementDeepWilsonRemainder background fieldValue plaquette placement)
    (sym averageExact)
    (Deep.deepRemainderLower env)

physicalDeepLowerCoefficient : ∀ background fieldValue plaquette →
  Radius.RelaxedInverseLinkRadius background →
  - Coeff.allPlacementDeepCoefficient * localInsertionCharge fieldValue plaquette
  ≤ Split.physicalPlaquetteDeepWilsonRemainder background fieldValue plaquette
physicalDeepLowerCoefficient background fieldValue plaquette radius =
  let
    summed = sumMapMonotone
      Placement.plaquetteSecondVariationPlacements4
      (λ placement →
        - Coeff.deepPlacementCoefficient * placementBudget fieldValue plaquette placement)
      (Split.placementDeepWilsonRemainder background fieldValue plaquette)
      (λ placement → placementDeepLower background fieldValue plaquette placement radius)
    scale = - Coeff.deepPlacementCoefficient
    sumExact = trans
      (sumMapScale scale Placement.plaquetteSecondVariationPlacements4
        (placementBudget fieldValue plaquette))
      (trans
        (cong (scale *_) (placementBudgetSumExact fieldValue plaquette))
        (ℚRing.solve-∀ Coeff.deepPlacementCoefficient
          (localInsertionCharge fieldValue plaquette)))
  in
  subst
    (λ lower → lower ≤ Split.physicalPlaquetteDeepWilsonRemainder
      background fieldValue plaquette)
    sumExact summed

physicalDeepWilsonRemainderLower : ∀ background fieldValue site axes →
  Radius.RelaxedInverseLinkRadius background →
  - (Wilson.rhoOverOneFortyFour
      * Wilson.plaquetteDiagonalCharge fieldValue (pair site axes))
  ≤ Split.physicalPlaquetteDeepWilsonRemainder
      background fieldValue (pair site axes)
physicalDeepWilsonRemainderLower background fieldValue site axes radius =
  let
    local = physicalDeepLowerCoefficient
      background fieldValue (pair site axes) radius
    q = localInsertionCharge fieldValue (pair site axes)
    qNN : 0ℚ ≤ q
    qNN =
      let
        i0 = PhysicalEnvelope.slotInsertion fieldValue (pair site axes) Placement.slot0
        i1 = PhysicalEnvelope.slotInsertion fieldValue (pair site axes) Placement.slot1
        i2 = PhysicalEnvelope.slotInsertion fieldValue (pair site axes) Placement.slot2
        i3 = PhysicalEnvelope.slotInsertion fieldValue (pair site axes) Placement.slot3
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

    diagonalExact = localChargeIsPlaquetteDiagonal fieldValue site axes
  in
  subst
    (λ diagonal →
      - (Wilson.rhoOverOneFortyFour * diagonal)
      ≤ Split.physicalPlaquetteDeepWilsonRemainder
          background fieldValue (pair site axes))
    diagonalExact
    (ℚP.≤-trans negativeOrder local)

physicalPairLowerLevel : ProofLevel
physicalPairLowerLevel = machineChecked

physicalDeepLowerLevel : ProofLevel
physicalDeepLowerLevel = machineChecked
