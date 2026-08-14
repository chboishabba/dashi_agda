module DASHI.Physics.YangMills.BalabanP33PhysicalSelectedFactorEnvelopeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson, "Confinement of Quarks".
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition. DOI: 10.1007/978-3-319-13467-3.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field".
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Instantiate the generic selected-factor envelope on every literal positive
-- and inverse physical plaquette jet.  The proof derives the factor weights
-- from the actual four insertions, transports the selected-background link
-- radius to every factor defect, and proves the weight product equals the
-- named placement's left/right Young charge.  No placement envelope is
-- supplied independently of the physical background, field or plaquette.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33QuaternionAdjointNormSquaredExact as AdjointNorm
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33WilsonPlaquetteSecondVariationPlacementsExact as Placement
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonPlacementTelescopeExact as Named
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonLinearNonlinearPartitionExact as Partition
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Radius
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeSignedLowerExact as Signed
import DASHI.Physics.YangMills.BalabanP33WilsonPairDeepBudgetExact as Budget
import DASHI.Physics.YangMills.BalabanP33WilsonDeepRemainderEnvelopeExact as Envelope
import DASHI.Physics.YangMills.BalabanStrongCouplingLiteralQuaternionScalarBudgetExact as Charges
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonIncidenceExact as Incidence
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2

positiveUnitJet inverseUnitJet :
  Q.RationalQuaternion → Q.RationalQuaternion → Q.QuaternionFactorJet
positiveUnitJet unit insertion =
  Q.factorJet unit (unit Q.*q insertion)
    (unit Q.*q (insertion Q.*q insertion))
inverseUnitJet unit insertion =
  Q.factorJet
    (Physical.quaternionConjugate unit)
    (Q.negQ insertion Q.*q Physical.quaternionConjugate unit)
    ((insertion Q.*q insertion) Q.*q Physical.quaternionConjugate unit)

selectionWeight : Named.FactorSelection → ℚ → ℚ
selectionWeight Named.valueSelection insertionNorm = 1ℚ
selectionWeight Named.firstSelection insertionNorm = insertionNorm
selectionWeight Named.secondSelection insertionNorm = insertionNorm * insertionNorm

selectionWeightNonnegative : ∀ selection n →
  0ℚ ≤ n → 0ℚ ≤ selectionWeight selection n
selectionWeightNonnegative Named.valueSelection n nNN = ℚP.nonNegative⁻¹ 1ℚ
selectionWeightNonnegative Named.firstSelection n nNN = nNN
selectionWeightNonnegative Named.secondSelection n nNN =
  FiniteL2.squareNonnegative n

normSqNegExact : ∀ value →
  Norm.normSq (Q.negQ value) ≡ Norm.normSq value
normSqNegExact (Q.quat q0 q1 q2 q3) = ℚRing.solve-∀ q0 q1 q2 q3

identityPositiveSelectedNorm : ∀ insertion selection →
  Norm.normSq (Named.applySelection selection
    (positiveUnitJet Q.oneQ insertion))
  ≡ selectionWeight selection (Norm.normSq insertion)
identityPositiveSelectedNorm insertion Named.valueSelection = ℚRing.solve []
identityPositiveSelectedNorm insertion Named.firstSelection =
  trans (Norm.normSqMultiplyExact Q.oneQ insertion)
    (ℚRing.solve-∀ (Norm.normSq insertion))
identityPositiveSelectedNorm insertion Named.secondSelection =
  trans
    (Norm.normSqMultiplyExact Q.oneQ (insertion Q.*q insertion))
    (trans
      (cong (Norm.normSq Q.oneQ *_)
        (Norm.normSqMultiplyExact insertion insertion))
      (ℚRing.solve-∀ (Norm.normSq insertion)))

identityInverseSelectedNorm : ∀ insertion selection →
  Norm.normSq (Named.applySelection selection
    (inverseUnitJet Q.oneQ insertion))
  ≡ selectionWeight selection (Norm.normSq insertion)
identityInverseSelectedNorm insertion Named.valueSelection = ℚRing.solve []
identityInverseSelectedNorm insertion Named.firstSelection =
  trans
    (Norm.normSqMultiplyExact
      (Q.negQ insertion) (Physical.quaternionConjugate Q.oneQ))
    (trans
      (cong (_* Norm.normSq (Physical.quaternionConjugate Q.oneQ))
        (normSqNegExact insertion))
      (ℚRing.solve-∀ (Norm.normSq insertion)))
identityInverseSelectedNorm insertion Named.secondSelection =
  trans
    (Norm.normSqMultiplyExact
      (insertion Q.*q insertion) (Physical.quaternionConjugate Q.oneQ))
    (trans
      (cong (_* Norm.normSq (Physical.quaternionConjugate Q.oneQ))
        (Norm.normSqMultiplyExact insertion insertion))
      (ℚRing.solve-∀ (Norm.normSq insertion)))

positiveSelectedDefectNorm : ∀ unit insertion selection →
  Norm.normSq
    (Telescope._-q_
      (Named.applySelection selection (positiveUnitJet unit insertion))
      (Named.applySelection selection (positiveUnitJet Q.oneQ insertion)))
  ≡ Norm.normSq (Telescope._-q_ unit Q.oneQ)
      * selectionWeight selection (Norm.normSq insertion)
positiveSelectedDefectNorm
    (Q.quat u0 u1 u2 u3) (Q.quat x0 x1 x2 x3)
    Named.valueSelection = ℚRing.solve-∀ u0 u1 u2 u3
positiveSelectedDefectNorm
    (Q.quat u0 u1 u2 u3) (Q.quat x0 x1 x2 x3)
    Named.firstSelection = ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3
positiveSelectedDefectNorm
    (Q.quat u0 u1 u2 u3) (Q.quat x0 x1 x2 x3)
    Named.secondSelection = ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3

inverseSelectedDefectNorm : ∀ unit insertion selection →
  Norm.normSq
    (Telescope._-q_
      (Named.applySelection selection (inverseUnitJet unit insertion))
      (Named.applySelection selection (inverseUnitJet Q.oneQ insertion)))
  ≡ Norm.normSq
      (Telescope._-q_ (Physical.quaternionConjugate unit) Q.oneQ)
      * selectionWeight selection (Norm.normSq insertion)
inverseSelectedDefectNorm
    (Q.quat u0 u1 u2 u3) (Q.quat x0 x1 x2 x3)
    Named.valueSelection = ℚRing.solve-∀ u0 u1 u2 u3
inverseSelectedDefectNorm
    (Q.quat u0 u1 u2 u3) (Q.quat x0 x1 x2 x3)
    Named.firstSelection = ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3
inverseSelectedDefectNorm
    (Q.quat u0 u1 u2 u3) (Q.quat x0 x1 x2 x3)
    Named.secondSelection = ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3

record SelectedFactorEnvelope
    (actual flat : Q.RationalQuaternion) (epsilon : ℚ) : Set where
  field
    weight : ℚ
    weightNonnegative : 0ℚ ≤ weight
    flatNormExact : Norm.normSq flat ≡ weight
    defectNormUpper :
      Norm.normSq (Telescope._-q_ actual flat)
      ≤ (epsilon * epsilon) * weight

open SelectedFactorEnvelope public

scaledDefectUpper : ∀ defect weight epsilon →
  0ℚ ≤ weight → defect ≤ epsilon * epsilon →
  defect * weight ≤ (epsilon * epsilon) * weight
scaledDefectUpper defect weight epsilon weightNN defectUpper =
  subst
    (λ lower → lower ≤ (epsilon * epsilon) * weight)
    (ℚRing.solve-∀ defect weight)
    (subst
      (λ upper → weight * defect ≤ upper)
      (ℚRing.solve-∀ epsilon weight)
      (Norm.scaleNonnegative weight weightNN defectUpper))

positiveFactorEnvelope : ∀ unit insertion selection epsilon →
  Norm.normSq (Telescope._-q_ unit Q.oneQ) ≤ epsilon * epsilon →
  SelectedFactorEnvelope
    (Named.applySelection selection (positiveUnitJet unit insertion))
    (Named.applySelection selection (positiveUnitJet Q.oneQ insertion))
    epsilon
positiveFactorEnvelope unit insertion selection epsilon linkUpper =
  let
    n = Norm.normSq insertion
    w = selectionWeight selection n
    wNN = selectionWeightNonnegative selection n
      (Norm.normSqNonnegative insertion)
    defectExact = positiveSelectedDefectNorm unit insertion selection
  in
  record
    { weight = w
    ; weightNonnegative = wNN
    ; flatNormExact = identityPositiveSelectedNorm insertion selection
    ; defectNormUpper =
        subst
          (λ lower → lower ≤ (epsilon * epsilon) * w)
          (sym defectExact)
          (scaledDefectUpper
            (Norm.normSq (Telescope._-q_ unit Q.oneQ))
            w epsilon wNN linkUpper)
    }

inverseFactorEnvelope : ∀ unit insertion selection epsilon →
  Norm.normSq
    (Telescope._-q_ (Physical.quaternionConjugate unit) Q.oneQ)
  ≤ epsilon * epsilon →
  SelectedFactorEnvelope
    (Named.applySelection selection (inverseUnitJet unit insertion))
    (Named.applySelection selection (inverseUnitJet Q.oneQ insertion))
    epsilon
inverseFactorEnvelope unit insertion selection epsilon linkUpper =
  let
    n = Norm.normSq insertion
    w = selectionWeight selection n
    wNN = selectionWeightNonnegative selection n
      (Norm.normSqNonnegative insertion)
    defectExact = inverseSelectedDefectNorm unit insertion selection
  in
  record
    { weight = w
    ; weightNonnegative = wNN
    ; flatNormExact = identityInverseSelectedNorm insertion selection
    ; defectNormUpper =
        subst
          (λ lower → lower ≤ (epsilon * epsilon) * w)
          (sym defectExact)
          (scaledDefectUpper
            (Norm.normSq
              (Telescope._-q_ (Physical.quaternionConjugate unit) Q.oneQ))
            w epsilon wNN linkUpper)
    }

epsilonSquareIsFourRhoSquare :
  Budget.epsilon * Budget.epsilon ≡ Radius.fourRhoSquare
epsilonSquareIsFourRhoSquare = ℚRing.solve []

positiveLinkUpper : ∀ background → Radius.RelaxedInverseLinkRadius background →
  ∀ bond →
  Norm.normSq (Telescope._-q_ (Physical.link background bond) Q.oneQ)
  ≤ Budget.epsilon * Budget.epsilon
positiveLinkUpper background radius bond =
  let
    inverseUpper = radius bond
    sameNorm = AdjointNorm.inverseDifferenceNormSqExact
      (Physical.link background bond)
  in
  subst
    (λ upper →
      Norm.normSq (Telescope._-q_ (Physical.link background bond) Q.oneQ)
      ≤ upper)
    (sym epsilonSquareIsFourRhoSquare)
    (subst
      (λ lower → lower ≤ Radius.fourRhoSquare)
      sameNorm inverseUpper)

inverseLinkUpper : ∀ background → Radius.RelaxedInverseLinkRadius background →
  ∀ bond →
  Norm.normSq
    (Telescope._-q_ (Physical.inverseLink background bond) Q.oneQ)
  ≤ Budget.epsilon * Budget.epsilon
inverseLinkUpper background radius bond =
  subst
    (λ upper →
      Norm.normSq
        (Telescope._-q_ (Physical.inverseLink background bond) Q.oneQ)
      ≤ upper)
    (sym epsilonSquareIsFourRhoSquare)
    (radius bond)

slotInsertion :
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 →
  Placement.PlaquetteLinkSlot4 → Q.RationalQuaternion
slotInsertion fieldValue (pair site axes) Placement.slot0 =
  Q.pureQuaternion (Physical.insertionAt fieldValue (Physical.pairLeft axes) site)
slotInsertion fieldValue (pair site axes) Placement.slot1 =
  Q.pureQuaternion
    (Physical.insertionAt fieldValue (Physical.pairRight axes)
      (Periodic.shiftForward (Physical.pairLeft axes) site))
slotInsertion fieldValue (pair site axes) Placement.slot2 =
  Q.pureQuaternion
    (Physical.insertionAt fieldValue (Physical.pairLeft axes)
      (Periodic.shiftForward (Physical.pairRight axes) site))
slotInsertion fieldValue (pair site axes) Placement.slot3 =
  Q.pureQuaternion (Physical.insertionAt fieldValue (Physical.pairRight axes) site)

slotUnit :
  Physical.RationalSU2Background4 → Physical.Plaquette4 →
  Placement.PlaquetteLinkSlot4 → Q.RationalQuaternion
slotUnit background (pair site axes) Placement.slot0 =
  Physical.link background (pair site (Physical.pairLeft axes))
slotUnit background (pair site axes) Placement.slot1 =
  Physical.link background
    (pair (Periodic.shiftForward (Physical.pairLeft axes) site)
      (Physical.pairRight axes))
slotUnit background (pair site axes) Placement.slot2 =
  Physical.link background
    (pair (Periodic.shiftForward (Physical.pairRight axes) site)
      (Physical.pairLeft axes))
slotUnit background (pair site axes) Placement.slot3 =
  Physical.link background (pair site (Physical.pairRight axes))

slotActualFactor :
  Physical.RationalSU2Background4 → Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 → Placement.PlaquetteLinkSlot4 →
  Named.FactorSelection → Q.RationalQuaternion
slotActualFactor background fieldValue plaquette Placement.slot0 selection =
  Named.applySelection selection
    (positiveUnitJet
      (slotUnit background plaquette Placement.slot0)
      (slotInsertion fieldValue plaquette Placement.slot0))
slotActualFactor background fieldValue plaquette Placement.slot1 selection =
  Named.applySelection selection
    (positiveUnitJet
      (slotUnit background plaquette Placement.slot1)
      (slotInsertion fieldValue plaquette Placement.slot1))
slotActualFactor background fieldValue plaquette Placement.slot2 selection =
  Named.applySelection selection
    (inverseUnitJet
      (slotUnit background plaquette Placement.slot2)
      (slotInsertion fieldValue plaquette Placement.slot2))
slotActualFactor background fieldValue plaquette Placement.slot3 selection =
  Named.applySelection selection
    (inverseUnitJet
      (slotUnit background plaquette Placement.slot3)
      (slotInsertion fieldValue plaquette Placement.slot3))

slotFlatFactor :
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 →
  Placement.PlaquetteLinkSlot4 → Named.FactorSelection →
  Q.RationalQuaternion
slotFlatFactor fieldValue plaquette Placement.slot0 selection =
  Named.applySelection selection
    (positiveUnitJet Q.oneQ (slotInsertion fieldValue plaquette Placement.slot0))
slotFlatFactor fieldValue plaquette Placement.slot1 selection =
  Named.applySelection selection
    (positiveUnitJet Q.oneQ (slotInsertion fieldValue plaquette Placement.slot1))
slotFlatFactor fieldValue plaquette Placement.slot2 selection =
  Named.applySelection selection
    (inverseUnitJet Q.oneQ (slotInsertion fieldValue plaquette Placement.slot2))
slotFlatFactor fieldValue plaquette Placement.slot3 selection =
  Named.applySelection selection
    (inverseUnitJet Q.oneQ (slotInsertion fieldValue plaquette Placement.slot3))

slotSelectedEnvelope :
  ∀ background fieldValue plaquette slot selection →
  Radius.RelaxedInverseLinkRadius background →
  SelectedFactorEnvelope
    (slotActualFactor background fieldValue plaquette slot selection)
    (slotFlatFactor fieldValue plaquette slot selection)
    Budget.epsilon
slotSelectedEnvelope background fieldValue (pair site axes)
    Placement.slot0 selection radius =
  positiveFactorEnvelope
    (Physical.link background (pair site (Physical.pairLeft axes)))
    (slotInsertion fieldValue (pair site axes) Placement.slot0)
    selection Budget.epsilon
    (positiveLinkUpper background radius
      (pair site (Physical.pairLeft axes)))
slotSelectedEnvelope background fieldValue (pair site axes)
    Placement.slot1 selection radius =
  positiveFactorEnvelope
    (Physical.link background
      (pair (Periodic.shiftForward (Physical.pairLeft axes) site)
        (Physical.pairRight axes)))
    (slotInsertion fieldValue (pair site axes) Placement.slot1)
    selection Budget.epsilon
    (positiveLinkUpper background radius
      (pair (Periodic.shiftForward (Physical.pairLeft axes) site)
        (Physical.pairRight axes)))
slotSelectedEnvelope background fieldValue (pair site axes)
    Placement.slot2 selection radius =
  inverseFactorEnvelope
    (Physical.link background
      (pair (Periodic.shiftForward (Physical.pairRight axes) site)
        (Physical.pairLeft axes)))
    (slotInsertion fieldValue (pair site axes) Placement.slot2)
    selection Budget.epsilon
    (inverseLinkUpper background radius
      (pair (Periodic.shiftForward (Physical.pairRight axes) site)
        (Physical.pairLeft axes)))
slotSelectedEnvelope background fieldValue (pair site axes)
    Placement.slot3 selection radius =
  inverseFactorEnvelope
    (Physical.link background (pair site (Physical.pairRight axes)))
    (slotInsertion fieldValue (pair site axes) Placement.slot3)
    selection Budget.epsilon
    (inverseLinkUpper background radius
      (pair site (Physical.pairRight axes)))

slotInsertionNorm :
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 →
  Placement.PlaquetteLinkSlot4 → ℚ
slotInsertionNorm fieldValue plaquette slot =
  Norm.normSq (slotInsertion fieldValue plaquette slot)

placementWeightProductExact : ∀ placement n0 n1 n2 n3 →
  selectionWeight (Named.selection0 placement) n0
    * selectionWeight (Named.selection1 placement) n1
    * selectionWeight (Named.selection2 placement) n2
    * selectionWeight (Named.selection3 placement) n3
  ≡ Charges.placementLeftCharge placement n0 n1 n2 n3
      * Charges.placementRightCharge placement n0 n1 n2 n3
placementWeightProductExact Placement.secondAt0 n0 n1 n2 n3 = ℚRing.solve-∀ n0 n1 n2 n3
placementWeightProductExact Placement.secondAt1 n0 n1 n2 n3 = ℚRing.solve-∀ n0 n1 n2 n3
placementWeightProductExact Placement.secondAt2 n0 n1 n2 n3 = ℚRing.solve-∀ n0 n1 n2 n3
placementWeightProductExact Placement.secondAt3 n0 n1 n2 n3 = ℚRing.solve-∀ n0 n1 n2 n3
placementWeightProductExact (Placement.firstFirst Placement.ordered01) n0 n1 n2 n3 = ℚRing.solve-∀ n0 n1 n2 n3
placementWeightProductExact (Placement.firstFirst Placement.ordered10) n0 n1 n2 n3 = ℚRing.solve-∀ n0 n1 n2 n3
placementWeightProductExact (Placement.firstFirst Placement.ordered02) n0 n1 n2 n3 = ℚRing.solve-∀ n0 n1 n2 n3
placementWeightProductExact (Placement.firstFirst Placement.ordered20) n0 n1 n2 n3 = ℚRing.solve-∀ n0 n1 n2 n3
placementWeightProductExact (Placement.firstFirst Placement.ordered03) n0 n1 n2 n3 = ℚRing.solve-∀ n0 n1 n2 n3
placementWeightProductExact (Placement.firstFirst Placement.ordered30) n0 n1 n2 n3 = ℚRing.solve-∀ n0 n1 n2 n3
placementWeightProductExact (Placement.firstFirst Placement.ordered12) n0 n1 n2 n3 = ℚRing.solve-∀ n0 n1 n2 n3
placementWeightProductExact (Placement.firstFirst Placement.ordered21) n0 n1 n2 n3 = ℚRing.solve-∀ n0 n1 n2 n3
placementWeightProductExact (Placement.firstFirst Placement.ordered13) n0 n1 n2 n3 = ℚRing.solve-∀ n0 n1 n2 n3
placementWeightProductExact (Placement.firstFirst Placement.ordered31) n0 n1 n2 n3 = ℚRing.solve-∀ n0 n1 n2 n3
placementWeightProductExact (Placement.firstFirst Placement.ordered23) n0 n1 n2 n3 = ℚRing.solve-∀ n0 n1 n2 n3
placementWeightProductExact (Placement.firstFirst Placement.ordered32) n0 n1 n2 n3 = ℚRing.solve-∀ n0 n1 n2 n3

physicalPlacementEnvelope :
  ∀ background fieldValue plaquette placement →
  Radius.RelaxedInverseLinkRadius background →
  let
    factors = Partition.physicalPlacementSelectedFactors
      background fieldValue plaquette placement
    n0 = slotInsertionNorm fieldValue plaquette Placement.slot0
    n1 = slotInsertionNorm fieldValue plaquette Placement.slot1
    n2 = slotInsertionNorm fieldValue plaquette Placement.slot2
    n3 = slotInsertionNorm fieldValue plaquette Placement.slot3
  in
  Envelope.FourFactorDeepEnvelope
    (Partition.a0 factors) (Partition.a1 factors)
    (Partition.a2 factors) (Partition.a3 factors)
    (Partition.b0 factors) (Partition.b1 factors)
    (Partition.b2 factors) (Partition.b3 factors)
    Budget.epsilon
    (Charges.placementLeftCharge placement n0 n1 n2 n3)
    (Charges.placementRightCharge placement n0 n1 n2 n3)
physicalPlacementEnvelope background fieldValue plaquette placement radius =
  let
    n0 = slotInsertionNorm fieldValue plaquette Placement.slot0
    n1 = slotInsertionNorm fieldValue plaquette Placement.slot1
    n2 = slotInsertionNorm fieldValue plaquette Placement.slot2
    n3 = slotInsertionNorm fieldValue plaquette Placement.slot3
    n0NN = Norm.normSqNonnegative (slotInsertion fieldValue plaquette Placement.slot0)
    n1NN = Norm.normSqNonnegative (slotInsertion fieldValue plaquette Placement.slot1)
    n2NN = Norm.normSqNonnegative (slotInsertion fieldValue plaquette Placement.slot2)
    n3NN = Norm.normSqNonnegative (slotInsertion fieldValue plaquette Placement.slot3)

    e0 = slotSelectedEnvelope background fieldValue plaquette Placement.slot0
      (Named.selection0 placement) radius
    e1 = slotSelectedEnvelope background fieldValue plaquette Placement.slot1
      (Named.selection1 placement) radius
    e2 = slotSelectedEnvelope background fieldValue plaquette Placement.slot2
      (Named.selection2 placement) radius
    e3 = slotSelectedEnvelope background fieldValue plaquette Placement.slot3
      (Named.selection3 placement) radius

    leftNN = Charges.chargeAtNonnegative (Charges.leftSlot placement)
      n0 n1 n2 n3 n0NN n1NN n2NN n3NN
    rightNN = Charges.chargeAtNonnegative (Charges.rightSlot placement)
      n0 n1 n2 n3 n0NN n1NN n2NN n3NN
  in
  record
    { Envelope.w0 = weight e0
    ; Envelope.w1 = weight e1
    ; Envelope.w2 = weight e2
    ; Envelope.w3 = weight e3
    ; Envelope.epsilonNonnegative =
        Norm.scaleNonnegative (+ 2 / 1)
          (ℚP.nonNegative⁻¹ (+ 2 / 1))
          (ℚP.<⇒≤ Signed.rhoPositive)
    ; Envelope.leftChargeNonnegative = leftNN
    ; Envelope.rightChargeNonnegative = rightNN
    ; Envelope.w0Nonnegative = weightNonnegative e0
    ; Envelope.w1Nonnegative = weightNonnegative e1
    ; Envelope.w2Nonnegative = weightNonnegative e2
    ; Envelope.w3Nonnegative = weightNonnegative e3
    ; Envelope.baseNorm0 = flatNormExact e0
    ; Envelope.baseNorm1 = flatNormExact e1
    ; Envelope.baseNorm2 = flatNormExact e2
    ; Envelope.baseNorm3 = flatNormExact e3
    ; Envelope.defectNorm0 = defectNormUpper e0
    ; Envelope.defectNorm1 = defectNormUpper e1
    ; Envelope.defectNorm2 = defectNormUpper e2
    ; Envelope.defectNorm3 = defectNormUpper e3
    ; Envelope.weightProductExact = placementWeightProductExact placement n0 n1 n2 n3
    }

physicalSelectedFactorEnvelopeLevel : ProofLevel
physicalSelectedFactorEnvelopeLevel = machineChecked
