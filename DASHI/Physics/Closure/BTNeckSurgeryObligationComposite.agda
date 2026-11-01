module DASHI.Physics.Closure.BTNeckSurgeryObligationComposite where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.BTCanonicalNeckAnalogue as BT
import DASHI.Physics.Closure.SurgeryCanonicalNeighborhoodObligationLadder as Ladder
import DASHI.Physics.Closure.SurgeryCanonicalNeighborhoodObstruction as Surgery

------------------------------------------------------------------------
-- Finite BT neck to surgery-obligation crosswalk.
--
-- Each canonical p = 2, 3, 7 BT neck row supplies finite cross-section
-- cardinality and path-cylinder evidence.  The smooth S2 cross-section,
-- smooth epsilon-neck theorem, and surgery continuation obligations remain
-- explicitly undischarged.

canonicalBTNeckSurgeryObligations :
  List Surgery.SurgeryObligation
canonicalBTNeckSurgeryObligations =
  Surgery.requireSmoothEpsilonNeckModel
  ∷ Surgery.requireSurgeryContinuationLaw
  ∷ Surgery.retainDiscreteShellOnlyStatus
  ∷ []

canonicalBTNeckSurgeryStatus :
  Ladder.LadderPromotionStatus
canonicalBTNeckSurgeryStatus =
  Ladder.finiteAnalogueConstructedSmoothTargetBlocked

record BTNeckSurgeryObligationCompositeRow : Set where
  field
    analogue :
      BT.BTCanonicalNeckAnalogue

    pValue :
      Nat

    pValueIsAnaloguePValue :
      pValue ≡ BT.pValue analogue

    crossSectionCardinality :
      Nat

    crossSectionCardinalityIsAnalogueCardinality :
      crossSectionCardinality ≡ BT.crossSectionCardinality analogue

    crossSectionCardinalityIsPPlusOne :
      BT.crossSectionCardinality analogue
      ≡
      BT.crossSectionCardinalityForLane (BT.primeLane analogue)

    pathCylinderConstructed :
      Bool

    pathCylinderConstructedIsTrue :
      pathCylinderConstructed ≡ true

    smoothS2CrossSectionConstructed :
      Bool

    smoothS2CrossSectionConstructedIsFalse :
      smoothS2CrossSectionConstructed ≡ false

    epsilonNeckTheoremConstructed :
      Bool

    epsilonNeckTheoremConstructedIsFalse :
      epsilonNeckTheoremConstructed ≡ false

    associatedSmoothObligations :
      List Surgery.SurgeryObligation

    associatedSmoothObligationsAreCanonical :
      associatedSmoothObligations ≡ canonicalBTNeckSurgeryObligations

    associatedSmoothObligationStatus :
      Ladder.LadderPromotionStatus

    associatedSmoothObligationStatusIsCanonical :
      associatedSmoothObligationStatus ≡ canonicalBTNeckSurgeryStatus

    rowStatement :
      String

open BTNeckSurgeryObligationCompositeRow public

rowForAnalogue :
  BT.BTCanonicalNeckAnalogue →
  BTNeckSurgeryObligationCompositeRow
rowForAnalogue analogue =
  record
    { analogue =
        analogue
    ; pValue =
        BT.pValue analogue
    ; pValueIsAnaloguePValue =
        refl
    ; crossSectionCardinality =
        BT.crossSectionCardinality analogue
    ; crossSectionCardinalityIsAnalogueCardinality =
        refl
    ; crossSectionCardinalityIsPPlusOne =
        BT.crossSectionCardinalityIsPPlusOne analogue
    ; pathCylinderConstructed =
        BT.pathCylinderAnalogueConstructed analogue
    ; pathCylinderConstructedIsTrue =
        BT.pathCylinderAnalogueConstructedIsTrue analogue
    ; smoothS2CrossSectionConstructed =
        BT.smoothS2CrossSectionPromoted analogue
    ; smoothS2CrossSectionConstructedIsFalse =
        BT.smoothS2CrossSectionPromotedIsFalse analogue
    ; epsilonNeckTheoremConstructed =
        BT.epsilonNeckTheoremPromoted analogue
    ; epsilonNeckTheoremConstructedIsFalse =
        BT.epsilonNeckTheoremPromotedIsFalse analogue
    ; associatedSmoothObligations =
        canonicalBTNeckSurgeryObligations
    ; associatedSmoothObligationsAreCanonical =
        refl
    ; associatedSmoothObligationStatus =
        canonicalBTNeckSurgeryStatus
    ; associatedSmoothObligationStatusIsCanonical =
        refl
    ; rowStatement =
        "Finite BT neck evidence is crosswalked to the surgery obligation ladder without discharging smooth S2, smooth epsilon-neck, or surgery-continuation obligations."
    }

p2BTNeckSurgeryObligationCompositeRow :
  BTNeckSurgeryObligationCompositeRow
p2BTNeckSurgeryObligationCompositeRow =
  rowForAnalogue BT.canonicalP2BTNeckAnalogue

p3BTNeckSurgeryObligationCompositeRow :
  BTNeckSurgeryObligationCompositeRow
p3BTNeckSurgeryObligationCompositeRow =
  rowForAnalogue BT.canonicalP3BTNeckAnalogue

p7BTNeckSurgeryObligationCompositeRow :
  BTNeckSurgeryObligationCompositeRow
p7BTNeckSurgeryObligationCompositeRow =
  rowForAnalogue BT.canonicalP7BTNeckAnalogue

canonicalBTNeckSurgeryObligationCompositeRows :
  List BTNeckSurgeryObligationCompositeRow
canonicalBTNeckSurgeryObligationCompositeRows =
  p2BTNeckSurgeryObligationCompositeRow
  ∷ p3BTNeckSurgeryObligationCompositeRow
  ∷ p7BTNeckSurgeryObligationCompositeRow
  ∷ []

record BTNeckSurgeryObligationComposite : Set where
  field
    rows :
      List BTNeckSurgeryObligationCompositeRow

    rowsAreCanonical :
      rows ≡ canonicalBTNeckSurgeryObligationCompositeRows

    smoothObligations :
      List Surgery.SurgeryObligation

    smoothObligationsAreCanonical :
      smoothObligations ≡ canonicalBTNeckSurgeryObligations

    smoothObligationStatus :
      Ladder.LadderPromotionStatus

    smoothObligationStatusIsCanonical :
      smoothObligationStatus ≡ canonicalBTNeckSurgeryStatus

    compositeStatement :
      String

open BTNeckSurgeryObligationComposite public

canonicalBTNeckSurgeryObligationComposite :
  BTNeckSurgeryObligationComposite
canonicalBTNeckSurgeryObligationComposite =
  record
    { rows =
        canonicalBTNeckSurgeryObligationCompositeRows
    ; rowsAreCanonical =
        refl
    ; smoothObligations =
        canonicalBTNeckSurgeryObligations
    ; smoothObligationsAreCanonical =
        refl
    ; smoothObligationStatus =
        canonicalBTNeckSurgeryStatus
    ; smoothObligationStatusIsCanonical =
        refl
    ; compositeStatement =
        "Canonical p=2,3,7 BT neck rows have finite path-cylinder evidence only; the associated surgery ladder remains blocked at smooth epsilon-neck and continuation obligations."
    }

p2CrossSectionCardinalityIs3 :
  crossSectionCardinality p2BTNeckSurgeryObligationCompositeRow ≡ 3
p2CrossSectionCardinalityIs3 =
  refl

p3CrossSectionCardinalityIs4 :
  crossSectionCardinality p3BTNeckSurgeryObligationCompositeRow ≡ 4
p3CrossSectionCardinalityIs4 =
  refl

p7CrossSectionCardinalityIs8 :
  crossSectionCardinality p7BTNeckSurgeryObligationCompositeRow ≡ 8
p7CrossSectionCardinalityIs8 =
  refl

p2PathCylinderConstructedIsTrue :
  pathCylinderConstructed p2BTNeckSurgeryObligationCompositeRow ≡ true
p2PathCylinderConstructedIsTrue =
  refl

p3PathCylinderConstructedIsTrue :
  pathCylinderConstructed p3BTNeckSurgeryObligationCompositeRow ≡ true
p3PathCylinderConstructedIsTrue =
  refl

p7PathCylinderConstructedIsTrue :
  pathCylinderConstructed p7BTNeckSurgeryObligationCompositeRow ≡ true
p7PathCylinderConstructedIsTrue =
  refl

p2SmoothS2ConstructedIsFalse :
  smoothS2CrossSectionConstructed p2BTNeckSurgeryObligationCompositeRow
  ≡
  false
p2SmoothS2ConstructedIsFalse =
  refl

p3SmoothS2ConstructedIsFalse :
  smoothS2CrossSectionConstructed p3BTNeckSurgeryObligationCompositeRow
  ≡
  false
p3SmoothS2ConstructedIsFalse =
  refl

p7SmoothS2ConstructedIsFalse :
  smoothS2CrossSectionConstructed p7BTNeckSurgeryObligationCompositeRow
  ≡
  false
p7SmoothS2ConstructedIsFalse =
  refl

p2EpsilonNeckTheoremConstructedIsFalse :
  epsilonNeckTheoremConstructed p2BTNeckSurgeryObligationCompositeRow
  ≡
  false
p2EpsilonNeckTheoremConstructedIsFalse =
  refl

p3EpsilonNeckTheoremConstructedIsFalse :
  epsilonNeckTheoremConstructed p3BTNeckSurgeryObligationCompositeRow
  ≡
  false
p3EpsilonNeckTheoremConstructedIsFalse =
  refl

p7EpsilonNeckTheoremConstructedIsFalse :
  epsilonNeckTheoremConstructed p7BTNeckSurgeryObligationCompositeRow
  ≡
  false
p7EpsilonNeckTheoremConstructedIsFalse =
  refl

p2SmoothObligationsWitness :
  associatedSmoothObligations p2BTNeckSurgeryObligationCompositeRow
  ≡
  canonicalBTNeckSurgeryObligations
p2SmoothObligationsWitness =
  refl

p3SmoothObligationsWitness :
  associatedSmoothObligations p3BTNeckSurgeryObligationCompositeRow
  ≡
  canonicalBTNeckSurgeryObligations
p3SmoothObligationsWitness =
  refl

p7SmoothObligationsWitness :
  associatedSmoothObligations p7BTNeckSurgeryObligationCompositeRow
  ≡
  canonicalBTNeckSurgeryObligations
p7SmoothObligationsWitness =
  refl

p2SmoothStatusWitness :
  associatedSmoothObligationStatus p2BTNeckSurgeryObligationCompositeRow
  ≡
  Ladder.finiteAnalogueConstructedSmoothTargetBlocked
p2SmoothStatusWitness =
  refl

p3SmoothStatusWitness :
  associatedSmoothObligationStatus p3BTNeckSurgeryObligationCompositeRow
  ≡
  Ladder.finiteAnalogueConstructedSmoothTargetBlocked
p3SmoothStatusWitness =
  refl

p7SmoothStatusWitness :
  associatedSmoothObligationStatus p7BTNeckSurgeryObligationCompositeRow
  ≡
  Ladder.finiteAnalogueConstructedSmoothTargetBlocked
p7SmoothStatusWitness =
  refl
