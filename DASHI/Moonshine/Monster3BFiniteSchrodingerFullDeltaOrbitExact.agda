module DASHI.Moonshine.Monster3BFiniteSchrodingerFullDeltaOrbitExact where

------------------------------------------------------------------------
-- FULL DELTA ORBIT ON X6 FROM THE SIX EXISTING UNIT TRANSLATIONS
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl; trans)
open import Relation.Binary.PropositionalEquality using (sym)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteSchrodingerFunctionModuleExact as V
import DASHI.Moonshine.Monster3BFiniteSchrodingerDeltaExtractionExact as Extract
import DASHI.Moonshine.Monster3BFiniteSchrodingerBooleanDeltaExact as Boolean
import DASHI.Moonshine.Monster3BFiniteSchrodingerTranslationOrbitExact as Orbit

translationActionRespectsPointwise :
  (axis : H.Axis6) {f g : V.SchrodingerFunction} →
  V.PointwiseEqual f g →
  V.PointwiseEqual (V.translationAction axis f) (V.translationAction axis g)
translationActionRespectsPointwise axis equal x =
  equal (H.translateInverse axis x)

translateWordRespectsPointwise :
  (shift : Trit) (axis : H.Axis6) {f g : V.SchrodingerFunction} →
  V.PointwiseEqual f g →
  V.PointwiseEqual
    (Orbit.translateWord shift axis f)
    (Orbit.translateWord shift axis g)
translateWordRespectsPointwise zer axis equal = equal
translateWordRespectsPointwise pos axis equal =
  translationActionRespectsPointwise axis equal
translateWordRespectsPointwise neg axis equal =
  translationActionRespectsPointwise axis
    (translationActionRespectsPointwise axis equal)

wordPoint : Trit → H.Axis6 → H.X6 → H.X6
wordPoint zer axis selected = selected
wordPoint pos axis selected = H.translate axis selected
wordPoint neg axis selected = H.translate axis (H.translate axis selected)

translateWordCarriesBooleanDelta :
  (shift : Trit) (axis : H.Axis6) (selected : H.X6) →
  V.PointwiseEqual
    (Orbit.translateWord shift axis (Boolean.booleanDelta selected))
    (Boolean.booleanDelta (wordPoint shift axis selected))
translateWordCarriesBooleanDelta zer axis selected x = refl
translateWordCarriesBooleanDelta pos axis selected =
  Boolean.unitTranslationCarriesBooleanDeltaPointwise axis selected
translateWordCarriesBooleanDelta neg axis selected x =
  trans
    (translationActionRespectsPointwise axis
      (Boolean.unitTranslationCarriesBooleanDeltaPointwise axis selected) x)
    (Boolean.unitTranslationCarriesBooleanDeltaPointwise
      axis (H.translate axis selected) x)

generatedPoint : H.X6 → H.X6 → H.X6
generatedPoint (H.x6 s0 s1 s2 s3 s4 s5) selected =
  wordPoint s5 H.axis5
    (wordPoint s4 H.axis4
      (wordPoint s3 H.axis3
        (wordPoint s2 H.axis2
          (wordPoint s1 H.axis1
            (wordPoint s0 H.axis0 selected)))))

generatedTranslationCarriesBooleanDelta :
  (shift selected : H.X6) →
  V.PointwiseEqual
    (Orbit.generatedTranslation shift (Boolean.booleanDelta selected))
    (Boolean.booleanDelta (generatedPoint shift selected))
generatedTranslationCarriesBooleanDelta
    (H.x6 s0 s1 s2 s3 s4 s5) selected x =
  let
    e0 = translateWordCarriesBooleanDelta s0 H.axis0 selected
    p0 = wordPoint s0 H.axis0 selected
    e1 = translateWordCarriesBooleanDelta s1 H.axis1 p0
    p1 = wordPoint s1 H.axis1 p0
    e2 = translateWordCarriesBooleanDelta s2 H.axis2 p1
    p2 = wordPoint s2 H.axis2 p1
    e3 = translateWordCarriesBooleanDelta s3 H.axis3 p2
    p3 = wordPoint s3 H.axis3 p2
    e4 = translateWordCarriesBooleanDelta s4 H.axis4 p3
    p4 = wordPoint s4 H.axis4 p3
    e5 = translateWordCarriesBooleanDelta s5 H.axis5 p4
  in
  trans
    (translateWordRespectsPointwise s5 H.axis5
      (translateWordRespectsPointwise s4 H.axis4
        (translateWordRespectsPointwise s3 H.axis3
          (translateWordRespectsPointwise s2 H.axis2
            (translateWordRespectsPointwise s1 H.axis1 e0)))) x)
    (trans
      (translateWordRespectsPointwise s5 H.axis5
        (translateWordRespectsPointwise s4 H.axis4
          (translateWordRespectsPointwise s3 H.axis3
            (translateWordRespectsPointwise s2 H.axis2 e1))) x)
      (trans
        (translateWordRespectsPointwise s5 H.axis5
          (translateWordRespectsPointwise s4 H.axis4
            (translateWordRespectsPointwise s3 H.axis3 e2)) x)
        (trans
          (translateWordRespectsPointwise s5 H.axis5
            (translateWordRespectsPointwise s4 H.axis4 e3) x)
          (trans
            (translateWordRespectsPointwise s5 H.axis5 e4 x)
            (e5 x)))))

wordPointAxis0 : (s : Trit) (x : H.X6) →
  wordPoint s H.axis0 x ≡
  H.x6 (Orbit.shiftTrit s (H.x0 x)) (H.x1 x) (H.x2 x)
       (H.x3 x) (H.x4 x) (H.x5 x)
wordPointAxis0 zer (H.x6 a0 a1 a2 a3 a4 a5) = refl
wordPointAxis0 pos (H.x6 a0 a1 a2 a3 a4 a5) = refl
wordPointAxis0 neg (H.x6 a0 a1 a2 a3 a4 a5) = refl

wordPointAxis1 : (s : Trit) (x : H.X6) →
  wordPoint s H.axis1 x ≡
  H.x6 (H.x0 x) (Orbit.shiftTrit s (H.x1 x)) (H.x2 x)
       (H.x3 x) (H.x4 x) (H.x5 x)
wordPointAxis1 zer (H.x6 a0 a1 a2 a3 a4 a5) = refl
wordPointAxis1 pos (H.x6 a0 a1 a2 a3 a4 a5) = refl
wordPointAxis1 neg (H.x6 a0 a1 a2 a3 a4 a5) = refl

wordPointAxis2 : (s : Trit) (x : H.X6) →
  wordPoint s H.axis2 x ≡
  H.x6 (H.x0 x) (H.x1 x) (Orbit.shiftTrit s (H.x2 x))
       (H.x3 x) (H.x4 x) (H.x5 x)
wordPointAxis2 zer (H.x6 a0 a1 a2 a3 a4 a5) = refl
wordPointAxis2 pos (H.x6 a0 a1 a2 a3 a4 a5) = refl
wordPointAxis2 neg (H.x6 a0 a1 a2 a3 a4 a5) = refl

wordPointAxis3 : (s : Trit) (x : H.X6) →
  wordPoint s H.axis3 x ≡
  H.x6 (H.x0 x) (H.x1 x) (H.x2 x)
       (Orbit.shiftTrit s (H.x3 x)) (H.x4 x) (H.x5 x)
wordPointAxis3 zer (H.x6 a0 a1 a2 a3 a4 a5) = refl
wordPointAxis3 pos (H.x6 a0 a1 a2 a3 a4 a5) = refl
wordPointAxis3 neg (H.x6 a0 a1 a2 a3 a4 a5) = refl

wordPointAxis4 : (s : Trit) (x : H.X6) →
  wordPoint s H.axis4 x ≡
  H.x6 (H.x0 x) (H.x1 x) (H.x2 x) (H.x3 x)
       (Orbit.shiftTrit s (H.x4 x)) (H.x5 x)
wordPointAxis4 zer (H.x6 a0 a1 a2 a3 a4 a5) = refl
wordPointAxis4 pos (H.x6 a0 a1 a2 a3 a4 a5) = refl
wordPointAxis4 neg (H.x6 a0 a1 a2 a3 a4 a5) = refl

wordPointAxis5 : (s : Trit) (x : H.X6) →
  wordPoint s H.axis5 x ≡
  H.x6 (H.x0 x) (H.x1 x) (H.x2 x) (H.x3 x) (H.x4 x)
       (Orbit.shiftTrit s (H.x5 x))
wordPointAxis5 zer (H.x6 a0 a1 a2 a3 a4 a5) = refl
wordPointAxis5 pos (H.x6 a0 a1 a2 a3 a4 a5) = refl
wordPointAxis5 neg (H.x6 a0 a1 a2 a3 a4 a5) = refl

generatedPointIsShiftPoint :
  (shift selected : H.X6) →
  generatedPoint shift selected ≡ Orbit.shiftPoint shift selected
generatedPointIsShiftPoint
    (H.x6 s0 s1 s2 s3 s4 s5)
    (H.x6 x0 x1 x2 x3 x4 x5)
  rewrite wordPointAxis0 s0 (H.x6 x0 x1 x2 x3 x4 x5)
        | wordPointAxis1 s1 _
        | wordPointAxis2 s2 _
        | wordPointAxis3 s3 _
        | wordPointAxis4 s4 _
        | wordPointAxis5 s5 _ = refl

canonicalGeneratedActionCarriesBooleanDelta :
  (source target : H.X6) →
  V.PointwiseEqual
    (Orbit.generatedTranslation (Orbit.shiftFromTo source target)
      (Boolean.booleanDelta source))
    (Boolean.booleanDelta target)
canonicalGeneratedActionCarriesBooleanDelta source target x =
  trans
    (generatedTranslationCarriesBooleanDelta
      (Orbit.shiftFromTo source target) source x)
    (congBooleanDeltaAt
      (generatedPointIsShiftPoint (Orbit.shiftFromTo source target) source)
      (Orbit.shiftFromToRestores source target) x)
  where
  congBooleanDeltaAt :
    ∀ {a b c : H.X6} → a ≡ b → b ≡ c →
    (x : H.X6) → Boolean.booleanDelta a x ≡ Boolean.booleanDelta c x
  congBooleanDeltaAt refl refl x = refl

canonicalDeltaTransportReceipt :
  (source target : H.X6) → Orbit.GeneratedDeltaTransportReceipt source target
canonicalDeltaTransportReceipt source target =
  Orbit.generated-delta-transport-receipt
    (Orbit.shiftFromTo source target)
    (Orbit.shiftFromToRestores source target)
    (λ x →
      trans
        (translationOnComparisonToBoolean source target x)
        (trans
          (canonicalGeneratedActionCarriesBooleanDelta source target x)
          (BooleanDeltaToComparison target x)))
  where
  generatedTranslationRespectsPointwise :
    (shift : H.X6) {f g : V.SchrodingerFunction} →
    V.PointwiseEqual f g →
    V.PointwiseEqual
      (Orbit.generatedTranslation shift f)
      (Orbit.generatedTranslation shift g)
  generatedTranslationRespectsPointwise
      (H.x6 s0 s1 s2 s3 s4 s5) equal =
    translateWordRespectsPointwise s5 H.axis5
      (translateWordRespectsPointwise s4 H.axis4
        (translateWordRespectsPointwise s3 H.axis3
          (translateWordRespectsPointwise s2 H.axis2
            (translateWordRespectsPointwise s1 H.axis1
              (translateWordRespectsPointwise s0 H.axis0 equal)))))

  translationOnComparisonToBoolean :
    (source target x : H.X6) →
    Orbit.generatedTranslation (Orbit.shiftFromTo source target)
      (Extract.comparisonDelta source) x
    ≡ Orbit.generatedTranslation (Orbit.shiftFromTo source target)
      (Boolean.booleanDelta source) x
  translationOnComparisonToBoolean source target x =
    generatedTranslationRespectsPointwise
      (Orbit.shiftFromTo source target)
      (Boolean.comparisonDeltaIsBooleanDelta source) x

  BooleanDeltaToComparison :
    (target x : H.X6) →
    Boolean.booleanDelta target x ≡ Extract.comparisonDelta target x
  BooleanDeltaToComparison target x =
    sym (Boolean.comparisonDeltaIsBooleanDelta target x)

allDeltaOrbitMember :
  ∀ {Member}
    (inv : V.HeisenbergInvariantSubspace Member) →
    (source target : H.X6) →
    Member (Extract.comparisonDelta source) →
    Member (Extract.comparisonDelta target)
allDeltaOrbitMember inv source target sourceMember =
  Orbit.transportedDeltaMember inv source target sourceMember
    (canonicalDeltaTransportReceipt source target)

record FullDeltaOrbitBoundary : Set where
  constructor full-delta-orbit-boundary
  field
    generatedActionDeltaTransportClosed : Bool
    canonicalSourceTargetReceiptConstructed : Bool
    allDeltaOrbitMembershipClosed : Bool
    arbitraryPermutationClosureUsed : Bool
open FullDeltaOrbitBoundary public

canonicalFullDeltaOrbitBoundary : FullDeltaOrbitBoundary
canonicalFullDeltaOrbitBoundary =
  full-delta-orbit-boundary true true true false
