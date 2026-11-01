module DASHI.Moonshine.OggSSPP2F4EllipticVOAS3ActionRecognitionCutsetExact where

------------------------------------------------------------------------
-- SAME-ACTION RECOGNITION CUT: ACTUAL E(F4) S3 VS MONSTER-3B VOA
--
-- The elliptic shear rho(x,y)=(zeta_F4*x,y) and F4 Frobenius are
-- SOURCE-NATIVE actions on the nine rational elliptic points.
--
-- Separately, the existing Moonshine owner acts on a literal graded VOA
-- carrier by a selected central element and its normalizer.
--
-- A proposed comparison MUST provide a common-action intertwiner:
--   curve rho  -> selected central action
--   curve F    -> a selected normalizer inverter.
-- It does not identify char-2 field zeta_F4 with characteristic-zero
-- cyclotomic scalars, or identify elliptic S3 with Monster 3B.
--
-- The record below is a genuine uninhabited recognition obligation, not
-- an intentionally empty proposition masquerading as a no-go proof.
-- Its consequence checks the F*rho*F=rho^2 square on the SAME VOA states.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Moonshine.GradedRepresentation as GR
import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA
import DASHI.Moonshine.Base369Monster3BVOAActionPhaseAdapterBidiExact as Adapter
import DASHI.Moonshine.OggSSPP2F4ZetaCurvePointEnumerationExact as Curve
import DASHI.Moonshine.OggSSPP2F4EllipticS3NineSheetBidiExact as Elliptic

record EllipticToLiteralVOAS3Intertwiner
    {G K : Set}
    {group : GR.Group G}
    (source : Adapter.ActualMonster3BVOAPhaseActionSource G K group)
    : Setω where
  field
    normalizerInverter : G

    normalizerReallyInvertsSelectedCentral :
      Adapter.preservesOrInverts source normalizerInverter ≡ false

    stateMap :
      Curve.RationalF4Point →
      Adapter.VOACarrier (Adapter.bridge source)

    shearIntertwinesSelectedCentral :
      (p : Curve.RationalF4Point) →
      stateMap (Elliptic.rhoCurve p)
      ≡
      VOA.VOAGroupAction.act
        (VOA.monsterAction (Adapter.bridge source))
        (Adapter.centralElement source)
        (stateMap p)

    frobeniusIntertwinesNormalizerInverter :
      (p : Curve.RationalF4Point) →
      stateMap (Curve.frobeniusRational p)
      ≡
      VOA.VOAGroupAction.act
        (VOA.monsterAction (Adapter.bridge source))
        normalizerInverter
        (stateMap p)

open EllipticToLiteralVOAS3Intertwiner public

module Consequences
    {G K : Set}
    {group : GR.Group G}
    (source : Adapter.ActualMonster3BVOAPhaseActionSource G K group)
    (comparison : EllipticToLiteralVOAS3Intertwiner source)
    where

  Carrier : Set
  Carrier = Adapter.VOACarrier (Adapter.bridge source)

  centralAct : Carrier → Carrier
  centralAct =
    VOA.VOAGroupAction.act
      (VOA.monsterAction (Adapter.bridge source))
      (Adapter.centralElement source)

  normalizerAct : Carrier → Carrier
  normalizerAct =
    VOA.VOAGroupAction.act
      (VOA.monsterAction (Adapter.bridge source))
      (normalizerInverter comparison)

  -- This is supplied by the independent actual VOA normalizer source,
  -- not by a numerical orbit comparison or elliptic group labels.
  selectedCentralConjugationSource :
    (state : Carrier) →
    centralAct (normalizerAct state)
    ≡
    normalizerAct
      (VOA.VOAGroupAction.act
        (VOA.monsterAction (Adapter.bridge source))
        (Adapter.centralInverseElement source)
        state)
  selectedCentralConjugationSource state =
    Adapter.invertingIntertwiner source
      (normalizerInverter comparison)
      (normalizerReallyInvertsSelectedCentral comparison)
      state

  -- Consequence of the TWO individually required intertwining squares:
  -- the source F rho F relation transports to the same literal VOA states.
  transportedS3Relation :
    (p : Curve.RationalF4Point) →
    normalizerAct
      (centralAct (normalizerAct (stateMap comparison p)))
    ≡
    centralAct (centralAct (stateMap comparison p))
  transportedS3Relation p =
    trans
      (cong
        (λ state → normalizerAct (centralAct state))
        (sym (frobeniusIntertwinesNormalizerInverter comparison p)))
      (trans
        (cong normalizerAct
          (sym (shearIntertwinesSelectedCentral comparison
            (Curve.frobeniusRational p))))
        (trans
          (sym (frobeniusIntertwinesNormalizerInverter comparison
            (Elliptic.rhoCurve (Curve.frobeniusRational p))))
          (trans
            (cong (stateMap comparison)
              (Elliptic.frobeniusConjugatesRho p))
            (trans
              (shearIntertwinesSelectedCentral comparison
                (Elliptic.rhoCurve p))
              (cong centralAct
                (shearIntertwinesSelectedCentral comparison p))))))

record EllipticVOAS3RecognitionBoundary : Set where
  constructor elliptic-voa-s3-recognition-boundary
  field
    sourceArithmeticFrobeniusAndShearReused : Bool
    literalVOAGroupActionReused : Bool
    selectedCentralAndInverseKeptDistinct : Bool
    actualNormalizerInversionReceiptRequired : Bool
    commonStateActionIntertwinerRequired : Bool
    sameVOAStateS3WordTransportCompiler : Bool
    ellipticF4ZetaEquatedWithComplexCyclotomicZeta : Bool
    selectedVOAActionIntertwinerInhabitedHere : Bool
    monsterValuationMechanismProvedHere : Bool

canonicalEllipticVOAS3RecognitionBoundary :
  EllipticVOAS3RecognitionBoundary
canonicalEllipticVOAS3RecognitionBoundary =
  elliptic-voa-s3-recognition-boundary
    true true true true true true false false false
