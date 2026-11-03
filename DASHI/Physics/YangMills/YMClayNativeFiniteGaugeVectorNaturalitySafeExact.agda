{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayNativeFiniteGaugeVectorNaturalitySafeExact where

------------------------------------------------------------------------
-- R443: assumption-free FINITE original-bond gauge naturality.
--
-- The only parameters are (1) the finite periodic side, (2) an actual
-- group with associativity, and (3) the original positive-bond target
-- function. No Haar integral, real scalar, continuum limit, or physics
-- source is required. This deliberately separates the truly Golden
-- finite proof from RealAnalysisAxioms / compact Lie standard authorities.
--
-- Original geometry: BalabanPeriodicTorus4Carrier.
-- Canonical duplicate-free bond indexing:
--   YMClayNativePositiveBondEnumerationVectorExact.
-- Group action: Wilson's source/target link convention.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Agda.Builtin.List as List
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.YangMills.CompactLieGroupCore as Core
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec

module _
    {Link : Set}
    (L : Nat)
    (group : Core.Group Link)
    (target : Torus.PositiveBond L → Torus.periodicTorus4Definition L)
  where

  Site : Set
  Site = Torus.periodicTorus4Definition L

  Bond : Set
  Bond = Torus.PositiveBond L

  Gauge : Set
  Gauge = Site → Link

  Vector : Set
  Vector = Vec.Vec Link (Codec.originalPositiveBondCount L)

  encode : Torus.BondField L Link → Vector
  encode = Codec.encodeOriginalBonds L

  decode : Vector → Torus.BondField L Link
  decode = Codec.decodeOriginalBonds L

  leftField : Gauge → Torus.BondField L Link
  leftField gamma bond = gamma (Torus.first bond)

  rightField : Gauge → Torus.BondField L Link
  rightField gamma bond =
    Core.inverse group (gamma (target bond))

  leftVector : Gauge → Vector
  leftVector gamma = encode (leftField gamma)

  rightVector : Gauge → Vector
  rightVector gamma = encode (rightField gamma)

  singleGauge : Link → Link → Link → Link
  singleGauge left right U =
    Core.multiply group left (Core.multiply group U right)

  vectorGauge :
    ∀ {count} →
    Vec.Vec Link count → Vec.Vec Link count →
    Vec.Vec Link count → Vec.Vec Link count
  vectorGauge Vec.[] Vec.[] Vec.[] = Vec.[]
  vectorGauge (left Vec.∷ lefts) (right Vec.∷ rights)
      (U Vec.∷ values) =
    singleGauge left right U Vec.∷
      vectorGauge lefts rights values

  -- The original Wilson bond transform uses left association.
  -- The one-link bilateral Haar action uses right association.
  originalGauge :
    Gauge → Torus.BondField L Link → Torus.BondField L Link
  originalGauge gamma field bond =
    Core.multiply group
      (Core.multiply group (leftField gamma bond) (field bond))
      (rightField gamma bond)

  vectorGaugeListNaturality :
    ∀ {A : Set}
      (labels : List.List A)
      (left right field : A → Link) →
    vectorGauge
      (Codec.listValues labels left)
      (Codec.listValues labels right)
      (Codec.listValues labels field)
    ≡
    Codec.listValues labels
      (λ label →
        singleGauge (left label) (right label) (field label))
  vectorGaugeListNaturality List.[] left right field = refl
  vectorGaugeListNaturality (List._∷_ label labels) left right field =
    cong
      (Vec._∷_ (singleGauge
        (left label) (right label) (field label)))
      (vectorGaugeListNaturality labels left right field)

  vectorGaugeEncoded :
    ∀ gamma vector →
    vectorGauge (leftVector gamma) (rightVector gamma) vector
    ≡
    encode
      (λ bond →
        singleGauge
          (leftField gamma bond)
          (rightField gamma bond)
          (decode vector bond))
  vectorGaugeEncoded gamma vector =
    trans
      (cong
        (λ selected →
          vectorGauge (leftVector gamma) (rightVector gamma) selected)
        (sym (Codec.originalBondsEncodeDecodeExactly L vector)))
      (vectorGaugeListNaturality
        (Torus.elements (Codec.originalPositiveBondFinite L))
        (leftField gamma) (rightField gamma) (decode vector))

  vectorGaugeDecodedAt :
    ∀ gamma vector bond →
    decode
      (vectorGauge (leftVector gamma) (rightVector gamma) vector)
      bond
    ≡
    singleGauge
      (leftField gamma bond)
      (rightField gamma bond)
      (decode vector bond)
  vectorGaugeDecodedAt gamma vector bond =
    trans
      (cong (λ selected → decode selected bond)
        (vectorGaugeEncoded gamma vector))
      (Codec.originalBondsDecodeEncodeAt L
        (λ label →
          singleGauge
            (leftField gamma label)
            (rightField gamma label)
            (decode vector label))
        bond)

  -- The same ORIGINAL field, not a freely assumed action equality.
  originalGaugeDecodedAt :
    ∀ gamma vector bond →
    originalGauge gamma (decode vector) bond
    ≡
    decode
      (vectorGauge (leftVector gamma) (rightVector gamma) vector)
      bond
  originalGaugeDecodedAt gamma vector bond =
    trans
      (Core.multiplyAssociative group
        (leftField gamma bond)
        (decode vector bond)
        (rightField gamma bond))
      (sym (vectorGaugeDecodedAt gamma vector bond))

  -- Native gauge covariance of the encoded field is a consequence of
  -- the actual codec and group laws, without any global function axiom.
  encodeGaugeNatural :
    ∀ gamma vector →
    encode (originalGauge gamma (decode vector))
    ≡
    vectorGauge (leftVector gamma) (rightVector gamma) vector
  encodeGaugeNatural gamma vector =
    Codec.vecPointwiseEquality
      (λ index →
        trans
          (Codec.listValuesAt
            (Torus.elements (Codec.originalPositiveBondFinite L))
            (originalGauge gamma (decode vector)) index)
          (trans
            (originalGaugeDecodedAt gamma vector
              (Codec.listAt
                (Torus.elements (Codec.originalPositiveBondFinite L))
                index))
            (sym
              (Codec.listValuesAt
                (Torus.elements (Codec.originalPositiveBondFinite L))
                (decode
                  (vectorGauge
                    (leftVector gamma) (rightVector gamma) vector))
                index))))
