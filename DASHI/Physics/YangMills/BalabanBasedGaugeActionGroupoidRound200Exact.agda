{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanBasedGaugeActionGroupoidRound200Exact where

------------------------------------------------------------------------
-- ROUND200 X-POLLINATION: THE EXISTING BASED GAUGE ACTION AS A PROOF-RELEVANT
-- GROUPOID.
--
-- R196/R199 use actual gauge-action arrows rather than an opaque quotient
-- relation.  The older action owner proves based freeness but does not expose
-- composition/inversion of arrows.  Prove those laws once from the literal
-- pointwise gauge transformation and the exact group laws.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
open import DASHI.Physics.YangMills.BalabanPeriodicLatticeBonds using (source; target)
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Transport
import DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance as Covariance
import DASHI.Physics.YangMills.BalabanBasedGaugeActionFreeExact as Free

rightInverseUnique :
  (group : Transport.GroupStructure) → ∀ a b →
  Transport.multiply group a b ≡ Transport.unit group →
  b ≡ Transport.inverse group a
rightInverseUnique group a b rightInverse =
  trans
    (sym (Transport.unitLeft group b))
    (trans
      (cong (λ left → Transport.multiply group left b)
        (sym (Transport.inverseLeft group a)))
      (trans
        (Transport.multiplyAssoc group (Transport.inverse group a) a b)
        (trans
          (cong (Transport.multiply group (Transport.inverse group a))
            rightInverse)
          (Transport.unitRight group (Transport.inverse group a)))))

inverseMultiply :
  (group : Transport.GroupStructure) → ∀ left right →
  Transport.inverse group (Transport.multiply group left right)
  ≡ Transport.multiply group
      (Transport.inverse group right) (Transport.inverse group left)
inverseMultiply group left right =
  sym
    (rightInverseUnique group
      (Transport.multiply group left right)
      (Transport.multiply group
        (Transport.inverse group right) (Transport.inverse group left))
      (trans
        (Transport.multiplyAssoc group left right
          (Transport.multiply group
            (Transport.inverse group right) (Transport.inverse group left)))
        (trans
          (cong (Transport.multiply group left)
            (sym
              (Transport.multiplyAssoc group right
                (Transport.inverse group right)
                (Transport.inverse group left))))
          (trans
            (cong (Transport.multiply group left)
              (cong
                (λ middle → Transport.multiply group middle
                  (Transport.inverse group left))
                (Transport.inverseRight group right)))
            (trans
              (cong (Transport.multiply group left)
                (Transport.unitLeft group (Transport.inverse group left)))
              (Transport.inverseRight group left))))))

gaugeMultiply :
  ∀ {N} (group : Transport.GroupStructure) →
  Covariance.GaugeFunction4 N group →
  Covariance.GaugeFunction4 N group →
  Covariance.GaugeFunction4 N group
gaugeMultiply group outer inner site =
  Transport.multiply group (outer site) (inner site)

gaugeInverse :
  ∀ {N} (group : Transport.GroupStructure) →
  Covariance.GaugeFunction4 N group →
  Covariance.GaugeFunction4 N group
gaugeInverse group gauge site = Transport.inverse group (gauge site)

unitGauge :
  ∀ {N} (group : Transport.GroupStructure) →
  Covariance.GaugeFunction4 N group
unitGauge group _ = Transport.unit group

gaugeTransformUnit :
  ∀ {N} {{nz : NonZero N}}
    (group : Transport.GroupStructure)
    (field : Covariance.DirectedGaugeField4 N group) bond →
  Covariance.gaugeTransformBond group (unitGauge group) field bond
  ≡ field bond
gaugeTransformUnit group field bond =
  trans
    (cong
      (Transport.multiply group (Transport.unit group))
      (cong
        (Transport.multiply group (field bond))
        (Free.inverseUnitExact group)))
    (trans
      (Transport.unitLeft group
        (Transport.multiply group (field bond) (Transport.unit group)))
      (Transport.unitRight group (field bond)))

gaugeTransformCompose :
  ∀ {N} {{nz : NonZero N}}
    (group : Transport.GroupStructure)
    (outer inner : Covariance.GaugeFunction4 N group)
    (field : Covariance.DirectedGaugeField4 N group) bond →
  Covariance.gaugeTransformBond group outer
    (Covariance.gaugeTransformBond group inner field) bond
  ≡ Covariance.gaugeTransformBond group
      (gaugeMultiply group outer inner) field bond
gaugeTransformCompose group outer inner field bond =
  let
    oS = outer (source bond)
    oT = outer (target bond)
    iS = inner (source bond)
    iT = inner (target bond)
    u = field bond
  in
  trans
    (sym
      (Transport.multiplyAssoc group oS
        (Transport.multiply group iS
          (Transport.multiply group u (Transport.inverse group iT)))
        (Transport.inverse group oT)))
    (trans
      (cong
        (λ left → Transport.multiply group left (Transport.inverse group oT))
        (sym
          (Transport.multiplyAssoc group oS iS
            (Transport.multiply group u (Transport.inverse group iT)))))
      (trans
        (Transport.multiplyAssoc group
          (Transport.multiply group oS iS)
          (Transport.multiply group u (Transport.inverse group iT))
          (Transport.inverse group oT))
        (trans
          (cong
            (Transport.multiply group (Transport.multiply group oS iS))
            (Transport.multiplyAssoc group u
              (Transport.inverse group iT)
              (Transport.inverse group oT)))
          (cong
            (λ inverseTarget →
              Transport.multiply group
                (Transport.multiply group oS iS)
                (Transport.multiply group u inverseTarget))
            (sym (inverseMultiply group oT iT))))))

gaugeInverseCancelsAction :
  ∀ {N} {{nz : NonZero N}}
    (group : Transport.GroupStructure)
    (gauge : Covariance.GaugeFunction4 N group)
    (field : Covariance.DirectedGaugeField4 N group) bond →
  Covariance.gaugeTransformBond group (gaugeInverse group gauge)
    (Covariance.gaugeTransformBond group gauge field) bond
  ≡ field bond
gaugeInverseCancelsAction group gauge field bond =
  trans
    (gaugeTransformCompose group (gaugeInverse group gauge) gauge field bond)
    (trans
      (cong
        (λ selectedGauge →
          Covariance.gaugeTransformBond group selectedGauge field bond)
        -- no function extensionality: expand the action at this bond below
        refl)
      (let
        s = source bond
        t = target bond
        u = field bond
        in
        trans
          (cong₂ (Transport.multiply group)
            (Transport.inverseLeft group (gauge s))
            (cong₂ (Transport.multiply group)
              refl
              (cong (Transport.inverse group)
                (Transport.inverseLeft group (gauge t)))))
          (trans
            (cong
              (Transport.multiply group (Transport.unit group))
              (cong (Transport.multiply group u)
                (Free.inverseUnitExact group)))
            (trans
              (Transport.unitLeft group
                (Transport.multiply group u (Transport.unit group)))
              (Transport.unitRight group u)))))

composeGaugeActionArrows :
  ∀ {N} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {left middle right : Covariance.DirectedGaugeField4 N group} →
  Free.GaugeActionArrow group left middle →
  Free.GaugeActionArrow group middle right →
  Free.GaugeActionArrow group left right
composeGaugeActionArrows {group = group} firstArrow secondArrow = record
  { Free.GaugeActionArrow.gauge =
      gaugeMultiply group (Free.gauge secondArrow) (Free.gauge firstArrow)
  ; Free.GaugeActionArrow.actionExact = λ bond →
      trans
        (sym
          (gaugeTransformCompose group
            (Free.gauge secondArrow) (Free.gauge firstArrow) _ bond))
        (trans
          (cong
            (λ selected →
              Covariance.gaugeTransformBond group
                (Free.gauge secondArrow) selected bond)
            (Free.actionExact firstArrow bond))
          (Free.actionExact secondArrow bond))
  }

inverseGaugeActionArrow :
  ∀ {N} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {left right : Covariance.DirectedGaugeField4 N group} →
  Free.GaugeActionArrow group left right →
  Free.GaugeActionArrow group right left
inverseGaugeActionArrow {group = group} arrow = record
  { Free.GaugeActionArrow.gauge = gaugeInverse group (Free.gauge arrow)
  ; Free.GaugeActionArrow.actionExact = λ bond →
      trans
        (cong
          (λ selected →
            Covariance.gaugeTransformBond group
              (gaugeInverse group (Free.gauge arrow)) selected bond)
          (sym (Free.actionExact arrow bond)))
        (gaugeInverseCancelsAction group (Free.gauge arrow) _ bond)
  }

basedGaugeMultiply :
  ∀ {N} (group : Transport.GroupStructure) (base : Cube4 N)
    (outer inner : Covariance.GaugeFunction4 N group) →
  Free.BasedGaugeFunction group base outer →
  Free.BasedGaugeFunction group base inner →
  Free.BasedGaugeFunction group base (gaugeMultiply group outer inner)
basedGaugeMultiply group base outer inner outerBased innerBased =
  trans
    (cong₂ (Transport.multiply group) outerBased innerBased)
    (Transport.unitLeft group (Transport.unit group))

basedGaugeInverse :
  ∀ {N} (group : Transport.GroupStructure) (base : Cube4 N)
    (gauge : Covariance.GaugeFunction4 N group) →
  Free.BasedGaugeFunction group base gauge →
  Free.BasedGaugeFunction group base (gaugeInverse group gauge)
basedGaugeInverse group base gauge based =
  trans
    (cong (Transport.inverse group) based)
    (Free.inverseUnitExact group)

basedGaugeActionGroupoidRound200Level : ProofLevel
basedGaugeActionGroupoidRound200Level = machineChecked

gaugeActionCompositionRound200Level : ProofLevel
gaugeActionCompositionRound200Level = machineChecked

gaugeActionInverseRound200Level : ProofLevel
gaugeActionInverseRound200Level = machineChecked
