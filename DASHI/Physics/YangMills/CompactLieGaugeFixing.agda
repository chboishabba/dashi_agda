module DASHI.Physics.YangMills.CompactLieGaugeFixing where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.BalabanSU2CriticalMapContraction using
  (FiniteCriticalContraction; fixedPoint; fixedPointUnique)

------------------------------------------------------------------------
-- Generic nonlinear gauge-fixing socket.
--
-- Once the Faddeev--Popov/Newton map is exhibited as a finite strict
-- contraction and its fixed point satisfies the gauge condition, the
-- normalized gauge representative is unique.  Actual coercivity and Lipschitz
-- constants remain group- and patch-specific inputs.
------------------------------------------------------------------------

record GaugeFixingContraction
    (Field Gauge Distance : Set) : Set₁ where
  field
    normalizedGauge : Gauge → Set
    transform : Gauge → Field → Field
    GaugeCondition : Field → Set

    inputField : Field
    solver : Gauge → Gauge
    contraction : FiniteCriticalContraction Gauge Distance

    solverAgrees : ∀ gauge →
      FiniteCriticalContraction.step contraction gauge ≡ solver gauge

    fixedGaugeIsNormalized : normalizedGauge (fixedPoint contraction)
    fixedGaugeFixesField :
      GaugeCondition (transform (fixedPoint contraction) inputField)

open GaugeFixingContraction public

gaugeFixingGaugeUnique :
  ∀ {Field Gauge Distance : Set} →
  (bundle : GaugeFixingContraction Field Gauge Distance) →
  ∀ gauge →
  solver bundle gauge ≡ gauge →
  gauge ≡ fixedPoint (contraction bundle)
gaugeFixingGaugeUnique bundle gauge solverFixed =
  fixedPointUnique
    (contraction bundle)
    gauge
    (trans (solverAgrees bundle gauge) solverFixed)
