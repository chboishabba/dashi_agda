module DASHI.Analysis.RiemannG1FiniteRetentionAssemblyExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Remove the last packaging seam inside G1.
--
-- Source-facing analytic work produces:
--   (1) a Hermitian Poisson full-grid excess,
--   (2) a cosh/second-moment coercivity ledger for that SAME excess,
--   (3) a finite-grid tail ledger for that SAME full-grid excess.
--
-- Once the two scalar alignments are supplied, the downstream
-- `CoerciveFiniteRetention` object is constructed automatically, and the
-- existing theorem then derives its `FiniteRetentionCertificate`.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)

open import DASHI.Analysis.RiemannPhiCoshCoercivityReductionExact
  using
    ( PhiCoshCoercivityLedger
    ; alphaSquared
    ; secondMomentPredecessor
    ; phiExcess
    ; coshSlack
    ; coercivityIdentity
    )
open import DASHI.Analysis.RiemannComplexPoissonFiniteRetentionExact
  using
    ( FiniteGridTailLedger
    ; fullGridExcess
    ; CoerciveFiniteRetention
    ; coerciveFiniteRetention
    ; FiniteRetentionCertificate
    ; coerciveFiniteRetentionImpliesCertificate
    )

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

record G1AlignedFiniteData : Set where
  constructor g1AlignedFiniteData
  field
    cosh : PhiCoshCoercivityLedger
    tail : FiniteGridTailLedger

    poissonHermitianExcess : Nat

    poissonExcessIsCoshExcess :
      poissonHermitianExcess ≡ phiExcess cosh

    poissonExcessIsTailFullGridExcess :
      poissonHermitianExcess ≡ fullGridExcess tail

open G1AlignedFiniteData public

weightedAlphaSquaredDefect : G1AlignedFiniteData → Nat
weightedAlphaSquaredDefect g =
  ((2 * suc (secondMomentPredecessor (cosh g))) * alphaSquared (cosh g))

------------------------------------------------------------------------
-- EXACT CONNECTION.
------------------------------------------------------------------------

g1AlignedDataToCoerciveFiniteRetention :
  G1AlignedFiniteData → CoerciveFiniteRetention
g1AlignedDataToCoerciveFiniteRetention g =
  coerciveFiniteRetention
    (weightedAlphaSquaredDefect g)
    (coshSlack (cosh g))
    (tail g)
    aligned
  where
  aligned :
    weightedAlphaSquaredDefect g + coshSlack (cosh g)
      ≡ fullGridExcess (tail g)
  aligned =
    trans
      (coercivityIdentity (cosh g))
      (trans
        (sym (poissonExcessIsCoshExcess g))
        (poissonExcessIsTailFullGridExcess g))

g1AlignedDataToFiniteRetentionCertificate :
  (g : G1AlignedFiniteData) →
  FiniteRetentionCertificate (g1AlignedDataToCoerciveFiniteRetention g)
g1AlignedDataToFiniteRetentionCertificate g =
  coerciveFiniteRetentionImpliesCertificate
    (g1AlignedDataToCoerciveFiniteRetention g)

------------------------------------------------------------------------
-- Source-facing producer.  The only non-algebraic work left in G1 is now
-- producing these aligned ledgers from the actual complex Poisson theorem,
-- elementary cosh/moment estimate, and finite-k tail estimate.
------------------------------------------------------------------------

record G1AnalyticProducer : Set₁ where
  field
    ZeroPair : Set
    alignedFiniteData : ZeroPair → G1AlignedFiniteData

producerCoerciveFiniteRetention :
  (p : G1AnalyticProducer) →
  (rho : G1AnalyticProducer.ZeroPair p) →
  CoerciveFiniteRetention
producerCoerciveFiniteRetention p rho =
  g1AlignedDataToCoerciveFiniteRetention
    (G1AnalyticProducer.alignedFiniteData p rho)
