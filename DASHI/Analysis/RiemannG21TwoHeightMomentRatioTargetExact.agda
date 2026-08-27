module DASHI.Analysis.RiemannG21TwoHeightMomentRatioTargetExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Two-height moment-ratio target behind the symmetric-sample parity minors.
--
-- For the actual real-even taper one expects, near r = 0,
--
--   A_y(r) = M0(y) - r^2 M2(y)/2 + O(r^4)
--   B_y(r) = -r N1(y) + r^3 N3(y)/6 + O(r^5),
--
-- where schematically
--
--   Mj(y) = integral u^j phi(u) cosh(y u) du  (even j),
--   Nj(y) = integral u^j phi(u) sinh(y u) du  (odd j).
--
-- If the ratios M2/M0 and N3/N1 differ between off-line height alpha and
-- pole height 1/2, the leading parity minors are nonzero.  We encode the
-- division-free cross-product conditions needed for that argument.  No claim
-- is made here that the source taper already satisfies the analytic remainder
-- control needed to transfer these leading terms to finite sample radii.
------------------------------------------------------------------------

record MomentQuadruple : Set where
  constructor moments
  field
    M0 M2 N1 N3 : Nat

open MomentQuadruple public

record CrossProductSeparation : Set where
  constructor crossProductSeparation
  field
    offLine pole : MomentQuadruple

    evenCrossProductsDiffer :
      M2 offLine * M0 pole ≡ M0 offLine * M2 pole → ⊥

    oddCrossProductsDiffer :
      N3 offLine * N1 pole ≡ N1 offLine * N3 pole → ⊥

    separationReading : String

open CrossProductSeparation public

------------------------------------------------------------------------
-- Non-vacuous finite witness.
------------------------------------------------------------------------

toyOffLineMoments : MomentQuadruple
toyOffLineMoments = moments 2 2 2 2

toyPoleMoments : MomentQuadruple
toyPoleMoments = moments 2 4 2 6

-- even: 2*2 = 4 versus 2*4 = 8
-- odd : 2*2 = 4 versus 2*6 = 12
canonicalMomentCrossProductSeparation : CrossProductSeparation
canonicalMomentCrossProductSeparation =
  crossProductSeparation
    toyOffLineMoments
    toyPoleMoments
    (λ ())
    (λ ())
    "Finite regression witness only: both even and odd moment ratios can separate two height responses without using division."

------------------------------------------------------------------------
-- Actual analytic producer.  This is the next theorem socket.
------------------------------------------------------------------------

record ActualTaperMomentRatioProducer : Set₁ where
  field
    Height : Set
    StrictlyBelow : Height → Height → Set

    offLineHeight poleHeight : Height
    heightSeparated : StrictlyBelow offLineHeight poleHeight

    RealMoment : Set
    m0 m2 n1 n3 : Height → RealMoment
    multiply : RealMoment → RealMoment → RealMoment
    Distinct : RealMoment → RealMoment → Set

    evenMomentRatioSeparated :
      Distinct
        (multiply (m2 offLineHeight) (m0 poleHeight))
        (multiply (m0 offLineHeight) (m2 poleHeight))

    oddMomentRatioSeparated :
      Distinct
        (multiply (n3 offLineHeight) (n1 poleHeight))
        (multiply (n1 offLineHeight) (n3 poleHeight))

    PositiveDenominators : Set
    positiveDenominators : PositiveDenominators

    producerReading : String

open ActualTaperMomentRatioProducer public

------------------------------------------------------------------------
-- Transfer from moment-ratio separation to finite-radius parity minors also
-- needs a quantitative Taylor/remainder theorem.  Keep it separate.
------------------------------------------------------------------------

record MomentToParityMinorTransfer
    (producer : ActualTaperMomentRatioProducer) : Set₁ where
  field
    SampleRadius : Set
    radiusOne radiusTwo : SampleRadius

    RadiusAdmissible : SampleRadius → Set
    radiusOneAdmissible : RadiusAdmissible radiusOne
    radiusTwoAdmissible : RadiusAdmissible radiusTwo

    EvenMinorNonzero : Set
    OddMinorNonzero : Set

    taylorRemainderControl : Set
    evenMinorNonzero : EvenMinorNonzero
    oddMinorNonzero : OddMinorNonzero

    transferReading : String

record MomentRatioBoundary : Set where
  constructor momentRatioBoundary
  field
    divisionFreeMomentCriterionConstructed : Bool
    divisionFreeMomentCriterionConstructedIsTrue :
      divisionFreeMomentCriterionConstructed ≡ true

    strictHeightSeparationAloneImpliesMomentSeparation : Bool
    strictHeightSeparationAloneImpliesMomentSeparationIsFalse :
      strictHeightSeparationAloneImpliesMomentSeparation ≡ false

    momentSeparationAloneImpliesFiniteRadiusMinors : Bool
    momentSeparationAloneImpliesFiniteRadiusMinorsIsFalse :
      momentSeparationAloneImpliesFiniteRadiusMinors ≡ false

    actualTaperMomentRatioProducerConstructed : Bool
    actualTaperMomentRatioProducerConstructedIsFalse :
      actualTaperMomentRatioProducerConstructed ≡ false

canonicalMomentRatioBoundary : MomentRatioBoundary
canonicalMomentRatioBoundary =
  momentRatioBoundary
    true refl
    false refl
    false refl
    false refl
