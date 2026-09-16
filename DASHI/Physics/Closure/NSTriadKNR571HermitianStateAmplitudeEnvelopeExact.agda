module DASHI.Physics.Closure.NSTriadKNR571HermitianStateAmplitudeEnvelopeExact where

------------------------------------------------------------------------
-- R571 GATE-A / LOCAL G1 STATE-AMPLITUDE ENVELOPE
--
-- G0' already scalarizes the literal rational C^3 samples by
--
--   g(X;D) = Re <X,D>.
--
-- R579 proves, on exactly that rational Hermitian carrier and without square
-- roots,
--
--   |Re <X,D>| <= ||X||^2 + ||D||^2.
--
-- Therefore the two transported-state amplitudes g+ and g- admit one common
-- local envelope made only from the actual squared masses of X+, X- and the
-- spectator D.  This pays the G1 *local scalar-envelope* leaf without a new
-- analytic theorem and without a fibre-cardinality factor.
--
-- It does NOT pay G2 (the displacement-scaled state-difference envelope), does
-- not construct the complete R571StateDerivativeEnvelope, and does not claim a
-- cutoff-uniform collar/R423/R568 payment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNR571HermitianScalarizedOppositePairExact as G0
import DASHI.Physics.Closure.NSTriadKNRationalHermitianYoungRound579Exact as R579

F = G0.Weld.F

stateAmplitudeEnvelope :
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → ℚ
stateAmplitudeEnvelope XPlus XMinus D =
  (L2.complex3NormSquared XPlus + L2.complex3NormSquared D)
  + (L2.complex3NormSquared XMinus + L2.complex3NormSquared D)

stateAmplitudeEnvelopeNonnegative :
  (XPlus XMinus D : C3.Complex3 F) →
  0ℚ ≤ stateAmplitudeEnvelope XPlus XMinus D
stateAmplitudeEnvelopeNonnegative XPlus XMinus D =
  let
    plusNN :
      0ℚ ≤ L2.complex3NormSquared XPlus + L2.complex3NormSquared D
    plusNN =
      ℚP.+-mono-≤
        (Separation.complex3NormSquaredNonnegative XPlus)
        (Separation.complex3NormSquaredNonnegative D)

    minusNN :
      0ℚ ≤ L2.complex3NormSquared XMinus + L2.complex3NormSquared D
    minusNN =
      ℚP.+-mono-≤
        (Separation.complex3NormSquaredNonnegative XMinus)
        (Separation.complex3NormSquaredNonnegative D)
  in
  ℚP.+-mono-≤ plusNN minusNN

plusHermitianMagnitudeBelowStateEnvelope :
  (XPlus XMinus D : C3.Complex3 F) →
  ∣ G0.hermitianScalar XPlus D ∣
  ≤ stateAmplitudeEnvelope XPlus XMinus D
plusHermitianMagnitudeBelowStateEnvelope XPlus XMinus D =
  let
    plusMass = L2.complex3NormSquared XPlus + L2.complex3NormSquared D
    minusMass = L2.complex3NormSquared XMinus + L2.complex3NormSquared D

    local : ∣ G0.hermitianScalar XPlus D ∣ ≤ plusMass
    local = R579.rationalRealHermitianYoung XPlus D

    minusNN : 0ℚ ≤ minusMass
    minusNN =
      ℚP.+-mono-≤
        (Separation.complex3NormSquaredNonnegative XMinus)
        (Separation.complex3NormSquaredNonnegative D)

    extend : plusMass ≤ plusMass + minusMass
    extend = ℚP.+-monoʳ-≤ plusMass minusNN
  in
  ℚP.≤-trans local extend

minusHermitianMagnitudeBelowStateEnvelope :
  (XPlus XMinus D : C3.Complex3 F) →
  ∣ G0.hermitianScalar XMinus D ∣
  ≤ stateAmplitudeEnvelope XPlus XMinus D
minusHermitianMagnitudeBelowStateEnvelope XPlus XMinus D =
  let
    plusMass = L2.complex3NormSquared XPlus + L2.complex3NormSquared D
    minusMass = L2.complex3NormSquared XMinus + L2.complex3NormSquared D

    local : ∣ G0.hermitianScalar XMinus D ∣ ≤ minusMass
    local = R579.rationalRealHermitianYoung XMinus D

    plusNN : 0ℚ ≤ plusMass
    plusNN =
      ℚP.+-mono-≤
        (Separation.complex3NormSquaredNonnegative XPlus)
        (Separation.complex3NormSquaredNonnegative D)

    extendReversed : minusMass ≤ minusMass + plusMass
    extendReversed = ℚP.+-monoʳ-≤ minusMass plusNN

    extend : minusMass ≤ plusMass + minusMass
    extend =
      subst
        (minusMass ≤_)
        (solve
          ( L2.complex3NormSquared XPlus
          ∷ L2.complex3NormSquared XMinus
          ∷ L2.complex3NormSquared D
          ∷ []))
        extendReversed
  in
  ℚP.≤-trans local extend

r571LocalHermitianG1EnvelopeClosed : Bool
r571LocalHermitianG1EnvelopeClosed = true

r571LocalHermitianG1UsesSquareRoot : Bool
r571LocalHermitianG1UsesSquareRoot = false

r571LocalHermitianG2ClosedHere : Bool
r571LocalHermitianG2ClosedHere = false

r571FullStateDerivativeEnvelopeClosed : Bool
r571FullStateDerivativeEnvelopeClosed = false

r571LocalHermitianG1EnvelopeClosedIsTrue :
  r571LocalHermitianG1EnvelopeClosed ≡ true
r571LocalHermitianG1EnvelopeClosedIsTrue = refl

r571LocalHermitianG1UsesSquareRootIsFalse :
  r571LocalHermitianG1UsesSquareRoot ≡ false
r571LocalHermitianG1UsesSquareRootIsFalse = refl

r571LocalHermitianG2ClosedHereIsFalse :
  r571LocalHermitianG2ClosedHere ≡ false
r571LocalHermitianG2ClosedHereIsFalse = refl

r571FullStateDerivativeEnvelopeClosedIsFalse :
  r571FullStateDerivativeEnvelopeClosed ≡ false
r571FullStateDerivativeEnvelopeClosedIsFalse = refl
