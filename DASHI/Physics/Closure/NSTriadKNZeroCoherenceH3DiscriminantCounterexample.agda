module DASHI.Physics.Closure.NSTriadKNZeroCoherenceH3DiscriminantCounterexample where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: DASHI repository contributors.
-- Title: "Exact six-mode counterexample to the zero-coherence H^3 quartic
-- discriminant".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; this is a DASHI-original exact computation.
-- Uses: the literal periodic coefficient convention documented in
-- NSTriadKNComplex3GalerkinEquationAudit.
-- Relationship: falsifies one concrete candidate; it does not establish or
-- refute the full adaptive quartic family.  The discriminant gap
-- C^2 - 4AB = 28,984,957,666,432 > 0 is exact.  The falsification is
-- valuable because it identified a blind submanifold of the entire global
-- helicity family: every state with |u_k^+| = |u_k^-| at every occupied
-- mode is equally unreachable by any constant-sign global curl
-- perturbation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
import Data.Integer.Base as Int
open import Data.Integer.Base using (+_; -[1+_])
open import Data.Nat.Base using (_<_; z≤n; s≤s)

record Mode : Set where
  constructor mode
  field
    kx ky kz : Int.ℤ

record GaussianInteger : Set where
  constructor gi
  field
    real imaginary : Int.ℤ

record ComplexVelocity : Set where
  constructor velocity
  field
    ux uy uz : GaussianInteger

gzero : GaussianInteger
gzero = gi (+ 0) (+ 0)

gadd : GaussianInteger → GaussianInteger → GaussianInteger
gadd (gi ar ai) (gi br bi) =
  gi (Int._+_ ar br) (Int._+_ ai bi)

integerScale : Int.ℤ → GaussianInteger → GaussianInteger
integerScale n (gi ar ai) =
  gi (Int._*_ n ar) (Int._*_ n ai)

divergence : Mode → ComplexVelocity → GaussianInteger
divergence (mode x y z) (velocity a b c) =
  gadd (gadd (integerScale x a) (integerScale y b))
    (integerScale z c)

p q k : Mode
p = mode (-[1+ 0 ]) (+ 0) (+ 3)
q = mode (+ 2) (-[1+ 2 ]) (-[1+ 2 ])
k = mode (+ 1) (-[1+ 2 ]) (+ 0)

modeAdd : Mode → Mode → Mode
modeAdd (mode ax ay az) (mode bx by bz) =
  mode (Int._+_ ax bx) (Int._+_ ay by) (Int._+_ az bz)

physicalResonance : modeAdd p q ≡ k
physicalResonance = refl

u-p u-q u-k : ComplexVelocity
u-p =
  velocity
    (gi (+ 3) (+ 3))
    (gi (-[1+ 2 ]) (-[1+ 2 ]))
    (gi (+ 1) (+ 1))
u-q =
  velocity
    (gi (-[1+ 2 ]) (+ 0))
    gzero
    (gi (-[1+ 1 ]) (+ 0))
u-k =
  velocity
    (gi (+ 3) (-[1+ 2 ]))
    (gi (+ 1) (-[1+ 0 ]))
    gzero

pDivergenceFree : divergence p u-p ≡ gzero
pDivergenceFree = refl

qDivergenceFree : divergence q u-q ≡ gzero
qDivergenceFree = refl

kDivergenceFree : divergence k u-k ≡ gzero
kDivergenceFree = refl

------------------------------------------------------------------------
-- Exact receipt values for viscosity nu = 1, coherence w = 0 and
-- m(k) = (1 + |k|^2)^3 on the six modes +/-p, +/-q, +/-k.
--
-- scripts/ns_quartic_h3_zero_coherence_counterexample.py independently
-- evaluates the literal convolution, Leray projection and real Hermitian
-- pairing over Fraction and checks these three values.
------------------------------------------------------------------------

quadraticReserveValue quarticReserveValue cubicMagnitudeValue : Nat
quadraticReserveValue = 8503484
quarticReserveValue = 245944
cubicMagnitudeValue = 6111504

discriminantGap : Nat
discriminantGap = 28984957666432

homogeneousQuadraticReserveValue homogeneousCubicMagnitudeValue : Nat
homogeneousQuadraticReserveValue = 7250656
homogeneousCubicMagnitudeValue = 5441472

homogeneousDiscriminantGap : Nat
homogeneousDiscriminantGap = 22476596169728

exactDiscriminantGap :
  cubicMagnitudeValue * cubicMagnitudeValue
  ≡
  4 * quadraticReserveValue * quarticReserveValue
  + discriminantGap
exactDiscriminantGap = refl

discriminantGapPositive : 0 < discriminantGap
discriminantGapPositive = s≤s z≤n

exactHomogeneousDiscriminantGap :
  homogeneousCubicMagnitudeValue * homogeneousCubicMagnitudeValue
  ≡
  4 * homogeneousQuadraticReserveValue * quarticReserveValue
  + homogeneousDiscriminantGap
exactHomogeneousDiscriminantGap = refl

homogeneousDiscriminantGapPositive : 0 < homogeneousDiscriminantGap
homogeneousDiscriminantGapPositive = s≤s z≤n

record ExactCounterexampleReceipt : Set where
  constructor receipt
  field
    resonance : modeAdd p q ≡ k
    pTransverse : divergence p u-p ≡ gzero
    qTransverse : divergence q u-q ≡ gzero
    kTransverse : divergence k u-k ≡ gzero
    exactFailure :
      cubicMagnitudeValue * cubicMagnitudeValue
      ≡
      4 * quadraticReserveValue * quarticReserveValue
      + discriminantGap
    strictFailureGap : 0 < discriminantGap
    exactHomogeneousFailure :
      homogeneousCubicMagnitudeValue * homogeneousCubicMagnitudeValue
      ≡
      4 * homogeneousQuadraticReserveValue * quarticReserveValue
      + homogeneousDiscriminantGap
    strictHomogeneousFailureGap : 0 < homogeneousDiscriminantGap

zeroCoherenceH3DiscriminantCounterexample :
  ExactCounterexampleReceipt
zeroCoherenceH3DiscriminantCounterexample =
  receipt
    physicalResonance
    pDivergenceFree
    qDivergenceFree
    kDivergenceFree
    exactDiscriminantGap
    discriminantGapPositive
    exactHomogeneousDiscriminantGap
    homogeneousDiscriminantGapPositive

zeroCoherenceH3CandidateSurvivesDiscriminant : Bool
zeroCoherenceH3CandidateSurvivesDiscriminant = false

zeroCoherenceH3CandidateSurvivesDiscriminantIsFalse :
  zeroCoherenceH3CandidateSurvivesDiscriminant ≡ false
zeroCoherenceH3CandidateSurvivesDiscriminantIsFalse = refl

exactCounterexampleReceiptImplemented : Bool
exactCounterexampleReceiptImplemented = true

exactCounterexampleReceiptImplementedIsTrue :
  exactCounterexampleReceiptImplemented ≡ true
exactCounterexampleReceiptImplementedIsTrue = refl
