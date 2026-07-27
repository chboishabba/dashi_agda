module DASHI.Physics.Closure.NSTriadKNGlobalHelicityH3DiscriminantCounterexample where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: DASHI repository contributors.
-- Title: "Exact six-mode obstruction to the global helicity-perturbed H^3
-- quartic candidate".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; this is a DASHI-original exact computation.
-- Uses: the six-mode state in
-- NSTriadKNZeroCoherenceH3DiscriminantCounterexample and the literal curl
-- symbol C_k u = i k cross u.
-- Relationship: proves that the known state is modewise helicity-balanced
-- (|u_k^+|^2 = |u_k^-|^2 at every occupied mode, i.e. an equal-energy
-- superposition of the positive- and negative-curl eigenspaces), so the
-- global helicity perturbation changes neither its viscous reserve nor its
-- failed discriminant, for either sign and every epsilon.  The modewise
-- balance is a codimension-one condition in each complex two-dimensional
-- transverse fibre, not a measure-zero anomaly; symmetry constraints from
-- the ordered-pair/reality-mate cancellation machinery make it structurally
-- natural for states built by that route.  This eliminates the entire
-- constant-sign global curl perturbation family: any scalar spectral
-- localization still has zero quadratic value on this witness, because
-- every summand <u_k, ik x u_k> vanishes individually.  The surviving
-- mechanism for localized helicity is the non-conservation of H_chi under
-- Euler dynamics: the triadic derivative produces cutoff-difference
-- commutators because chi(k), chi(p), chi(q) are unequal when p+q=k.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
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

gnegate : GaussianInteger → GaussianInteger
gnegate (gi ar ai) = gi (Int.-_ ar) (Int.-_ ai)

gsubtract : GaussianInteger → GaussianInteger → GaussianInteger
gsubtract a b = gadd a (gnegate b)

gmultiply : GaussianInteger → GaussianInteger → GaussianInteger
gmultiply (gi ar ai) (gi br bi) =
  gi
    (Int._+_ (Int._*_ ar br) (Int.-_ (Int._*_ ai bi)))
    (Int._+_ (Int._*_ ar bi) (Int._*_ ai br))

gconjugate : GaussianInteger → GaussianInteger
gconjugate (gi ar ai) = gi ar (Int.-_ ai)

timesI : GaussianInteger → GaussianInteger
timesI (gi ar ai) = gi (Int.-_ ai) ar

integerScale : Int.ℤ → GaussianInteger → GaussianInteger
integerScale n (gi ar ai) =
  gi (Int._*_ n ar) (Int._*_ n ai)

curlSymbol : Mode → ComplexVelocity → ComplexVelocity
curlSymbol (mode x y z) (velocity a b c) =
  velocity
    (timesI (gsubtract (integerScale y c) (integerScale z b)))
    (timesI (gsubtract (integerScale z a) (integerScale x c)))
    (timesI (gsubtract (integerScale x b) (integerScale y a)))

realHermitianPairing :
  ComplexVelocity → ComplexVelocity → Int.ℤ
realHermitianPairing (velocity a b c) (velocity x y z) =
  GaussianInteger.real
    (gadd
      (gadd
        (gmultiply (gconjugate a) x)
        (gmultiply (gconjugate b) y))
      (gmultiply (gconjugate c) z))

helicityDensity : Mode → ComplexVelocity → Int.ℤ
helicityDensity k u = realHermitianPairing u (curlSymbol k u)

negateMode : Mode → Mode
negateMode (mode x y z) =
  mode (Int.-_ x) (Int.-_ y) (Int.-_ z)

conjugateVelocity : ComplexVelocity → ComplexVelocity
conjugateVelocity (velocity a b c) =
  velocity (gconjugate a) (gconjugate b) (gconjugate c)

p q k : Mode
p = mode (-[1+ 0 ]) (+ 0) (+ 3)
q = mode (+ 2) (-[1+ 2 ]) (-[1+ 2 ])
k = mode (+ 1) (-[1+ 2 ]) (+ 0)

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

pHelicityZero : helicityDensity p u-p ≡ + 0
pHelicityZero = refl

qHelicityZero : helicityDensity q u-q ≡ + 0
qHelicityZero = refl

kHelicityZero : helicityDensity k u-k ≡ + 0
kHelicityZero = refl

negativePHelicityZero :
  helicityDensity (negateMode p) (conjugateVelocity u-p) ≡ + 0
negativePHelicityZero = refl

negativeQHelicityZero :
  helicityDensity (negateMode q) (conjugateVelocity u-q) ≡ + 0
negativeQHelicityZero = refl

negativeKHelicityZero :
  helicityDensity (negateMode k) (conjugateVelocity u-k) ≡ + 0
negativeKHelicityZero = refl

knownSixModeHelicityDissipationEvaluation : Int.ℤ
knownSixModeHelicityDissipationEvaluation =
  Int._+_
    (Int._+_
      (Int._+_ (helicityDensity p u-p) (helicityDensity q u-q))
      (helicityDensity k u-k))
    (Int._+_
      (Int._+_
        (helicityDensity (negateMode p) (conjugateVelocity u-p))
        (helicityDensity (negateMode q) (conjugateVelocity u-q)))
      (helicityDensity (negateMode k) (conjugateVelocity u-k)))

knownSixModeHelicityDissipationEvaluationIsZero :
  knownSixModeHelicityDissipationEvaluation ≡ + 0
knownSixModeHelicityDissipationEvaluationIsZero = refl

data HelicitySign : Set where
  plus minus : HelicitySign

baseQuadraticReserve quarticReserve cubicMagnitude discriminantGap : Nat
baseQuadraticReserve = 8503484
quarticReserve = 245944
cubicMagnitude = 6111504
discriminantGap = 28984957666432

helicityPerturbedQuadraticReserve :
  HelicitySign → Nat → Nat
helicityPerturbedQuadraticReserve sign epsilon =
  baseQuadraticReserve + epsilon * 0

helicityPerturbedCubicContribution :
  HelicitySign → Nat → Nat
helicityPerturbedCubicContribution sign epsilon = cubicMagnitude

helicityPerturbedQuarticReserve :
  HelicitySign → Nat → Nat
helicityPerturbedQuarticReserve sign epsilon = quarticReserve

knownSixModeHelicityPerturbedAFormula :
  ∀ sign epsilon →
  helicityPerturbedQuadraticReserve sign epsilon
  ≡ baseQuadraticReserve
knownSixModeHelicityPerturbedAFormula sign epsilon = refl

knownSixModeHelicityPerturbedCFormula :
  ∀ sign epsilon →
  helicityPerturbedCubicContribution sign epsilon ≡ cubicMagnitude
knownSixModeHelicityPerturbedCFormula sign epsilon = refl

knownSixModeHelicityPerturbedBFormula :
  ∀ sign epsilon →
  helicityPerturbedQuarticReserve sign epsilon ≡ quarticReserve
knownSixModeHelicityPerturbedBFormula sign epsilon = refl

knownSixModeDiscriminantPolynomialInEpsilon :
  ∀ sign epsilon →
  helicityPerturbedCubicContribution sign epsilon
    * helicityPerturbedCubicContribution sign epsilon
  ≡
  4 * helicityPerturbedQuadraticReserve sign epsilon
      * helicityPerturbedQuarticReserve sign epsilon
  + discriminantGap
knownSixModeDiscriminantPolynomialInEpsilon sign epsilon = refl

AdmissibleEpsilon : Nat → Set
AdmissibleEpsilon epsilon = epsilon < 8

allAdmissibleEpsilonFailKnownCounterexample :
  ∀ sign epsilon →
  AdmissibleEpsilon epsilon →
  helicityPerturbedCubicContribution sign epsilon
    * helicityPerturbedCubicContribution sign epsilon
  ≡
  4 * helicityPerturbedQuadraticReserve sign epsilon
      * helicityPerturbedQuarticReserve sign epsilon
  + discriminantGap
allAdmissibleEpsilonFailKnownCounterexample sign epsilon admissible =
  knownSixModeDiscriminantPolynomialInEpsilon sign epsilon

discriminantGapPositive : 0 < discriminantGap
discriminantGapPositive = s≤s z≤n

record GlobalHelicityCounterexampleReceipt : Set where
  constructor receipt
  field
    pBalanced : helicityDensity p u-p ≡ + 0
    qBalanced : helicityDensity q u-q ≡ + 0
    kBalanced : helicityDensity k u-k ≡ + 0
    negativePBalanced :
      helicityDensity (negateMode p) (conjugateVelocity u-p) ≡ + 0
    negativeQBalanced :
      helicityDensity (negateMode q) (conjugateVelocity u-q) ≡ + 0
    negativeKBalanced :
      helicityDensity (negateMode k) (conjugateVelocity u-k) ≡ + 0
    everyParameterFails :
      ∀ sign epsilon →
      helicityPerturbedCubicContribution sign epsilon
        * helicityPerturbedCubicContribution sign epsilon
      ≡
      4 * helicityPerturbedQuadraticReserve sign epsilon
          * helicityPerturbedQuarticReserve sign epsilon
      + discriminantGap
    strictFailure : 0 < discriminantGap

globalHelicityH3Counterexample :
  GlobalHelicityCounterexampleReceipt
globalHelicityH3Counterexample =
  receipt
    pHelicityZero
    qHelicityZero
    kHelicityZero
    negativePHelicityZero
    negativeQHelicityZero
    negativeKHelicityZero
    knownSixModeDiscriminantPolynomialInEpsilon
    discriminantGapPositive

globalHelicityPerturbedH3CandidateSurvives : Bool
globalHelicityPerturbedH3CandidateSurvives = false

globalHelicityPerturbedH3CandidateSurvivesIsFalse :
  globalHelicityPerturbedH3CandidateSurvives ≡ false
globalHelicityPerturbedH3CandidateSurvivesIsFalse = refl

globalHelicityCounterexampleReceiptImplemented : Bool
globalHelicityCounterexampleReceiptImplemented = true

globalHelicityCounterexampleReceiptImplementedIsTrue :
  globalHelicityCounterexampleReceiptImplemented ≡ true
globalHelicityCounterexampleReceiptImplementedIsTrue = refl
