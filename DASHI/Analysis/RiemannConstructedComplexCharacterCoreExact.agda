module DASHI.Analysis.RiemannConstructedComplexCharacterCoreExact where

open import Agda.Builtin.Equality using (_≡_; refl; sym)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.ConcreteComplex

------------------------------------------------------------------------
-- LOWER BIDI CUT FOR H_X
--
-- The repository already has a genuinely constructed ordinary complex carrier:
-- ComplexPair over ConstructedOrderedCompleteReal, together with i, complex
-- arithmetic, expC, sin/cos and the Cartesian exponential formula.
--
-- That donor does NOT yet own two equations needed by the RH target character:
--
--   (1) scalar phase coherence
--         -(t u) + b u = (b - t) u
--
--   (2) complex exponential homomorphism
--         exp(x + y) = exp(x) exp(y).
--
-- We isolate exactly those missing laws.  Once supplied, the cosine projection
-- is already derivable from expCartesian + exp(0)=1; it is not an independent
-- RH assumption.
------------------------------------------------------------------------

record RealPhaseCoherence (C : ConstructedComplexPackage) : Set₁ where
  private
    R = real (realPackage C)
  field
    phaseGap :
      (b t u : Real R) →
      _+_ R (neg R (_*_ R t u)) (_*_ R b u)
      ≡ _*_ R (_-_ R b t) u

open RealPhaseCoherence public

record ComplexExponentialHomomorphism
    (C : ConstructedComplexPackage) : Set₁ where
  private
    R = real (realPackage C)
    CE = complexExponential C
  field
    expAddC :
      (x y : ComplexPair R) →
      expC CE (_+C_ x y) ≡ _*C_ (expC CE x) (expC CE y)

open ComplexExponentialHomomorphism public

plusPhase :
  (C : ConstructedComplexPackage) →
  Real (real (realPackage C)) →
  Real (real (realPackage C)) →
  ComplexPair (real (realPackage C))
plusPhase C delta u =
  let R = real (realPackage C)
  in complex (zero R) (_*_ R delta u)

minusPhase :
  (C : ConstructedComplexPackage) →
  Real (real (realPackage C)) →
  Real (real (realPackage C)) →
  ComplexPair (real (realPackage C))
minusPhase C t u =
  let R = real (realPackage C)
  in complex (zero R) (neg R (_*_ R t u))

phaseAddIsGap :
  (C : ConstructedComplexPackage) →
  RealPhaseCoherence C →
  (b t u : Real (real (realPackage C))) →
  _+C_ (minusPhase C t u) (plusPhase C b u)
  ≡ plusPhase C (_-_ (real (realPackage C)) b t) u
phaseAddIsGap C P b t u
  rewrite addZeroLeft (real (realPackage C))
            (zero (real (realPackage C)))
        | phaseGap P b t u
  = refl

reflectionEvenProjectionIsCosine :
  (C : ConstructedComplexPackage) →
  (delta u : Real (real (realPackage C))) →
  re (expC (complexExponential C) (plusPhase C delta u))
  ≡ cos (complexExponential C) (_*_ (real (realPackage C)) delta u)
reflectionEvenProjectionIsCosine C delta u
  rewrite expCartesian
            (complexExponential C)
            (zero (real (realPackage C)))
            (_*_ (real (realPackage C)) delta u)
        | expZero (exponential (realPackage C))
        | mulOneLeft
            (real (realPackage C))
            (cos (complexExponential C)
              (_*_ (real (realPackage C)) delta u))
  = refl

targetTimesSourceIsGap :
  (C : ConstructedComplexPackage) →
  (P : RealPhaseCoherence C) →
  (H : ComplexExponentialHomomorphism C) →
  (b t u : Real (real (realPackage C))) →
  _*C_
    (expC (complexExponential C) (minusPhase C t u))
    (expC (complexExponential C) (plusPhase C b u))
  ≡ expC
      (complexExponential C)
      (plusPhase C (_-_ (real (realPackage C)) b t) u)
targetTimesSourceIsGap C P H b t u
  rewrite sym (expAddC H (minusPhase C t u) (plusPhase C b u))
        | phaseAddIsGap C P b t u
  = refl

record ConstructedComplexCharacterCore
    (C : ConstructedComplexPackage) : Set₁ where
  constructor constructed-complex-character-core
  field
    realPhaseCoherence : RealPhaseCoherence C
    complexExponentialHomomorphism : ComplexExponentialHomomorphism C

  targetTimesSource :
    (b t u : Real (real (realPackage C))) →
    _*C_
      (expC (complexExponential C) (minusPhase C t u))
      (expC (complexExponential C) (plusPhase C b u))
    ≡ expC
        (complexExponential C)
        (plusPhase C (_-_ (real (realPackage C)) b t) u)
  targetTimesSource =
    targetTimesSourceIsGap C realPhaseCoherence complexExponentialHomomorphism

  evenProjection :
    (delta u : Real (real (realPackage C))) →
    re (expC (complexExponential C) (plusPhase C delta u))
    ≡ cos (complexExponential C) (_*_ (real (realPackage C)) delta u)
  evenProjection = reflectionEvenProjectionIsCosine C

open ConstructedComplexCharacterCore public

record ConstructedCharacterCoreBoundary : Set where
  constructor constructed-character-core-boundary
  field
    concreteComplexAlreadyOwnsImaginaryUnit : Bool
    concreteComplexAlreadyOwnsImaginaryUnitIsTrue :
      concreteComplexAlreadyOwnsImaginaryUnit ≡ true

    concreteComplexAlreadyOwnsCartesianExp : Bool
    concreteComplexAlreadyOwnsCartesianExpIsTrue :
      concreteComplexAlreadyOwnsCartesianExp ≡ true

    cosineProjectionIsNewIndependentAssumption : Bool
    cosineProjectionIsNewIndependentAssumptionIsFalse :
      cosineProjectionIsNewIndependentAssumption ≡ false

    realPhaseCoherenceAlreadyOwned : Bool
    realPhaseCoherenceAlreadyOwnedIsFalse :
      realPhaseCoherenceAlreadyOwned ≡ false

    complexExpHomomorphismAlreadyOwned : Bool
    complexExpHomomorphismAlreadyOwnedIsFalse :
      complexExpHomomorphismAlreadyOwned ≡ false

    constructedDonorAloneClosesCanonicalHX : Bool
    constructedDonorAloneClosesCanonicalHXIsFalse :
      constructedDonorAloneClosesCanonicalHX ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    nextTheorem : String

constructedCharacterCoreBoundary : ConstructedCharacterCoreBoundary
constructedCharacterCoreBoundary =
  constructed-character-core-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "Prove scalar phase coherence and expC additivity for the constructed ordinary complex package, then attach that same package to the canonical Riemann ComplexAnalyticCarrier without changing carriers."
