module DASHI.Moonshine.DeltaUnitCircleReflectionPhaseExact where

------------------------------------------------------------------------
-- DELTA CONJUGATION / S-TRANSFORM / UNIT-CIRCLE PHASE BRIDGE
--
-- PURPOSE
--
-- Derive the source-side identity
--
--   Delta(1 / conjugate z) = conjugate(z^12 Delta(z))
--
-- from the already-owned weight-12 modular law plus a concrete conjugation/S
-- semantics interface.  The reflection identity itself is NOT accepted as a
-- primitive field.
--
-- Existing theorem authority:
--
--   DASHI.Moonshine.DeltaNormalizedWeight12SameObjectExact
--
-- gives the all-SL2(Z) weight-12 law for normalized Delta.  The remaining
-- concrete complex-analysis obligations are exactly:
--
--   * identify one SL2(Z) element with S : tau |-> -1/tau;
--   * identify the denominator on -conjugate(z);
--   * prove Delta(-conjugate z) = conjugate(Delta z);
--   * instantiate the ordinary complex phase/half-turn quotient.
--
-- The existing finite-real-q-series owner already proves the finite Horner
-- conjugation mechanism.  It is retained below as supporting substrate, not
-- silently promoted to the infinite analytic Delta theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Analysis.FiniteRealQSeriesReflectionExact as FiniteReflection
import DASHI.Analysis.ConcreteComplexConjugationProductExact as ConcreteConjugation
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Eisenstein
import DASHI.Moonshine.EisensteinDiscriminantWeight12Exact as Disc
import DASHI.Moonshine.DeltaNormalizedWeight12SameObjectExact as Delta12
import DASHI.Interop.LeanMoonshineEisensteinAnalyticParityExact as LeanParity
import DASHI.Interop.LeanMoonshineDeltaIdentityPinnedReceiptExact as DeltaIdentityReceipt
import DASHI.Interop.Round11MachinLeanBindingManifestExact as ReplayManifest
import DASHI.Interop.LeanEta24PinnedReflectionParityExact as EtaParity
import DASHI.Interop.LeanEta24SixfoldPhaseParityExact as EtaPhaseParity
import DASHI.Interop.LeanDeltaFinalMinCutParityExact as FinalMinCutParity

------------------------------------------------------------------------
-- 1. Concrete-complex seam over the existing analytic model.
------------------------------------------------------------------------

record DeltaConjugationSInterface
    (M : Eisenstein.EisensteinAnalyticModel)
    (A : Disc.DiscriminantAlgebra M)
    (N : Delta12.WeightCompatibleNormalization M) : Set₁ where
  field
    conjugateScalar :
      Eisenstein.Scalar M → Eisenstein.Scalar M

    parameterAsScalar :
      Eisenstein.Parameter M → Eisenstein.Scalar M

    negConjugateParameter :
      Eisenstein.Parameter M → Eisenstein.Parameter M

    reciprocalConjugateParameter :
      Eisenstein.Parameter M → Eisenstein.Parameter M

    sElement : Eisenstein.SL2Z

    sActsOnNegConjugate :
      (z : Eisenstein.Parameter M) →
      Eisenstein.actParameter M sElement (negConjugateParameter z)
      ≡ reciprocalConjugateParameter z

    weight12FactorAtNegConjugate :
      (z : Eisenstein.Parameter M) →
      Eisenstein.power M
        (Eisenstein.denominator M sElement (negConjugateParameter z))
        12
      ≡
      conjugateScalar
        (Eisenstein.power M (parameterAsScalar z) 12)

    deltaNegConjugation :
      (z : Eisenstein.Parameter M) →
      Delta12.normalizedDelta M A N (negConjugateParameter z)
      ≡
      conjugateScalar (Delta12.normalizedDelta M A N z)

    conjugateProduct :
      (left right : Eisenstein.Scalar M) →
      conjugateScalar (Eisenstein._*ˢ_ M left right)
      ≡
      Eisenstein._*ˢ_ M
        (conjugateScalar left)
        (conjugateScalar right)

open DeltaConjugationSInterface public

------------------------------------------------------------------------
-- 2. Reflection identity derived, not postulated.
------------------------------------------------------------------------

deltaReciprocalConjugateReflection :
  (M : Eisenstein.EisensteinAnalyticModel) →
  (A : Disc.DiscriminantAlgebra M) →
  (N : Delta12.WeightCompatibleNormalization M) →
  (I : DeltaConjugationSInterface M A N) →
  (z : Eisenstein.Parameter M) →
  Delta12.normalizedDelta M A N (reciprocalConjugateParameter I z)
  ≡
  conjugateScalar I
    (Eisenstein._*ˢ_ M
      (Eisenstein.power M (parameterAsScalar I z) 12)
      (Delta12.normalizedDelta M A N z))
deltaReciprocalConjugateReflection M A N I z =
  trans
    (cong
      (Delta12.normalizedDelta M A N)
      (sym (sActsOnNegConjugate I z)))
    (trans
      (Delta12.normalizedDeltaTransformsAtWeight12
        M A N (sElement I) (negConjugateParameter I z))
      (trans
        (cong₂
          (Eisenstein._*ˢ_ M)
          (weight12FactorAtNegConjugate I z)
          (deltaNegConjugation I z))
        (sym
          (conjugateProduct I
            (Eisenstein.power M (parameterAsScalar I z) 12)
            (Delta12.normalizedDelta M A N z)))))

------------------------------------------------------------------------
-- 3. Fixed locus: |z|=1 is represented by reciprocal-conjugate(z)=z.
------------------------------------------------------------------------

record ReciprocalConjugateFixed
    {M : Eisenstein.EisensteinAnalyticModel}
    {A : Disc.DiscriminantAlgebra M}
    {N : Delta12.WeightCompatibleNormalization M}
    (I : DeltaConjugationSInterface M A N)
    (z : Eisenstein.Parameter M) : Set where
  constructor reciprocal-conjugate-fixed
  field
    fixed :
      reciprocalConjugateParameter I z ≡ z

open ReciprocalConjugateFixed public

deltaFixedLocusReflection :
  (M : Eisenstein.EisensteinAnalyticModel) →
  (A : Disc.DiscriminantAlgebra M) →
  (N : Delta12.WeightCompatibleNormalization M) →
  (I : DeltaConjugationSInterface M A N) →
  (z : Eisenstein.Parameter M) →
  ReciprocalConjugateFixed I z →
  Delta12.normalizedDelta M A N z
  ≡
  conjugateScalar I
    (Eisenstein._*ˢ_ M
      (Eisenstein.power M (parameterAsScalar I z) 12)
      (Delta12.normalizedDelta M A N z))
deltaFixedLocusReflection M A N I z fixedPoint =
  trans
    (cong
      (Delta12.normalizedDelta M A N)
      (sym (fixed fixedPoint)))
    (deltaReciprocalConjugateReflection M A N I z)

------------------------------------------------------------------------
-- 4. Phase readout.
--
-- The first theorem below derives the exact fixed-locus phase equation
--
--   phi = -(12 theta + phi)
--
-- in whatever continuous phase carrier a concrete complex implementation
-- supplies.  A separate half-turn quotient law then yields
--
--   phi == -6 theta   (mod pi).
--
-- Keeping the quotient law explicit avoids smuggling division-by-two through
-- an abstract phase type.
------------------------------------------------------------------------

record DeltaPhaseReadout
    (M : Eisenstein.EisensteinAnalyticModel)
    (A : Disc.DiscriminantAlgebra M)
    (N : Delta12.WeightCompatibleNormalization M)
    (I : DeltaConjugationSInterface M A N) : Set₁ where
  field
    Phase : Set

    phaseOfValue :
      Eisenstein.Scalar M → Phase

    phaseOfPoint :
      Eisenstein.Parameter M → Phase

    negatePhase : Phase → Phase
    addPhase : Phase → Phase → Phase
    scalePhase : Nat → Phase → Phase

    SameModuloHalfTurn : Phase → Phase → Set

    phaseOfConjugatedWeight12Product :
      (z : Eisenstein.Parameter M) →
      (value : Eisenstein.Scalar M) →
      phaseOfValue
        (conjugateScalar I
          (Eisenstein._*ˢ_ M
            (Eisenstein.power M (parameterAsScalar I z) 12)
            value))
      ≡
      negatePhase
        (addPhase
          (scalePhase 12 (phaseOfPoint z))
          (phaseOfValue value))

    reflectionEquationImpliesSixfoldModuloHalfTurn :
      (z : Eisenstein.Parameter M) →
      (value : Eisenstein.Scalar M) →
      phaseOfValue value
      ≡
      negatePhase
        (addPhase
          (scalePhase 12 (phaseOfPoint z))
          (phaseOfValue value))
      →
      SameModuloHalfTurn
        (phaseOfValue value)
        (negatePhase (scalePhase 6 (phaseOfPoint z)))

open DeltaPhaseReadout public

deltaFixedLocusPhaseEquation :
  (M : Eisenstein.EisensteinAnalyticModel) →
  (A : Disc.DiscriminantAlgebra M) →
  (N : Delta12.WeightCompatibleNormalization M) →
  (I : DeltaConjugationSInterface M A N) →
  (P : DeltaPhaseReadout M A N I) →
  (z : Eisenstein.Parameter M) →
  ReciprocalConjugateFixed I z →
  phaseOfValue P (Delta12.normalizedDelta M A N z)
  ≡
  negatePhase P
    (addPhase P
      (scalePhase P 12 (phaseOfPoint P z))
      (phaseOfValue P (Delta12.normalizedDelta M A N z)))
deltaFixedLocusPhaseEquation M A N I P z fixedPoint =
  trans
    (cong
      (phaseOfValue P)
      (deltaFixedLocusReflection M A N I z fixedPoint))
    (phaseOfConjugatedWeight12Product P z
      (Delta12.normalizedDelta M A N z))

deltaFixedLocusSixfoldModuloHalfTurn :
  (M : Eisenstein.EisensteinAnalyticModel) →
  (A : Disc.DiscriminantAlgebra M) →
  (N : Delta12.WeightCompatibleNormalization M) →
  (I : DeltaConjugationSInterface M A N) →
  (P : DeltaPhaseReadout M A N I) →
  (z : Eisenstein.Parameter M) →
  ReciprocalConjugateFixed I z →
  SameModuloHalfTurn P
    (phaseOfValue P (Delta12.normalizedDelta M A N z))
    (negatePhase P (scalePhase P 6 (phaseOfPoint P z)))
deltaFixedLocusSixfoldModuloHalfTurn M A N I P z fixedPoint =
  reflectionEquationImpliesSixfoldModuloHalfTurn P
    z
    (Delta12.normalizedDelta M A N z)
    (deltaFixedLocusPhaseEquation M A N I P z fixedPoint)

------------------------------------------------------------------------
-- 5. Honest frontier.
------------------------------------------------------------------------

record DeltaReflectionPhaseBoundary : Set where
  constructor delta-reflection-phase-boundary
  field
    weight12LawConsumedFromExistingTheorem : Bool
    reflectionIdentityDerivedRatherThanPostulated : Bool
    fixedLocusValueIdentityDerived : Bool
    sixfoldPhaseTheoremConditionalOnPhaseQuotient : Bool
    finiteRealQSeriesConjugationSubstrateAlreadyOwned : Bool
    concreteComplexConjugationProductDerived : Bool
    leanNormalizedDeltaWeight12SActionOwned : Bool
    leanNormalizedDeltaConjugationOwned : Bool
    leanInverseConjugationReflectionOwned : Bool
    leanUnitNormFixedLocusOwned : Bool
    leanFixedLocusValueIdentityOwned : Bool
    agdaBishopSetoidRouteBSourceOwned : Bool
    leanVendoredBishopEvaluatorFaithful : Bool
    leanExpSinCosMachinPiSemanticsCompiled : Bool
    leanRound11MachinBindingCompilerOwned : Bool
    leanMappedSourceE4E6ConvergenceOwned : Bool
    leanEta24Weight12SOwnedAtPinnedMathlib : Bool
    leanEta24ConjugationOwnedAtPinnedMathlib : Bool
    leanEta24InverseConjugationOwnedAtPinnedMathlib : Bool
    leanEta24FixedLocusValueIdentityOwned : Bool
    leanEta24BranchFreePhaseExponentialOwned : Bool
    leanEta24IntegerPiCongruenceOwned : Bool
    leanEta24SixfoldPhaseOwned : Bool
    leanEta24ArgCongruentNegativeSixOwned : Bool
    leanEta24ContinuousArgumentBranchAvoided : Bool
    leanFinalDeltaOnePropositionMinCutOwned : Bool
    leanNormalizedDeltaNonvanishingCompilerFromMinCutOwned : Bool
    leanNormalizedDeltaUnconditionalSixfoldCompilerFromMinCutOwned : Bool
    reciprocalRound11MachinBindingManifestOwned : Bool
    reciprocalManifestMatchesCurrentSourceBlobs : Bool

    primitiveAgdaRealToLeanRealExtractionInhabited : Bool
    actualAgdaRound11MachinBindingInLean : Bool
    normalizedAgdaDeltaSameObjectWithLeanTarget : Bool
    eta24NormalizedDeltaSameObject : Bool
    concreteComplexSActionInstantiated : Bool
    infiniteDeltaConjugationProvedHere : Bool
    concreteContinuousPhaseReadoutInstantiated : Bool
    unconditionalArcPhaseTheoremClosed : Bool

    nextResidual : String

open DeltaReflectionPhaseBoundary public

canonicalDeltaReflectionPhaseBoundary : DeltaReflectionPhaseBoundary
canonicalDeltaReflectionPhaseBoundary =
  delta-reflection-phase-boundary
    true true true true true true
    true true true true true
    true true true true true
    true true true true
    true true true true true
    true true true true true
    false false false true false false false false
    "The reflection and phase mathematics is now machine-formalized on the pinned Lean targets. The normalized E4/E6 target is a weight-12 modular form with inverse-conjugation and unit-circle fixed-locus identities. Independently, eta^24 has a no-dependency-bump weight-12 S/T theorem, direct q-product conjugation, inverse-conjugation reflection and the same fixed-locus value identity at Mathlib v4.28. Integration.MoonshineEta24SixfoldPhase now consumes eta nonvanishing plus that fixed-locus identity to prove the branch-free exponential phase equation exp(i(2 arg eta^24 + 12 arg tau))=1 and the exact integer-pi consequence arg eta^24 + 6 arg tau = k*pi, equivalently arg eta^24 = -6 arg tau + k*pi, without choosing a continuous argument branch. Agda remains source-pinned to the vendored Bishop setoid carrier, Round11 trig data and bishopMachinPi. The former final normalized-Delta same-object leaf is now closed in the pinned Lean companion by Integration.MoonshineDeltaIdentityPinned and canonically inhabited by Integration.MoonshineDeltaFinalMinCut: eta^24 = normalized(E4^3-E6^2)/1728, normalized-Delta nonvanishing, and normalized-Delta sixfold phase are hypothesis-free on that Lean target. The reciprocal Agda/Lean manifests now match all seven load-bearing source blob IDs and theorem-field bindings. The active residual is therefore only observation of the generated Round11+Machin source replay/inhabitation across the Agda/Lean boundary; no classical reflection, nonvanishing, phase-quotient, or Delta same-object theorem remains independently open."

------------------------------------------------------------------------
-- FiniteReflection is intentionally imported as provenance/theorem substrate:
-- its finiteQSeriesConjugation theorem establishes the algebraic mechanism on
-- finite real-coefficient q-series but is not equated with the infinite Delta
-- conjugation theorem.
------------------------------------------------------------------------
