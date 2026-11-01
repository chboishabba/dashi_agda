{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityFiniteHaarStrictPositivityExact where

open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; Positive; NonNegative; positive; nonNegative; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym; trans)

import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFinitePositiveWeightNormalizationExact as Normalize
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibrePositiveMassExact as Membership
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

------------------------------------------------------------------------
-- STRICT POSITIVITY FROM AN EXPLICIT FINITE HAAR QUADRATURE
--
-- The earlier RationalFiniteMeasureIntegrationLaws intentionally contains only
-- linearity.  It cannot prove Z>0.  The actual finite source may pay strict
-- positivity by exhibiting the finite quadrature behind its Haar integral:
--
--   integral f = sum_x w_H(x) f(x),
--
-- with nonnegative Haar weights and one state carrying positive Haar weight and
-- positive Gibbs density.  The same witness proves strict positivity of a
-- weighted F^2 numerator when F^2 is nonnegative everywhere and positive there.
------------------------------------------------------------------------

record FiniteRationalHaarQuadrature
    {Configuration : Set}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ) : Set₁ where
  field
    states : List Configuration
    haarWeight : Configuration → ℚ

    haarIntegralIsQuadrature :
      ∀ integrand →
      Physical.haarIntegral measure integrand
      ≡
      Sums.sumRational states
        (λ configuration →
          haarWeight configuration * integrand configuration)

    partitionFunctionIsDensityIntegral :
      Physical.partitionFunction measure
      ≡ Physical.haarIntegral measure (Physical.density measure)

    haarWeightNonnegative :
      ∀ configuration → 0ℚ ≤ haarWeight configuration

    densityNonnegative :
      ∀ configuration → 0ℚ ≤ Physical.density measure configuration

    positiveWitness : Configuration
    positiveWitnessInStates :
      Membership._∈_ positiveWitness states

    positiveWitnessHaarWeight :
      Positive (haarWeight positiveWitness)

    positiveWitnessDensity :
      Positive (Physical.density measure positiveWitness)

open FiniteRationalHaarQuadrature public

partitionWeight :
  ∀ {Configuration measure} →
  FiniteRationalHaarQuadrature
    {Configuration = Configuration} measure →
  Configuration → ℚ
partitionWeight {measure = measure} quadrature configuration =
  haarWeight quadrature configuration
  * Physical.density measure configuration

partitionWeightNonnegative :
  ∀ {Configuration measure}
    (quadrature :
      FiniteRationalHaarQuadrature
        {Configuration = Configuration} measure)
    configuration →
  0ℚ ≤ partitionWeight quadrature configuration
partitionWeightNonnegative {measure = measure} quadrature configuration =
  let
    instance
      hNN : NonNegative (haarWeight quadrature configuration)
      hNN = nonNegative (haarWeightNonnegative quadrature configuration)

      rhoNN : NonNegative (Physical.density measure configuration)
      rhoNN = nonNegative (densityNonnegative quadrature configuration)
  in
  ℚP.nonNegative⁻¹ _

partitionWitnessWeightPositive :
  ∀ {Configuration measure}
    (quadrature :
      FiniteRationalHaarQuadrature
        {Configuration = Configuration} measure) →
  Positive (partitionWeight quadrature (positiveWitness quadrature))
partitionWitnessWeightPositive {measure = measure} quadrature =
  let
    h = haarWeight quadrature (positiveWitness quadrature)
    rho = Physical.density measure (positiveWitness quadrature)

    instance
      hPositive : Positive h
      hPositive = positiveWitnessHaarWeight quadrature

      rhoPositive : Positive rho
      rhoPositive = positiveWitnessDensity quadrature
  in
  ℚP.pos*pos⇒pos h rho

partitionWeightFamily :
  ∀ {Configuration measure} →
  FiniteRationalHaarQuadrature
    {Configuration = Configuration} measure →
  Normalize.FinitePositiveWeightFamily Configuration
partitionWeightFamily quadrature = record
  { Normalize.FinitePositiveWeightFamily.states =
      states quadrature
  ; Normalize.FinitePositiveWeightFamily.rawWeight =
      partitionWeight quadrature
  ; Normalize.FinitePositiveWeightFamily.rawWeightNonnegative =
      partitionWeightNonnegative quadrature
  ; Normalize.FinitePositiveWeightFamily.positiveWitness =
      positiveWitness quadrature
  ; Normalize.FinitePositiveWeightFamily.positiveWitnessInStates =
      positiveWitnessInStates quadrature
  ; Normalize.FinitePositiveWeightFamily.positiveWitnessWeight =
      partitionWitnessWeightPositive quadrature
  }

partitionFunctionIsFinitePositiveMass :
  ∀ {Configuration measure}
    (quadrature :
      FiniteRationalHaarQuadrature
        {Configuration = Configuration} measure) →
  Physical.partitionFunction measure
  ≡ Normalize.totalMass (partitionWeightFamily quadrature)
partitionFunctionIsFinitePositiveMass {measure = measure} quadrature =
  trans
    (partitionFunctionIsDensityIntegral quadrature)
    (haarIntegralIsQuadrature quadrature (Physical.density measure))

partitionFunctionPositive :
  ∀ {Configuration measure}
    (quadrature :
      FiniteRationalHaarQuadrature
        {Configuration = Configuration} measure) →
  0ℚ < Physical.partitionFunction measure
partitionFunctionPositive quadrature =
  let
    mass = Normalize.totalMass (partitionWeightFamily quadrature)

    instance
      massPositive : Positive mass
      massPositive =
        Normalize.totalMassPositive (partitionWeightFamily quadrature)
  in
  subst
    (λ value → 0ℚ < value)
    (sym (partitionFunctionIsFinitePositiveMass quadrature))
    (ℚP.positive⁻¹ mass)

------------------------------------------------------------------------
-- STRICT POSITIVITY OF A WEIGHTED F^2 NUMERATOR.
------------------------------------------------------------------------

record PositiveFieldStrengthSquareWitness
    {Configuration : Set}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ}
    (quadrature : FiniteRationalHaarQuadrature measure)
    (fieldStrengthSquare : Configuration → ℚ) : Set where
  field
    fieldStrengthSquareNonnegative :
      ∀ configuration → 0ℚ ≤ fieldStrengthSquare configuration

    fieldStrengthSquarePositiveAtWitness :
      Positive
        (fieldStrengthSquare (positiveWitness quadrature))

open PositiveFieldStrengthSquareWitness public

fieldStrengthSquareWeight :
  ∀ {Configuration measure}
    (quadrature :
      FiniteRationalHaarQuadrature
        {Configuration = Configuration} measure)
    (fieldStrengthSquare : Configuration → ℚ) →
  Configuration → ℚ
fieldStrengthSquareWeight {measure = measure}
    quadrature fieldStrengthSquare configuration =
  partitionWeight quadrature configuration
  * fieldStrengthSquare configuration

fieldStrengthSquareWeightNonnegative :
  ∀ {Configuration measure}
    (quadrature :
      FiniteRationalHaarQuadrature
        {Configuration = Configuration} measure)
    (fieldStrengthSquare : Configuration → ℚ)
    (witness :
      PositiveFieldStrengthSquareWitness
        quadrature fieldStrengthSquare)
    configuration →
  0ℚ ≤ fieldStrengthSquareWeight quadrature fieldStrengthSquare configuration
fieldStrengthSquareWeightNonnegative
    quadrature fieldStrengthSquare witness configuration =
  let
    instance
      partitionNN :
        NonNegative (partitionWeight quadrature configuration)
      partitionNN =
        nonNegative (partitionWeightNonnegative quadrature configuration)

      f2NN :
        NonNegative (fieldStrengthSquare configuration)
      f2NN =
        nonNegative
          (fieldStrengthSquareNonnegative witness configuration)
  in
  ℚP.nonNegative⁻¹ _

fieldStrengthSquareWitnessWeightPositive :
  ∀ {Configuration measure}
    (quadrature :
      FiniteRationalHaarQuadrature
        {Configuration = Configuration} measure)
    (fieldStrengthSquare : Configuration → ℚ)
    (witness :
      PositiveFieldStrengthSquareWitness
        quadrature fieldStrengthSquare) →
  Positive
    (fieldStrengthSquareWeight
      quadrature fieldStrengthSquare
      (positiveWitness quadrature))
fieldStrengthSquareWitnessWeightPositive
    quadrature fieldStrengthSquare witness =
  let
    partition =
      partitionWeight quadrature (positiveWitness quadrature)
    f2 =
      fieldStrengthSquare (positiveWitness quadrature)

    instance
      partitionPositive : Positive partition
      partitionPositive =
        partitionWitnessWeightPositive quadrature

      f2Positive : Positive f2
      f2Positive =
        fieldStrengthSquarePositiveAtWitness witness
  in
  ℚP.pos*pos⇒pos partition f2

fieldStrengthSquareWeightFamily :
  ∀ {Configuration measure}
    (quadrature :
      FiniteRationalHaarQuadrature
        {Configuration = Configuration} measure)
    (fieldStrengthSquare : Configuration → ℚ)
    (witness :
      PositiveFieldStrengthSquareWitness
        quadrature fieldStrengthSquare) →
  Normalize.FinitePositiveWeightFamily Configuration
fieldStrengthSquareWeightFamily quadrature fieldStrengthSquare witness = record
  { Normalize.FinitePositiveWeightFamily.states =
      states quadrature
  ; Normalize.FinitePositiveWeightFamily.rawWeight =
      fieldStrengthSquareWeight quadrature fieldStrengthSquare
  ; Normalize.FinitePositiveWeightFamily.rawWeightNonnegative =
      fieldStrengthSquareWeightNonnegative
        quadrature fieldStrengthSquare witness
  ; Normalize.FinitePositiveWeightFamily.positiveWitness =
      positiveWitness quadrature
  ; Normalize.FinitePositiveWeightFamily.positiveWitnessInStates =
      positiveWitnessInStates quadrature
  ; Normalize.FinitePositiveWeightFamily.positiveWitnessWeight =
      fieldStrengthSquareWitnessWeightPositive
        quadrature fieldStrengthSquare witness
  }

fieldStrengthSquareNumerator :
  ∀ {Configuration measure} →
  (quadrature :
    FiniteRationalHaarQuadrature
      {Configuration = Configuration} measure) →
  (Configuration → ℚ) → ℚ
fieldStrengthSquareNumerator {measure = measure}
    quadrature fieldStrengthSquare =
  Physical.haarIntegral measure
    (λ configuration →
      Physical.density measure configuration
      * fieldStrengthSquare configuration)

fieldStrengthSquareNumeratorIsFinitePositiveMass :
  ∀ {Configuration measure}
    (quadrature :
      FiniteRationalHaarQuadrature
        {Configuration = Configuration} measure)
    (fieldStrengthSquare : Configuration → ℚ)
    (witness :
      PositiveFieldStrengthSquareWitness
        quadrature fieldStrengthSquare) →
  fieldStrengthSquareNumerator quadrature fieldStrengthSquare
  ≡
  Normalize.totalMass
    (fieldStrengthSquareWeightFamily
      quadrature fieldStrengthSquare witness)
fieldStrengthSquareNumeratorIsFinitePositiveMass
    {measure = measure} quadrature fieldStrengthSquare witness =
  haarIntegralIsQuadrature quadrature
    (λ configuration →
      Physical.density measure configuration
      * fieldStrengthSquare configuration)

fieldStrengthSquareNumeratorPositive :
  ∀ {Configuration measure}
    (quadrature :
      FiniteRationalHaarQuadrature
        {Configuration = Configuration} measure)
    (fieldStrengthSquare : Configuration → ℚ)
    (witness :
      PositiveFieldStrengthSquareWitness
        quadrature fieldStrengthSquare) →
  0ℚ < fieldStrengthSquareNumerator quadrature fieldStrengthSquare
fieldStrengthSquareNumeratorPositive
    quadrature fieldStrengthSquare witness =
  let
    family =
      fieldStrengthSquareWeightFamily
        quadrature fieldStrengthSquare witness
    mass = Normalize.totalMass family

    instance
      massPositive : Positive mass
      massPositive = Normalize.totalMassPositive family
  in
  subst
    (λ value → 0ℚ < value)
    (sym
      (fieldStrengthSquareNumeratorIsFinitePositiveMass
        quadrature fieldStrengthSquare witness))
    (ℚP.positive⁻¹ mass)
