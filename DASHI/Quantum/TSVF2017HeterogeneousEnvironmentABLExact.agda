{-# OPTIONS --safe #-}
module DASHI.Quantum.TSVF2017HeterogeneousEnvironmentABLExact where

-- P01/P07 MAX-CUT: heterogeneous independent environmental records,
-- actual rational-complex amplitudes, and the ORIGINAL TSVF ABL interface.
--
-- Original owners: DASHI.Quantum.TSVF; DASHI.Quantum.TSVF2017OriginalComplexABLSelectedExact;
-- DASHI.Quantum.TSVF2017ComplexEnvironmentRobustnessExact;
-- DASHI.Physics.Foundations.BidirectionallyAdmissibleHistoryFibreExact.
-- Scientific sources: Aharonov/Bergmann/Lebowitz (1964), Aharonov/Vaidman,
-- Aharonov/Cohen/Landsberger (2017), Entropy 19(3):111.
--
-- This replaces the identical-site assumption by a FINITE LIST OF DISTINCT
-- two-level Hermitian record pairs. The product is valid for independently
-- prepared tensor factors; arbitrary correlated/entangled environments are
-- NOT claimed to factor. Complex gamma phases are retained to the Born step.
-- The original Q.ablProbability and admitted-history projector owners are
-- reused, not imitated by a new probability theory.
--
-- A physical pointer-controlled unitary, actual final cosmological bra,
-- selected dynamics, OS/Stone same Hamiltonian, and Clay YM mass gap are
-- NOT obtained by this finite factorization.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (tt)
open import Data.List.Base using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)

import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as C
import DASHI.Quantum.TSVF as Q
import DASHI.Quantum.TSVFComplexGammaProductBornExact as Gamma
import DASHI.Quantum.TSVF2017ComplexEnvironmentRobustnessExact as Env
import DASHI.Quantum.TSVF2017OriginalComplexABLSelectedExact as OriginalABL
import DASHI.Quantum.TSVFConcreteAdmissibleQubitABLExact as OriginalBidi
import DASHI.Physics.Foundations.TSVFAdmissibleQuantumOverlapRobustnessExact as Structural

------------------------------------------------------------------------
-- The site pairs are genuinely complex two-component records, not
-- guessed overlap numbers. Independence is represented by list product.
------------------------------------------------------------------------

record EnvironmentSite : Set where
  constructor environmentSite
  field
    rightRecord wrongRecord : Env.ComplexPointerRecord

open EnvironmentSite public

siteOverlap : EnvironmentSite → C.RationalComplex
siteOverlap s = Env.hermitianPair (rightRecord s) (wrongRecord s)

tensorOverlap : List EnvironmentSite → C.RationalComplex
tensorOverlap [] = C.oneC
tensorOverlap (s ∷ ss) = C._*c_ (siteOverlap s) (tensorOverlap ss)

siteBorn : EnvironmentSite → ℚ
siteBorn s = C.complexNormSq (siteOverlap s)

tensorBornProduct : List EnvironmentSite → ℚ
tensorBornProduct [] = 1ℚ
tensorBornProduct (s ∷ ss) = siteBorn s * tensorBornProduct ss

tensorBorn : List EnvironmentSite → ℚ
tensorBorn ss = C.complexNormSq (tensorOverlap ss)

heterogeneousTensorBornFactorization :
  (ss : List EnvironmentSite) →
  tensorBorn ss ≡ tensorBornProduct ss
heterogeneousTensorBornFactorization [] = Env.unitGammaBornIsOne
heterogeneousTensorBornFactorization (s ∷ ss) =
  trans
    (C.complexNormMultiplicative (siteOverlap s) (tensorOverlap ss))
    (cong (λ x → siteBorn s * x)
      (heterogeneousTensorBornFactorization ss))

-- The older homogeneous all-k theorem is literally a specialization.
replicateSite : EnvironmentSite → Nat → List EnvironmentSite
replicateSite s zero = []
replicateSite s (suc k) = s ∷ replicateSite s k

homogeneousOverlapMatchesExisting :
  (s : EnvironmentSite) (k : Nat) →
  tensorOverlap (replicateSite s k)
  ≡ Env.environmentOverlapAmplitude (rightRecord s) (wrongRecord s) k
homogeneousOverlapMatchesExisting s zero = refl
homogeneousOverlapMatchesExisting s (suc k) =
  cong (λ x → C._*c_ (siteOverlap s) x)
    (homogeneousOverlapMatchesExisting s k)

homogeneousBornMatchesExisting :
  (s : EnvironmentSite) (k : Nat) →
  tensorBorn (replicateSite s k)
  ≡ Env.environmentBornOverlap (rightRecord s) (wrongRecord s) k
homogeneousBornMatchesExisting s k =
  cong C.complexNormSq (homogeneousOverlapMatchesExisting s k)

------------------------------------------------------------------------
-- Original 2017 amplitude objects: arbitrary complex disturbance factors.
------------------------------------------------------------------------

selectedRightAmplitude : C.RationalComplex
selectedRightAmplitude = C.oneC

selectedWrongAmplitude :
  List C.RationalComplex → List EnvironmentSite → C.RationalComplex
selectedWrongAmplitude gammas ss =
  C._*c_ (Gamma.complexGammaProduct gammas) (tensorOverlap ss)

selectedWrongBorn :
  List C.RationalComplex → List EnvironmentSite → ℚ
selectedWrongBorn gammas ss =
  C.complexNormSq (selectedWrongAmplitude gammas ss)

heterogeneousWrongBornFactorization :
  (gammas : List C.RationalComplex) (ss : List EnvironmentSite) →
  selectedWrongBorn gammas ss
  ≡ Gamma.complexGammaBornWeight gammas * tensorBornProduct ss
heterogeneousWrongBornFactorization gammas ss =
  trans
    (C.complexNormMultiplicative
      (Gamma.complexGammaProduct gammas) (tensorOverlap ss))
    (cong₂ _*_
      (Gamma.complexGammaBornWeightIsNormOfProduct gammas)
      (heterogeneousTensorBornFactorization ss))

-- A source-independent, nonnegative true Born weight, even when a
-- postselected wrong amplitude is exactly zero.
heterogeneousWrongBornNonnegative :
  (gammas : List C.RationalComplex) (ss : List EnvironmentSite) →
  0ℚ ≤ selectedWrongBorn gammas ss
heterogeneousWrongBornNonnegative gammas ss =
  Env.complexBornNonnegative (selectedWrongAmplitude gammas ss)

------------------------------------------------------------------------
-- The EXACT original TSVF finite-complex quantum surface and projectors,
-- with a nontrivial postselection depending on ALL environmental sites.
------------------------------------------------------------------------

heterogeneousEnsemble :
  (gammas : List C.RationalComplex) (ss : List EnvironmentSite) →
  Q.TSVFEnsemble OriginalABL.finiteComplexQuantum
heterogeneousEnsemble gammas ss =
  Q.prePostSelected tt tt tt
    (Env.pointerRecord C.oneC C.oneC)
    (Env.pointerRecord
      (C.conjugateC selectedRightAmplitude)
      (C.conjugateC (selectedWrongAmplitude gammas ss)))

rightOriginalAmplitude :
  (gammas : List C.RationalComplex) (ss : List EnvironmentSite) →
  Q.transitionAmplitude (heterogeneousEnsemble gammas ss)
    OriginalABL.rightProjector
  ≡ selectedRightAmplitude
rightOriginalAmplitude gammas ss =
  OriginalABL.pairRightConjugated
    selectedRightAmplitude (selectedWrongAmplitude gammas ss)

wrongOriginalAmplitude :
  (gammas : List C.RationalComplex) (ss : List EnvironmentSite) →
  Q.transitionAmplitude (heterogeneousEnsemble gammas ss)
    OriginalABL.wrongProjector
  ≡ selectedWrongAmplitude gammas ss
wrongOriginalAmplitude gammas ss =
  OriginalABL.pairWrongConjugated
    selectedRightAmplitude (selectedWrongAmplitude gammas ss)

rightOriginalBorn :
  (gammas : List C.RationalComplex) (ss : List EnvironmentSite) →
  OriginalABL.numerator
    (Q.transitionWeight (heterogeneousEnsemble gammas ss)
      OriginalABL.rightProjector)
  ≡ 1ℚ
rightOriginalBorn gammas ss =
  trans
    (cong C.complexNormSq (rightOriginalAmplitude gammas ss))
    Env.unitGammaBornIsOne

wrongOriginalBorn :
  (gammas : List C.RationalComplex) (ss : List EnvironmentSite) →
  OriginalABL.numerator
    (Q.transitionWeight (heterogeneousEnsemble gammas ss)
      OriginalABL.wrongProjector)
  ≡ selectedWrongBorn gammas ss
wrongOriginalBorn gammas ss =
  cong C.complexNormSq (wrongOriginalAmplitude gammas ss)

originalHeterogeneousTotal :
  (gammas : List C.RationalComplex) (ss : List EnvironmentSite) →
  OriginalABL.numerator
    (Q.ProjectiveMeasurement.totalPathWeight
      OriginalABL.finiteComplexMeasurement (heterogeneousEnsemble gammas ss))
  ≡ 1ℚ + selectedWrongBorn gammas ss
originalHeterogeneousTotal gammas ss =
  cong₂ _+_
    (rightOriginalBorn gammas ss)
    (wrongOriginalBorn gammas ss)

-- This inhabits Q.Positive because the selected right amplitude is 1;
-- an arbitrary zero/non-normalizable postselection is not admitted.
positiveHeterogeneousTotal :
  (gammas : List C.RationalComplex) (ss : List EnvironmentSite) →
  Q.QuantumSurface.Positive OriginalABL.finiteComplexQuantum
    (Q.ProjectiveMeasurement.totalPathWeight
      OriginalABL.finiteComplexMeasurement (heterogeneousEnsemble gammas ss))
positiveHeterogeneousTotal gammas ss =
  selectedWrongBorn gammas ss ,
    (originalHeterogeneousTotal gammas ss ,
     heterogeneousWrongBornNonnegative gammas ss)

heterogeneousABLContext :
  (gammas : List C.RationalComplex) (ss : List EnvironmentSite) →
  Q.ABLContext OriginalABL.finiteComplexQuantum
    OriginalABL.finiteComplexMeasurement (heterogeneousEnsemble gammas ss)
heterogeneousABLContext gammas ss =
  Q.ablContext (positiveHeterogeneousTotal gammas ss)

rightABL :
  (gammas : List C.RationalComplex) (ss : List EnvironmentSite) →
  OriginalABL.FractionWeight
rightABL gammas ss =
  Q.ablProbability (heterogeneousABLContext gammas ss)
    OriginalBidi.selectedRight

wrongABL :
  (gammas : List C.RationalComplex) (ss : List EnvironmentSite) →
  OriginalABL.FractionWeight
wrongABL gammas ss =
  Q.ablProbability (heterogeneousABLContext gammas ss)
    OriginalBidi.selectedWrong

rightABLNumerator :
  (gammas : List C.RationalComplex) (ss : List EnvironmentSite) →
  OriginalABL.numerator (rightABL gammas ss) ≡ 1ℚ
rightABLNumerator gammas ss =
  trans
    (cong (λ x → x * 1ℚ) (rightOriginalBorn gammas ss))
    (ℚₚ.*-identityʳ 1ℚ)

wrongABLNumerator :
  (gammas : List C.RationalComplex) (ss : List EnvironmentSite) →
  OriginalABL.numerator (wrongABL gammas ss)
  ≡ selectedWrongBorn gammas ss
wrongABLNumerator gammas ss =
  trans
    (cong (λ x → x * 1ℚ) (wrongOriginalBorn gammas ss))
    (ℚₚ.*-identityʳ (selectedWrongBorn gammas ss))

rightABLDenominator :
  (gammas : List C.RationalComplex) (ss : List EnvironmentSite) →
  OriginalABL.denominator (rightABL gammas ss)
  ≡ 1ℚ + selectedWrongBorn gammas ss
rightABLDenominator gammas ss =
  trans
    (ℚₚ.*-identityˡ
      (OriginalABL.numerator
        (Q.ProjectiveMeasurement.totalPathWeight
          OriginalABL.finiteComplexMeasurement
          (heterogeneousEnsemble gammas ss))))
    (originalHeterogeneousTotal gammas ss)

-- This is normalization on ORIGINAL Q.ablProbability, not a bespoke ratio.
heterogeneousOriginalABLNormalizes :
  (gammas : List C.RationalComplex) (ss : List EnvironmentSite) →
  OriginalABL.numerator (rightABL gammas ss)
    + OriginalABL.numerator (wrongABL gammas ss)
  ≡ OriginalABL.denominator (rightABL gammas ss)
heterogeneousOriginalABLNormalizes gammas ss =
  trans
    (cong₂ _+_ (rightABLNumerator gammas ss)
      (wrongABLNumerator gammas ss))
    (sym (rightABLDenominator gammas ss))

heterogeneousOriginalABLHasCorrectBornFactor :
  (gammas : List C.RationalComplex) (ss : List EnvironmentSite) →
  OriginalABL.numerator (wrongABL gammas ss)
  ≡ Gamma.complexGammaBornWeight gammas * tensorBornProduct ss
heterogeneousOriginalABLHasCorrectBornFactor gammas ss =
  trans
    (wrongABLNumerator gammas ss)
    (heterogeneousWrongBornFactorization gammas ss)

-- Same original nonvacuous two-boundary source: two admitted histories,
-- one excluded, with the SAME physical candidate ensemble.
actualHeterogeneousAdmissibleSource :
  (gammas : List C.RationalComplex) (ss : List EnvironmentSite) →
  Structural.AdmissibleTSVFQuantumSource
    OriginalBidi.jointAdmissibleHistoryFibre
    OriginalABL.finiteComplexQuantum
    (heterogeneousEnsemble gammas ss)
actualHeterogeneousAdmissibleSource gammas ss = record
  { initial = tt
  ; final = tt
  ; rightHistory = OriginalBidi.admittedRightHistory
  ; wrongHistory = OriginalBidi.admittedWrongHistory
  ; rightAllowed = OriginalBidi.admittedRightProof
  ; wrongAllowed = OriginalBidi.admittedWrongProof
  ; projectorOf = OriginalABL.projectorOfAdmittedHistory
  }

admittedWrongHistoryAmplitudeIsProduct :
  (gammas : List C.RationalComplex) (ss : List EnvironmentSite) →
  Structural.wrongAmplitude (actualHeterogeneousAdmissibleSource gammas ss)
  ≡ selectedWrongAmplitude gammas ss
admittedWrongHistoryAmplitudeIsProduct gammas ss =
  wrongOriginalAmplitude gammas ss

-- The remaining 2017 PHYSICAL cut is constructing the selected source
-- dynamics and its genuine pointer/environment unitary, not guessing the
-- site list or postselected final state, and then proving the continuous
-- observer generator equals the original OS reconstructed Hamiltonian.
