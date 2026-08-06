module DASHI.Physics.Closure.NSTriadKNLuoFiniteProjectedShellEquation42Exact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Derive the finite projected shell energy equation from the literal rational
-- Leray multiplier and a finite triad list.  The nonlinear right-hand side is
-- not an independent field: it is the negative pairing of the shell mode with
-- the recursively summed triad coefficient.  Linearity of the pairing proves
-- that this equals the complete signed triad fold.  Boolean range decisions
-- then derive the exact J1/J2, J11/J12, and lower/upper J11 decompositions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; -_; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq
  using (cong; subst; sym; trans)
open Eq.≡-Reasoning

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as Leray
import DASHI.Physics.Closure.NSTriadKNRationalLeraySelfAdjointExact as SelfAdjoint
import DASHI.Physics.Closure.NSTriadKNRationalLerayFiniteConvolutionExact as Convolution
import DASHI.Physics.Closure.NSTriadKNLuoEquation42FiniteRangeAssemblyExact as Assembly

vectorDotAddRight :
  (test left right : Leray.Vector3) →
  Leray.dot test (Leray.add left right)
  ≡ Leray.dot test left + Leray.dot test right
vectorDotAddRight
  (Leray.v3 tx ty tz)
  (Leray.v3 lx ly lz)
  (Leray.v3 rx ry rz) =
  solve (tx ∷ ty ∷ tz ∷ lx ∷ ly ∷ lz ∷ rx ∷ ry ∷ rz ∷ [])

negativeDotFiniteVectorSum :
  (test : Leray.Vector3) →
  (values : List Leray.Vector3) →
  - Leray.dot test (Convolution.vectorSum values)
  ≡ Assembly.sumℚ
      (Assembly.mapContribution
        (λ value → - Leray.dot test value)
        values)
negativeDotFiniteVectorSum (Leray.v3 tx ty tz) [] =
  solve (tx ∷ ty ∷ tz ∷ [])
negativeDotFiniteVectorSum test (value ∷ values)
  rewrite vectorDotAddRight test value (Convolution.vectorSum values)
        | negativeDotFiniteVectorSum test values =
  solve
    ( Leray.dot test value
    ∷ Assembly.sumℚ
        (Assembly.mapContribution
          (λ next → - Leray.dot test next)
          values)
    ∷ []
    )

record FiniteProjectedShellDynamics : Set₁ where
  field
    projectionAt : Nat → Leray.ProjectionMode
    velocity velocityDerivative : Nat → Leray.Vector3
    viscosityFrequency : Nat → ℚ
    triadVectorsAt : Nat → List Leray.Vector3

    isJ1 : Nat → Leray.Vector3 → Bool
    isJ11WithinJ1 : Nat → Leray.Vector3 → Bool
    isLowerHalfWithinJ11 : Nat → Leray.Vector3 → Bool

    velocityTransverse :
      (shell : Nat) →
      Leray.dot
        (Leray.mode (projectionAt shell))
        (velocity shell)
      ≡ 0ℚ

    shellProjectedEquation :
      (shell : Nat) →
      velocityDerivative shell
      ≡ Leray.add
          (Leray.scale
            (- viscosityFrequency shell)
            (velocity shell))
          (Leray.scale
            (- 1ℚ)
            (Leray.project
              (projectionAt shell)
              (Convolution.vectorSum (triadVectorsAt shell))))

open FiniteProjectedShellDynamics public

shellEnergyDerivative :
  FiniteProjectedShellDynamics → Nat → ℚ
shellEnergyDerivative data shell =
  Leray.dot (velocity data shell) (velocityDerivative data shell)

shellDissipation :
  FiniteProjectedShellDynamics → Nat → ℚ
shellDissipation data shell =
  viscosityFrequency data shell
  * Leray.normSquared (velocity data shell)

signedTriadContribution :
  FiniteProjectedShellDynamics → Nat → Leray.Vector3 → ℚ
signedTriadContribution data shell triad =
  - Leray.dot (velocity data shell) triad

totalSignedTriadFold :
  FiniteProjectedShellDynamics → Nat → ℚ
totalSignedTriadFold data shell =
  Assembly.sumℚ
    (Assembly.mapContribution
      (signedTriadContribution data shell)
      (triadVectorsAt data shell))

projectedShellEnergyIdentity :
  (data : FiniteProjectedShellDynamics) →
  (shell : Nat) →
  shellEnergyDerivative data shell + shellDissipation data shell
  ≡ - Leray.dot
      (velocity data shell)
      (Convolution.vectorSum (triadVectorsAt data shell))
projectedShellEnergyIdentity data shell
  rewrite shellProjectedEquation data shell
        | vectorDotAddRight
            (velocity data shell)
            (Leray.scale
              (- viscosityFrequency data shell)
              (velocity data shell))
            (Leray.scale
              (- 1ℚ)
              (Leray.project
                (projectionAt data shell)
                (Convolution.vectorSum (triadVectorsAt data shell))))
        | Leray.dotScaleRight
            (velocity data shell)
            (velocity data shell)
            (- viscosityFrequency data shell)
        | Leray.dotScaleRight
            (velocity data shell)
            (Leray.project
              (projectionAt data shell)
              (Convolution.vectorSum (triadVectorsAt data shell)))
            (- 1ℚ)
        | SelfAdjoint.removeProjectorAgainstTransverseTest
            (projectionAt data shell)
            (velocity data shell)
            (Convolution.vectorSum (triadVectorsAt data shell))
            (velocityTransverse data shell) =
  solve
    ( viscosityFrequency data shell
    ∷ Leray.normSquared (velocity data shell)
    ∷ Leray.dot
        (velocity data shell)
        (Convolution.vectorSum (triadVectorsAt data shell))
    ∷ []
    )

physicalRHSMatchesTotalInteractionFold :
  (data : FiniteProjectedShellDynamics) →
  (shell : Nat) →
  - Leray.dot
      (velocity data shell)
      (Convolution.vectorSum (triadVectorsAt data shell))
  ≡ totalSignedTriadFold data shell
physicalRHSMatchesTotalInteractionFold data shell =
  negativeDotFiniteVectorSum
    (velocity data shell)
    (triadVectorsAt data shell)

shellEquationAgainstTotalInteractionFold :
  (data : FiniteProjectedShellDynamics) →
  (shell : Nat) →
  shellEnergyDerivative data shell + shellDissipation data shell
  ≡ totalSignedTriadFold data shell
shellEquationAgainstTotalInteractionFold data shell =
  trans
    (projectedShellEnergyIdentity data shell)
    (physicalRHSMatchesTotalInteractionFold data shell)

finiteRangeData :
  FiniteProjectedShellDynamics → Assembly.Equation42FiniteRangeData
finiteRangeData data = record
  { Interaction = Leray.Vector3
  ; interactionsAt = triadVectorsAt data
  ; contributionAt = signedTriadContribution data
  ; isJ1 = isJ1 data
  ; isJ11WithinJ1 = isJ11WithinJ1 data
  ; isLowerHalfWithinJ11 = isLowerHalfWithinJ11 data
  ; J1DecisionHasSourceMeaning = ⊤
  ; j1DecisionHasSourceMeaning = tt
  ; J2DecisionHasSourceMeaning = ⊤
  ; j2DecisionHasSourceMeaning = tt
  ; J11DecisionHasSourceMeaning = ⊤
  ; j11DecisionHasSourceMeaning = tt
  ; LowerHalfDecisionHasSourceMeaning = ⊤
  ; lowerHalfDecisionHasSourceMeaning = tt
  }

totalInteractionMeaning :
  (data : FiniteProjectedShellDynamics) →
  (shell : Nat) →
  totalSignedTriadFold data shell
  ≡ Assembly.totalInteractionSum (finiteRangeData data) shell
totalInteractionMeaning data shell = refl

officialFiniteEquation42Equality :
  (data : FiniteProjectedShellDynamics) →
  (shell : Nat) →
  shellEnergyDerivative data shell + shellDissipation data shell
  ≡ Assembly.J1 (finiteRangeData data) shell
    + Assembly.J2 (finiteRangeData data) shell
officialFiniteEquation42Equality data shell =
  trans
    (shellEquationAgainstTotalInteractionFold data shell)
    (Assembly.J1J2Meaning (finiteRangeData data) shell)

officialFiniteEquation42 :
  (data : FiniteProjectedShellDynamics) →
  (shell : Nat) →
  shellEnergyDerivative data shell + shellDissipation data shell
  ≤ Assembly.J1 (finiteRangeData data) shell
    + Assembly.J2 (finiteRangeData data) shell
officialFiniteEquation42 data shell =
  subst
    (λ right →
      shellEnergyDerivative data shell + shellDissipation data shell
      ≤ right)
    (officialFiniteEquation42Equality data shell)
    ℚₚ.≤-refl

physicalTriadPartitionIntoJ1J2 :
  (data : FiniteProjectedShellDynamics) →
  (shell : Nat) →
  Assembly.totalInteractionSum (finiteRangeData data) shell
  ≡ Assembly.J1 (finiteRangeData data) shell
    + Assembly.J2 (finiteRangeData data) shell
physicalTriadPartitionIntoJ1J2 data shell =
  Assembly.J1J2Meaning (finiteRangeData data) shell

J1PartitionIntoJ11J12 :
  (data : FiniteProjectedShellDynamics) →
  (shell : Nat) →
  Assembly.J1 (finiteRangeData data) shell
  ≡ Assembly.J11 (finiteRangeData data) shell
    + Assembly.J12 (finiteRangeData data) shell
J1PartitionIntoJ11J12 data shell =
  Assembly.J11J12Meaning (finiteRangeData data) shell

J11PartitionIntoLowerUpper :
  (data : FiniteProjectedShellDynamics) →
  (shell : Nat) →
  Assembly.J11 (finiteRangeData data) shell
  ≡ Assembly.lowerHalfJ11 (finiteRangeData data) shell
    + Assembly.upperHalfJ11 (finiteRangeData data) shell
J11PartitionIntoLowerUpper data shell =
  Assembly.J11RangeMeaning (finiteRangeData data) shell
