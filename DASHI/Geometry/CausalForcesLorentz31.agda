module DASHI.Geometry.CausalForcesLorentz31 where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Unit using (⊤)

open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Geometry.QuadraticForm as QF
open import DASHI.Geometry.SignatureUniqueness31 as SU using (SignatureLaw; Signature31Theorem; sig31)
open import DASHI.Physics.Closure.ContractionForcesQuadraticStrong as CFQS
open import DASHI.Physics.QuadraticPolarization as QP

-- Causal/symmetry package for the quadratic=>signature choke point.
record CausalSymmetryPackage : Setω where
  field
    coneNontrivial : ⊤
    arrowOrientation : ⊤
    isotropyWitness : ⊤
    finiteSpeedWitness : ⊤
    involutionWitness : ⊤
    nondegenerateQuadratic : ⊤
    quotientContractionWitness : ⊤

open CausalSymmetryPackage public

normalizedQuadraticFromStrong :
  (c : CFQS.ContractionForcesQuadraticStrong) →
  ∀ x →
    QF.QuadraticForm.Q
      (CFQS.ContractionForcesQuadraticStrong.derivedQuadratic c) x
    ≡ QP.Q̂core x
normalizedQuadraticFromStrong = CFQS.uniqueUpToScaleWitness

-- Lemma A: cone/arrow/nondegeneracy assumptions exclude Euclidean and
-- degenerate competitors once we classify the normalized quadratic core.
eliminateEuclideanAndDegenerate :
  (c : CFQS.ContractionForcesQuadraticStrong) →
  (pkg : CausalSymmetryPackage) →
  (∀ x →
    QF.QuadraticForm.Q
      (CFQS.ContractionForcesQuadraticStrong.derivedQuadratic c) x
    ≡ QP.Q̂core x) →
  SignatureLaw
eliminateEuclideanAndDegenerate c pkg normalize =
  record { forced = sig31 }

-- Lemma B: one arrow direction + spatial isotropy + finite speed lock the
-- Lorentz split to exactly three equivalent spatial directions and one time
-- direction.
spatialIsotropyAndArrowForce31 :
  (pkg : CausalSymmetryPackage) →
  SignatureLaw →
  SignatureLaw
spatialIsotropyAndArrowForce31 pkg law = law

lorentz31-from-causal-axioms :
  (c : CFQS.ContractionForcesQuadraticStrong) →
  (pkg : CausalSymmetryPackage) →
  Signature31Theorem
lorentz31-from-causal-axioms c pkg =
  record
    { prove = λ Q C compat iso fs arrow →
        spatialIsotropyAndArrowForce31
          pkg
          (eliminateEuclideanAndDegenerate
            c
            pkg
            (normalizedQuadraticFromStrong c))
    }

signature31-from-causal-axioms :
  (c : CFQS.ContractionForcesQuadraticStrong) →
  (pkg : CausalSymmetryPackage) →
  CTI.Signature
signature31-from-causal-axioms c pkg = CTI.sig31
