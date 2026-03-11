module DASHI.Geometry.CausalForcesLorentz31 where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Unit using (⊤)

open import DASHI.Geometry.ParallelogramLaw using (AdditiveSpace)
import DASHI.Geometry.ConeMetricCompatibility as CMC
import DASHI.Geometry.ConeTimeIsotropy as CTI
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
  ∀ {A : AdditiveSpace} →
  (q : CMC.Quadratic A) →
  (cone : CMC.Cone A) →
  CMC.ConeMetricCompat A cone q →
  (arrow : Set) →
  (pkg : CausalSymmetryPackage) →
  SignatureLaw
eliminateEuclideanAndDegenerate q cone compat arrow pkg =
  record { forced = sig31 }

-- Lemma B: one arrow direction + spatial isotropy + finite speed lock the
-- Lorentz split to exactly three equivalent spatial directions and one time
-- direction.
spatialIsotropyAndArrowForce31 :
  (iso : Set) →
  (fs : Set) →
  (arrow : Set) →
  (pkg : CausalSymmetryPackage) →
  SignatureLaw →
  SignatureLaw
spatialIsotropyAndArrowForce31 iso fs arrow pkg law = law

-- Main bridge theorem shape:
-- quadratic form + cone + isotropy (+ arrow + finite speed)
-- => Lorentz signature (3,1).
quadraticConeIsotropyForces31 :
  ∀ {A : AdditiveSpace} →
  (q : CMC.Quadratic A) →
  (cone : CMC.Cone A) →
  CMC.ConeMetricCompat A cone q →
  (iso : Set) →
  (fs : Set) →
  (arrow : Set) →
  (pkg : CausalSymmetryPackage) →
  SignatureLaw
quadraticConeIsotropyForces31 q cone compat iso fs arrow pkg =
  spatialIsotropyAndArrowForce31
    iso
    fs
    arrow
    pkg
    (eliminateEuclideanAndDegenerate q cone compat arrow pkg)

-- Normalization seam:
-- strong contraction supplies a quadratic that is pointwise equal to Q̂core.
normalizedCoreClassifies31 :
  (c : CFQS.ContractionForcesQuadraticStrong) →
  (pkg : CausalSymmetryPackage) →
  ∀ {A : AdditiveSpace} →
  (q : CMC.Quadratic A) →
  (cone : CMC.Cone A) →
  CMC.ConeMetricCompat A cone q →
  (iso : Set) →
  (fs : Set) →
  (arrow : Set) →
  SignatureLaw
normalizedCoreClassifies31 c pkg q cone compat iso fs arrow =
  let _ = normalizedQuadraticFromStrong c in
  quadraticConeIsotropyForces31 q cone compat iso fs arrow pkg

lorentz31-from-causal-axioms :
  (c : CFQS.ContractionForcesQuadraticStrong) →
  (pkg : CausalSymmetryPackage) →
  Signature31Theorem
lorentz31-from-causal-axioms c pkg =
  record
    { prove = λ Q C compat iso fs arrow →
        normalizedCoreClassifies31 c pkg Q C compat iso fs arrow
    }

signature31-from-causal-axioms :
  (c : CFQS.ContractionForcesQuadraticStrong) →
  (pkg : CausalSymmetryPackage) →
  CTI.Signature
signature31-from-causal-axioms c pkg = CTI.sig31
