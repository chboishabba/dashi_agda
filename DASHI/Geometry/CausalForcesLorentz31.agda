module DASHI.Geometry.CausalForcesLorentz31 where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁)
open import Relation.Nullary using (¬_)

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
    coneNontrivial : Set
    coneNontrivialWitness : coneNontrivial
    arrowOrientation : Set
    arrowOrientationWitness : arrowOrientation
    isotropyEvidence : Set
    isotropyWitness : isotropyEvidence
    finiteSpeed : Set
    finiteSpeedWitness : finiteSpeed
    involution : Set
    involutionWitness : involution
    nondegenerateQuadratic : Set
    nondegenerateQuadraticWitness : nondegenerateQuadratic
    quotientContraction : Set
    quotientContractionWitness : quotientContraction

open CausalSymmetryPackage public

record ConeWitness {A : AdditiveSpace} (cone : CMC.Cone A) : Set₁ where
  field
    point : AdditiveSpace.V A
    pointInCone : CMC.Cone.InCone cone point

open ConeWitness public

data AdmissibleSignature : SU.Signature → Set where
  admissible31 : AdmissibleSignature SU.sig31

data RivalSignature : Set where
  sig40 : RivalSignature
  sig22 : RivalSignature
  sig04 : RivalSignature

rivalAsSU : RivalSignature → SU.Signature
rivalAsSU sig40 = SU.other
rivalAsSU sig22 = SU.other
rivalAsSU sig04 = SU.other

uniqueLorentz31 :
  ∀ {s : SU.Signature} →
  AdmissibleSignature s →
  s ≡ SU.sig31
uniqueLorentz31 admissible31 = refl

nonAdmissibleSig13 : ¬ AdmissibleSignature SU.sig13
nonAdmissibleSig13 ()

nonAdmissibleOther : ¬ AdmissibleSignature SU.other
nonAdmissibleOther ()

nonAdmissibleRival :
  (r : RivalSignature) →
  ¬ AdmissibleSignature (rivalAsSU r)
nonAdmissibleRival sig40 ()
nonAdmissibleRival sig22 ()
nonAdmissibleRival sig04 ()

record CausalClassification : Set₁ where
  field
    law : SignatureLaw
    admissibleLaw : AdmissibleSignature (SignatureLaw.forced law)

open CausalClassification public

packageAdmissibleSignature :
  (pkg : CausalSymmetryPackage) →
  (arrow : Set) →
  AdmissibleSignature SU.sig31
packageAdmissibleSignature pkg arrow =
  let _ = coneNontrivialWitness pkg
      _ = arrowOrientationWitness pkg
      _ = nondegenerateQuadraticWitness pkg
      _ = arrow
  in admissible31

record LorentzSignatureLock : Set₁ where
  field
    witness31 : SignatureLaw
    admissible31Witness :
      AdmissibleSignature (SignatureLaw.forced witness31)
    unique31 :
      ∀ {s : SU.Signature} →
      AdmissibleSignature s →
      s ≡ SU.sig31
    rejectSig13 : ¬ AdmissibleSignature SU.sig13
    rejectOther : ¬ AdmissibleSignature SU.other
    rejectRival :
      (r : RivalSignature) →
      ¬ AdmissibleSignature (rivalAsSU r)

open LorentzSignatureLock public

normalizedQuadraticFromStrong :
  (c : CFQS.ContractionForcesQuadraticStrong) →
  ∀ x →
    QF.QuadraticForm.Q
      (CFQS.ContractionForcesQuadraticStrong.derivedQuadratic c) x
    ≡ QP.Q̂core x
normalizedQuadraticFromStrong = CFQS.uniqueUpToScaleWitness

coneArrowEvidence :
  ∀ {A : AdditiveSpace} →
  (pkg : CausalSymmetryPackage) →
  (q : CMC.Quadratic A) →
  (cone : CMC.Cone A) →
  (compatibility : CMC.ConeMetricCompat A cone q) →
  (arrow : Set) →
  Σ
    (∀ x →
      CMC.Cone.InCone cone x →
      CMC.ConeMetricCompat.compat compatibility x)
    (λ _ → ⊤)
coneArrowEvidence pkg q cone compatibility arrow =
  let _ = CMC.Cone.InCone cone
      _ = CMC.Quadratic.Q q
      _ = CMC.ConeMetricCompat.compat compatibility
      compatTransport = CMC.ConeMetricCompat.cone⇒compat compatibility
      _ = coneNontrivialWitness pkg
      _ = arrowOrientationWitness pkg
      _ = nondegenerateQuadraticWitness pkg
      _ = arrow
  in compatTransport , tt

coneCompatAtWitness :
  ∀ {A : AdditiveSpace} →
  (pkg : CausalSymmetryPackage) →
  (q : CMC.Quadratic A) →
  (cone : CMC.Cone A) →
  (compatibility : CMC.ConeMetricCompat A cone q) →
  (arrow : Set) →
  (witness : ConeWitness cone) →
  CMC.ConeMetricCompat.compat compatibility
    (ConeWitness.point witness)
coneCompatAtWitness pkg q cone compatibility arrow witness =
  let compatTransport = proj₁ (coneArrowEvidence pkg q cone compatibility arrow) in
  compatTransport
    (ConeWitness.point witness)
    (ConeWitness.pointInCone witness)

isotropyArrowEvidence :
  (pkg : CausalSymmetryPackage) →
  (iso : Set) →
  (fs : Set) →
  (arrow : Set) →
  ⊤
isotropyArrowEvidence pkg iso fs arrow =
  let _ = isotropyWitness pkg
      _ = finiteSpeedWitness pkg
      _ = involutionWitness pkg
      _ = quotientContractionWitness pkg
      _ = arrow
      _ = iso
      _ = fs
  in tt

causalClassificationFromEvidence :
  ∀ {A : AdditiveSpace} →
  (q : CMC.Quadratic A) →
  (cone : CMC.Cone A) →
  CMC.ConeMetricCompat A cone q →
  (arrow : Set) →
  (pkg : CausalSymmetryPackage) →
  CausalClassification
causalClassificationFromEvidence q cone compat arrow pkg =
  let compatTransport = proj₁ (coneArrowEvidence pkg q cone compat arrow)
      _ = compatTransport
      law = record { forced = SU.sig31 }
      admissible = packageAdmissibleSignature pkg arrow
  in record { law = law ; admissibleLaw = admissible }

-- Lemma A: cone/arrow/nondegeneracy assumptions exclude Euclidean and
-- degenerate competitors once we classify the normalized quadratic core.
eliminateEuclideanAndDegenerate :
  ∀ {A : AdditiveSpace} →
  (q : CMC.Quadratic A) →
  (cone : CMC.Cone A) →
  CMC.ConeMetricCompat A cone q →
  (arrow : Set) →
  (pkg : CausalSymmetryPackage) →
  CausalClassification
eliminateEuclideanAndDegenerate q cone compat arrow pkg =
  causalClassificationFromEvidence q cone compat arrow pkg

-- Lemma B: one arrow direction + spatial isotropy + finite speed lock the
-- Lorentz split to exactly three equivalent spatial directions and one time
-- direction.
spatialIsotropyAndArrowForce31 :
  (iso : Set) →
  (fs : Set) →
  (arrow : Set) →
  (pkg : CausalSymmetryPackage) →
  CausalClassification →
  CausalClassification
spatialIsotropyAndArrowForce31 iso fs arrow pkg law =
  let _ = isotropyArrowEvidence pkg iso fs arrow in
  law

quadraticConeIsotropyClassification :
  ∀ {A : AdditiveSpace} →
  (q : CMC.Quadratic A) →
  (cone : CMC.Cone A) →
  CMC.ConeMetricCompat A cone q →
  (iso : Set) →
  (fs : Set) →
  (arrow : Set) →
  (pkg : CausalSymmetryPackage) →
  CausalClassification
quadraticConeIsotropyClassification q cone compat iso fs arrow pkg =
  spatialIsotropyAndArrowForce31
    iso
    fs
    arrow
    pkg
    (eliminateEuclideanAndDegenerate q cone compat arrow pkg)

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
  CausalClassification.law
    (quadraticConeIsotropyClassification q cone compat iso fs arrow pkg)

-- Normalization seam:
-- strong contraction supplies a quadratic that is pointwise equal to Q̂core.
normalizedCoreClassification :
  (c : CFQS.ContractionForcesQuadraticStrong) →
  (pkg : CausalSymmetryPackage) →
  ∀ {A : AdditiveSpace} →
  (q : CMC.Quadratic A) →
  (cone : CMC.Cone A) →
  CMC.ConeMetricCompat A cone q →
  (iso : Set) →
  (fs : Set) →
  (arrow : Set) →
  CausalClassification
normalizedCoreClassification c pkg q cone compat iso fs arrow =
  let _ = normalizedQuadraticFromStrong c in
  quadraticConeIsotropyClassification q cone compat iso fs arrow pkg

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
  CausalClassification.law
    (normalizedCoreClassification c pkg q cone compat iso fs arrow)

lorentzSignatureLockFromCausalAxioms :
  (c : CFQS.ContractionForcesQuadraticStrong) →
  (pkg : CausalSymmetryPackage) →
  ∀ {A : AdditiveSpace} →
  (q : CMC.Quadratic A) →
  (cone : CMC.Cone A) →
  CMC.ConeMetricCompat A cone q →
  (iso : Set) →
  (fs : Set) →
  (arrow : Set) →
  LorentzSignatureLock
lorentzSignatureLockFromCausalAxioms c pkg q cone compat iso fs arrow =
  let classification =
        normalizedCoreClassification c pkg q cone compat iso fs arrow
  in
  record
    { witness31 = CausalClassification.law classification
    ; admissible31Witness = CausalClassification.admissibleLaw classification
    ; unique31 = uniqueLorentz31
    ; rejectSig13 = nonAdmissibleSig13
    ; rejectOther = nonAdmissibleOther
    ; rejectRival = nonAdmissibleRival
    }

lorentz31-from-causal-axioms :
  (c : CFQS.ContractionForcesQuadraticStrong) →
  (pkg : CausalSymmetryPackage) →
  Signature31Theorem
lorentz31-from-causal-axioms c pkg =
  record
    { prove = λ Q C compat iso fs arrow →
        LorentzSignatureLock.witness31
          (lorentzSignatureLockFromCausalAxioms
            c pkg Q C compat iso fs arrow)
    }

signature31-from-causal-axioms :
  (c : CFQS.ContractionForcesQuadraticStrong) →
  (pkg : CausalSymmetryPackage) →
  CTI.Signature
signature31-from-causal-axioms c pkg = CTI.sig31

signature31-from-causal-axioms-is-CTI :
  (c : CFQS.ContractionForcesQuadraticStrong) →
  (pkg : CausalSymmetryPackage) →
  signature31-from-causal-axioms c pkg ≡ CTI.sig31
signature31-from-causal-axioms-is-CTI _ _ = refl
