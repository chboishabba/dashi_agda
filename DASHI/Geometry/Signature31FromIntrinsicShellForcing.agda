module DASHI.Geometry.Signature31FromIntrinsicShellForcing where

open import Level using (_⊔_; suc)
open import Agda.Primitive using (Setω)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Geometry.QuadraticForm
open import DASHI.Geometry.ProjectionDefect using (Additive)
open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Geometry.SignatureUniqueness31 as SU using (Signature31Theorem)
open import DASHI.Geometry.CausalForcesLorentz31 as CFL
open import DASHI.Geometry.ConeArrowIsotropyOrbitProfile as CAOP
open import DASHI.Geometry.ConeArrowIsotropyShellAction as CAS
open import DASHI.Geometry.ConeArrowShellStratification as CASS
open import DASHI.Geometry.ConeArrowOrbitStructure as CAOS
open import DASHI.Geometry.ConeArrowOrientationAsymmetry as CAOA
open import DASHI.Geometry.SignatureExclusionFromOrbitProfile as SEFP
open import DASHI.Physics.Closure.ContractionForcesQuadraticStrong as CFQS
open import DASHI.Physics.OrbitSignatureDiscriminant as OSD

record IntrinsicSignatureCoreAxioms : Setω where
  field
    strengthenedContraction : CFQS.ContractionForcesQuadraticStrong
    causalSymmetry : CFL.CausalSymmetryPackage

open IntrinsicSignatureCoreAxioms public

-- Secondary witness package: kept separate so profile data cannot become a
-- hidden dependency of the primary theorem path.
record IntrinsicProfileWitness
  (core : IntrinsicSignatureCoreAxioms) : Set where
  field
    shellStratification : CASS.IntrinsicShellStratification
    orientation : CAOA.IntrinsicOrientation
    profileMatches31 :
      CAOP.toProfile
        (CAOS.buildAbstractOrbitProfile
          (CAOA.IntrinsicOrientation.orientationTag orientation)
          (CAOS.buildIntrinsicOrbitStructure shellStratification))
      ≡ OSD.ProfileOf OSD.sig31

open IntrinsicProfileWitness public

profileEqFromIntrinsic :
  {core : IntrinsicSignatureCoreAxioms} →
  (w : IntrinsicProfileWitness core) →
  CAOP.toProfile
    (CAOS.buildAbstractOrbitProfile
      (CAOA.IntrinsicOrientation.orientationTag
        (IntrinsicProfileWitness.orientation w))
      (CAOS.buildIntrinsicOrbitStructure
        (IntrinsicProfileWitness.shellStratification w)))
  ≡ OSD.ProfileOf OSD.sig31
profileEqFromIntrinsic w = IntrinsicProfileWitness.profileMatches31 w

signature31-theoremFromIntrinsic :
  IntrinsicSignatureCoreAxioms →
  Signature31Theorem
signature31-theoremFromIntrinsic core =
  CFL.lorentz31-from-causal-axioms
    (IntrinsicSignatureCoreAxioms.strengthenedContraction core)
    (IntrinsicSignatureCoreAxioms.causalSymmetry core)

-- Secondary certification path: profile match remains available as an
-- eliminator/cross-check, but it is no longer the primary theorem source.
profileSignatureLawFromIntrinsic :
  {core : IntrinsicSignatureCoreAxioms} →
  IntrinsicProfileWitness core →
  SU.SignatureLaw
profileSignatureLawFromIntrinsic w =
  SEFP.signatureLawFromProfileEq _ (profileEqFromIntrinsic w)

signature31FromIntrinsic :
  IntrinsicSignatureCoreAxioms →
  CTI.Signature
signature31FromIntrinsic core =
  CFL.signature31-from-causal-axioms
    (IntrinsicSignatureCoreAxioms.strengthenedContraction core)
    (IntrinsicSignatureCoreAxioms.causalSymmetry core)
