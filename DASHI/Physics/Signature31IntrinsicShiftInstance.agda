module DASHI.Physics.Signature31IntrinsicShiftInstance where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Unit using (⊤; tt)
open import DASHI.Geometry.ParallelogramLaw using (AdditiveSpace)
import DASHI.Geometry.ConeMetricCompatibility as CMC

open import DASHI.Geometry.ConeArrowOrientationAsymmetry as CAOA
open import DASHI.Geometry.ConeArrowOrbitStructure as CAOS
open import DASHI.Geometry.ConeArrowShellStratification as CASS
open import DASHI.Geometry.ConeArrowIsotropyOrbitProfile as CAOP
import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Geometry.CausalForcesLorentz31 as CFL
open import DASHI.Geometry.Signature31FromIntrinsicShellForcing as S31ISF
open import DASHI.Geometry.SignatureUniqueness31 as SU using (Signature31Theorem)
open import DASHI.Physics.Closure.ContractionForcesQuadraticStrong as CFQS
open import DASHI.Physics.ConeArrowIsotropyShiftOrbitEnumeration as SOE
open import DASHI.Physics.OrbitSignatureDiscriminant as OSD
open import DASHI.Physics.Signature31ShiftProfileWitness as SPW

shiftShellStratification :
  CASS.IntrinsicShellStratification
shiftShellStratification =
  record
    { shell1OrbitSizes = SOE.shell1Derived
    ; shell2OrbitSizes = SOE.shell2Derived
    }

shiftOrbitStructure :
  CAOS.IntrinsicOrbitStructure
shiftOrbitStructure =
  CAOS.buildIntrinsicOrbitStructure shiftShellStratification

shiftOrientation : CAOA.IntrinsicOrientation
shiftOrientation =
  record
    { orientationTag = 31
    ; orientationTag≡sig31 = SOE.orientationTagDerived
    }

shiftProfileMatches31 :
  CAOP.toProfile
    (CAOS.buildAbstractOrbitProfile
      (CAOA.IntrinsicOrientation.orientationTag shiftOrientation)
      shiftOrbitStructure)
  ≡ OSD.ProfileOf OSD.sig31
shiftProfileMatches31
  rewrite SOE.orientationTagDerived
        | SOE.shiftEnumeration-shell1≡computed
        | SOE.shiftEnumeration-shell2≡computed =
  SPW.computed≡sig31Profile

shiftIntrinsicCoreAxioms :
  S31ISF.IntrinsicSignatureCoreAxioms
shiftIntrinsicCoreAxioms =
  record
    { strengthenedContraction = CFQS.canonicalNontrivialInvariantStrong
    ; causalSymmetry =
        record
          { coneNontrivial = ⊤
          ; coneNontrivialWitness = tt
          ; arrowOrientation = ⊤
          ; arrowOrientationWitness = tt
          ; isotropyEvidence = ⊤
          ; isotropyWitness = tt
          ; finiteSpeed = ⊤
          ; finiteSpeedWitness = tt
          ; involution = ⊤
          ; involutionWitness = tt
          ; nondegenerateQuadratic = ⊤
          ; nondegenerateQuadraticWitness =
              CFQS.ContractionForcesQuadraticStrong.nondegenerate
                CFQS.canonicalNontrivialInvariantStrong
          ; quotientContraction = ⊤
          ; quotientContractionWitness = tt
          }
    }

shiftProfileWitness :
  S31ISF.IntrinsicProfileWitness shiftIntrinsicCoreAxioms
shiftProfileWitness =
  record
    { shellStratification = shiftShellStratification
    ; orientation = shiftOrientation
    ; profileMatches31 = shiftProfileMatches31
    }

profileEq :
  CAOP.toProfile
    (CAOS.buildAbstractOrbitProfile
      (CAOA.IntrinsicOrientation.orientationTag shiftOrientation)
      shiftOrbitStructure)
  ≡ OSD.ProfileOf OSD.sig31
profileEq = S31ISF.profileEqFromIntrinsic shiftProfileWitness

signature31-theorem : Signature31Theorem
signature31-theorem =
  S31ISF.signature31-theoremFromIntrinsic shiftIntrinsicCoreAxioms

signature31 : CTI.Signature
signature31 = S31ISF.signature31FromIntrinsic shiftIntrinsicCoreAxioms

lorentzLock :
  ∀ {A : AdditiveSpace} →
  (q : CMC.Quadratic A) →
  (cone : CMC.Cone A) →
  CMC.ConeMetricCompat A cone q →
  (iso : Set) →
  (fs : Set) →
  (arrow : Set) →
  CFL.LorentzSignatureLock
lorentzLock q cone compat iso fs arrow =
  S31ISF.lorentzLockFromIntrinsic
    shiftIntrinsicCoreAxioms
    q cone compat iso fs arrow
