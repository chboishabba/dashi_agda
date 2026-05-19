module DASHI.Physics.Signature31IntrinsicRootSystemB4Instance where

open import Data.Unit using (⊤; tt)
open import Agda.Builtin.String using (String)

open import DASHI.Geometry.Signature31FromIntrinsicShellForcing as S31ISF
open import DASHI.Physics.Closure.ContractionForcesQuadraticStrong as CFQS

b4IntrinsicCoreAxioms :
  S31ISF.IntrinsicSignatureCoreAxioms
b4IntrinsicCoreAxioms =
  record
    { strengthenedContraction = CFQS.canonicalIdentityInvariantStrong 4
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
                (CFQS.canonicalIdentityInvariantStrong 4)
          ; quotientContraction = ⊤
          ; quotientContractionWitness = tt
          }
    }

b4Label : String
b4Label = "root-system-b4-intrinsic-core"
