module DASHI.Physics.Signature31IntrinsicSyntheticInstance where

open import Data.Unit using (⊤; tt)
open import Agda.Builtin.String using (String)

open import DASHI.Geometry.Signature31FromIntrinsicShellForcing as S31ISF
open import DASHI.Physics.Closure.ContractionForcesQuadraticStrong as CFQS
open import DASHI.Physics.Closure.Validation.SyntheticOneMinusDynamicsWitness as SODW

-- Alternate intrinsic-core inhabitant path:
-- uses the same theorem-critical contraction witness, but is packaged on the
-- synthetic one-minus dynamics track instead of the shift-orbit profile path.
syntheticIntrinsicCoreAxioms :
  S31ISF.IntrinsicSignatureCoreAxioms
syntheticIntrinsicCoreAxioms =
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

syntheticLabel : String
syntheticLabel =
  SODW.SyntheticOneMinusDynamicsWitness.label
    SODW.syntheticDynamicsWitness
