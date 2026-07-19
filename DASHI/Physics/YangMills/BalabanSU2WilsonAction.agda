module DASHI.Physics.YangMills.BalabanSU2WilsonAction where

open import Agda.Builtin.List using (List)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanFiniteOneStepCore public using
  (FiniteWilsonActionData; wilsonPlaquetteTerm; finiteWilsonAction)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (SU2Quaternion; quaternion; q0; zeroR; oneR; _+R_; -R_)

record SU2FinitePlaquetteData (Plaquette : Set) : Set₁ where
  field
    plaquettes : List Plaquette
    plaquetteHolonomy : Plaquette → SU2Quaternion

open SU2FinitePlaquetteData public

subtractR : ℝ → ℝ → ℝ
subtractR left right = left +R (-R right)

su2WilsonActionData :
  ∀ {Plaquette} →
  SU2FinitePlaquetteData Plaquette →
  FiniteWilsonActionData Plaquette SU2Quaternion ℝ
su2WilsonActionData bundle = record
  { plaquettes = SU2FinitePlaquetteData.plaquettes bundle
  ; plaquetteHolonomy = SU2FinitePlaquetteData.plaquetteHolonomy bundle
  ; normalizedRealTrace = λ link → q0 (quaternion link)
  ; scalarZero = zeroR
  ; scalarOne = oneR
  ; scalarAdd = _+R_
  ; scalarSubtract = subtractR
  }

su2FiniteWilsonAction :
  ∀ {Plaquette} → SU2FinitePlaquetteData Plaquette → ℝ
su2FiniteWilsonAction bundle = finiteWilsonAction (su2WilsonActionData bundle)
