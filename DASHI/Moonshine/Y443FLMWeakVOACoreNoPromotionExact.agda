module DASHI.Moonshine.Y443FLMWeakVOACoreNoPromotionExact where

------------------------------------------------------------------------
-- REAL COUNTERMODEL: the existing VertexOperatorAlgebraCore is a
-- DATA INTERFACE, not a proof of VOA axioms. Its important axiom fields
-- are *Set values*, not inhabitants of semantic equations.
--
-- Two concrete inhabitants of the core record have carrier Bool and Unit.
-- Their operations are freely chosen and the "law" fields are filled with
-- the proposition Unit. There cannot exist a state-space equivalence
-- Bool <-> Unit. Therefore it is invalid to derive a generic canonical
-- FLM equivalence merely from an instance of the original VOA record.
--
-- This no-go is intentionally narrower than claims about the genuine
-- FLM Moonshine VOA: it tests the formal certificate authority only.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)
open import Data.Empty using (⊥)
import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA

boolGM : VOA.GradedModule
boolGM = record
  { VOA.GradedModule.Scalar = ⊤
  ; VOA.GradedModule.Carrier = Bool
  ; VOA.GradedModule.gradePiece = λ _ → Bool
  ; VOA.GradedModule.includeGrade = λ _ b → b
  ; VOA.GradedModule.zero = false
  ; VOA.GradedModule._+_ = λ _ _ → false
  ; VOA.GradedModule._·_ = λ _ b → b
  }

boolVertex : VOA.VertexOperatorData boolGM
boolVertex = record
  { VOA.VertexOperatorData.vacuum = false
  ; VOA.VertexOperatorData.conformalVector = false
  ; VOA.VertexOperatorData.mode = λ _ _ _ → false
  ; VOA.VertexOperatorData.translation = λ _ → false
  }

boolLower : VOA.LowerTruncation boolGM boolVertex
boolLower = record
  { VOA.LowerTruncation.truncationBound = λ _ _ → zero
  ; VOA.LowerTruncation.modeVanishesAboveBound = λ _ _ → ⊤
  }

boolVacuum : VOA.VacuumAxioms boolGM boolVertex
boolVacuum = record
  { VOA.VacuumAxioms.vacuumFieldIdentity = ⊤
  ; VOA.VacuumAxioms.creationProperty = ⊤
  ; VOA.VacuumAxioms.translationKillsVacuum = ⊤
  }

boolTranslation : VOA.TranslationAxiom boolGM boolVertex
boolTranslation = record
  { VOA.TranslationAxiom.translationCovariance = ⊤
  }

boolLocality : VOA.LocalityAxiom boolGM boolVertex
boolLocality = record
  { VOA.LocalityAxiom.localityExponent = λ _ _ → zero
  ; VOA.LocalityAxiom.mutuallyLocal = λ _ _ → ⊤
  }

boolJacobi : VOA.JacobiAxiom boolGM boolVertex
boolJacobi = record
  { VOA.JacobiAxiom.borcherdsJacobiIdentity = ⊤
  }

boolConformal : VOA.ConformalAxioms boolGM boolVertex
boolConformal = record
  { VOA.ConformalAxioms.virasoroModes = λ _ _ → false
  ; VOA.ConformalAxioms.centralCharge = tt
  ; VOA.ConformalAxioms.virasoroCommutator = ⊤
  ; VOA.ConformalAxioms.gradingFromL0 = ⊤
  ; VOA.ConformalAxioms.translationIsLMinusOne = ⊤
  }

weakBoolVOA : VOA.VertexOperatorAlgebra
weakBoolVOA = record
  { VOA.VertexOperatorAlgebra.gradedModule = boolGM
  ; VOA.VertexOperatorAlgebra.vertexData = boolVertex
  ; VOA.VertexOperatorAlgebra.lowerTruncation = boolLower
  ; VOA.VertexOperatorAlgebra.vacuumAxioms = boolVacuum
  ; VOA.VertexOperatorAlgebra.translationAxiom = boolTranslation
  ; VOA.VertexOperatorAlgebra.localityAxiom = boolLocality
  ; VOA.VertexOperatorAlgebra.jacobiAxiom = boolJacobi
  ; VOA.VertexOperatorAlgebra.conformalAxioms = boolConformal
  }

unitGM : VOA.GradedModule
unitGM = record
  { VOA.GradedModule.Scalar = ⊤
  ; VOA.GradedModule.Carrier = ⊤
  ; VOA.GradedModule.gradePiece = λ _ → ⊤
  ; VOA.GradedModule.includeGrade = λ _ _ → tt
  ; VOA.GradedModule.zero = tt
  ; VOA.GradedModule._+_ = λ _ _ → tt
  ; VOA.GradedModule._·_ = λ _ _ → tt
  }

unitVertex : VOA.VertexOperatorData unitGM
unitVertex = record
  { VOA.VertexOperatorData.vacuum = tt
  ; VOA.VertexOperatorData.conformalVector = tt
  ; VOA.VertexOperatorData.mode = λ _ _ _ → tt
  ; VOA.VertexOperatorData.translation = λ _ → tt
  }

unitLower : VOA.LowerTruncation unitGM unitVertex
unitLower = record
  { VOA.LowerTruncation.truncationBound = λ _ _ → zero
  ; VOA.LowerTruncation.modeVanishesAboveBound = λ _ _ → ⊤
  }

unitVacuum : VOA.VacuumAxioms unitGM unitVertex
unitVacuum = record
  { VOA.VacuumAxioms.vacuumFieldIdentity = ⊤
  ; VOA.VacuumAxioms.creationProperty = ⊤
  ; VOA.VacuumAxioms.translationKillsVacuum = ⊤
  }

unitTranslation : VOA.TranslationAxiom unitGM unitVertex
unitTranslation = record
  { VOA.TranslationAxiom.translationCovariance = ⊤
  }

unitLocality : VOA.LocalityAxiom unitGM unitVertex
unitLocality = record
  { VOA.LocalityAxiom.localityExponent = λ _ _ → zero
  ; VOA.LocalityAxiom.mutuallyLocal = λ _ _ → ⊤
  }

unitJacobi : VOA.JacobiAxiom unitGM unitVertex
unitJacobi = record
  { VOA.JacobiAxiom.borcherdsJacobiIdentity = ⊤
  }

unitConformal : VOA.ConformalAxioms unitGM unitVertex
unitConformal = record
  { VOA.ConformalAxioms.virasoroModes = λ _ _ → tt
  ; VOA.ConformalAxioms.centralCharge = tt
  ; VOA.ConformalAxioms.virasoroCommutator = ⊤
  ; VOA.ConformalAxioms.gradingFromL0 = ⊤
  ; VOA.ConformalAxioms.translationIsLMinusOne = ⊤
  }

weakUnitVOA : VOA.VertexOperatorAlgebra
weakUnitVOA = record
  { VOA.VertexOperatorAlgebra.gradedModule = unitGM
  ; VOA.VertexOperatorAlgebra.vertexData = unitVertex
  ; VOA.VertexOperatorAlgebra.lowerTruncation = unitLower
  ; VOA.VertexOperatorAlgebra.vacuumAxioms = unitVacuum
  ; VOA.VertexOperatorAlgebra.translationAxiom = unitTranslation
  ; VOA.VertexOperatorAlgebra.localityAxiom = unitLocality
  ; VOA.VertexOperatorAlgebra.jacobiAxiom = unitJacobi
  ; VOA.VertexOperatorAlgebra.conformalAxioms = unitConformal
  }

unitUnique : (x y : ⊤) → x ≡ y
unitUnique tt tt = refl

sym : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {X : Set} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
trans refl y = y

cong : ∀ {X Y : Set} (f : X → Y) {x y : X} → x ≡ y → f x ≡ f y
cong f refl = refl

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

noTwoSidedBoolUnitStateIso :
  (to : Bool → ⊤) (from : ⊤ → Bool) →
  ((x : Bool) → from (to x) ≡ x) → ⊥
noTwoSidedBoolUnitStateIso to from leftInverse =
  falseNotTrue
    (trans
      (sym (leftInverse false))
      (trans
        (cong from (unitUnique (to false) (to true)))
        (leftInverse true)))

-- Thus: any universally asserted
--   (V W : VOA.VertexOperatorAlgebra) -> ExactFLMVOAIsomorphism V W
-- is contradicted already by the carriers of weakBoolVOA/weakUnitVOA.
-- Real VOA laws and actual uniqueness conditions cannot be omitted.
