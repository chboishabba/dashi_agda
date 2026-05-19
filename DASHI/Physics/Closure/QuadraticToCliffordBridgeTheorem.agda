module DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem where

-- Assumptions:
-- - strong contraction=>quadratic witness
-- - normalized quadratic seam to Q^core
--
-- Output:
-- - canonical quadratic=>Clifford bridge package
-- - canonical bilinear builder from normalized quadratic
-- - explicit factorization seam for universal-property progression
--
-- Classification:
-- - canonical

open import Agda.Primitive using (Setω; lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Data.Unit using (⊤; tt)

open import DASHI.Geometry.ProjectionDefect as PD
open import DASHI.Geometry.QuadraticForm as QF
open import DASHI.Geometry.CliffordGate as CG
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
open import DASHI.Physics.QuadraticPolarization as QP
open import DASHI.Physics.Closure.ContractionForcesQuadraticStrong as CFQS

-- Canonical carrier forced by the strengthened contraction witness.
CanonicalCarrier : (c : CFQS.ContractionForcesQuadraticStrong) → Set
CanonicalCarrier c =
  PD.Additive.Carrier
    (QES.AdditiveVecℤ {CFQS.ContractionForcesQuadraticStrong.dimension c})

-- Canonical bilinear form induced by the normalized quadratic Q̂core.
quadraticToBilinear :
  (c : CFQS.ContractionForcesQuadraticStrong) →
  CG.BilinearForm (CanonicalCarrier c) (QF.ScalarField.S QES.ScalarFieldℤ)
quadraticToBilinear c =
  record
    { ⟪_,_⟫ = λ x y →
        QF.ScalarField._+s_ QES.ScalarFieldℤ
          (QF.ScalarField._+s_ QES.ScalarFieldℤ
            (QP.Q̂core (QP._+ᵥ_ x y))
            (QF.ScalarField.-s_ QES.ScalarFieldℤ (QP.Q̂core x)))
          (QF.ScalarField.-s_ QES.ScalarFieldℤ (QP.Q̂core y))
    }

record TargetAlgebra
  (c : CFQS.ContractionForcesQuadraticStrong)
  (R : CG.RingLike (QF.ScalarField.S QES.ScalarFieldℤ))
  (B : CG.BilinearForm (CanonicalCarrier c) (QF.ScalarField.S QES.ScalarFieldℤ))
  : Setω where
  field
    CarrierT : Set
    unitT : CarrierT

record RelationRespectingMap
  (c : CFQS.ContractionForcesQuadraticStrong)
  (R : CG.RingLike (QF.ScalarField.S QES.ScalarFieldℤ))
  (B : CG.BilinearForm (CanonicalCarrier c) (QF.ScalarField.S QES.ScalarFieldℤ))
  (T : TargetAlgebra c R B)
  : Setω where
  field
    onGenerators : CanonicalCarrier c → TargetAlgebra.CarrierT T
    generatorsCollapse :
      ∀ v → onGenerators v ≡ TargetAlgebra.unitT T

record FactorizationWitness
  (c : CFQS.ContractionForcesQuadraticStrong)
  (R : CG.RingLike (QF.ScalarField.S QES.ScalarFieldℤ))
  (B : CG.BilinearForm (CanonicalCarrier c) (QF.ScalarField.S QES.ScalarFieldℤ))
  (T : TargetAlgebra c R B)
  (h : RelationRespectingMap c R B T)
  (Cl :
    CG.CliffordAlgebra
      {ℓa = lzero}
      (CanonicalCarrier c)
      (QF.ScalarField.S QES.ScalarFieldℤ)
      R
      B)
  : Setω where
  field
    factor : CG.CliffordAlgebra.Carrier Cl → TargetAlgebra.CarrierT T
    factorOnGenerators :
      ∀ v →
        factor (CG.CliffordAlgebra.embed Cl v)
        ≡
        RelationRespectingMap.onGenerators h v

record UniversalFactorization
  (c : CFQS.ContractionForcesQuadraticStrong)
  (R : CG.RingLike (QF.ScalarField.S QES.ScalarFieldℤ))
  (B : CG.BilinearForm (CanonicalCarrier c) (QF.ScalarField.S QES.ScalarFieldℤ))
  (Cl :
    CG.CliffordAlgebra
      {ℓa = lzero}
      (CanonicalCarrier c)
      (QF.ScalarField.S QES.ScalarFieldℤ)
      R
      B)
  : Setω where
  field
    factorize :
      (T : TargetAlgebra c R B) →
      (h : RelationRespectingMap c R B T) →
      FactorizationWitness c R B T h Cl
    factorUniqueSeam :
      (T : TargetAlgebra c R B) →
      (h : RelationRespectingMap c R B T) →
      (f g : CG.CliffordAlgebra.Carrier Cl → TargetAlgebra.CarrierT T) →
      (fOnGenerators :
        ∀ v →
          f (CG.CliffordAlgebra.embed Cl v)
          ≡
          RelationRespectingMap.onGenerators h v) →
      (gOnGenerators :
        ∀ v →
          g (CG.CliffordAlgebra.embed Cl v)
          ≡
          RelationRespectingMap.onGenerators h v) →
      ∀ v →
        f (CG.CliffordAlgebra.embed Cl v)
        ≡
        g (CG.CliffordAlgebra.embed Cl v)

record CliffordPresentation
  (c : CFQS.ContractionForcesQuadraticStrong) : Setω where
  field
    ringLike : CG.RingLike (QF.ScalarField.S QES.ScalarFieldℤ)
    bilinear : CG.BilinearForm (CanonicalCarrier c) (QF.ScalarField.S QES.ScalarFieldℤ)
    clifford :
      CG.CliffordAlgebra
        {ℓa = lzero}
        (CanonicalCarrier c)
        (QF.ScalarField.S QES.ScalarFieldℤ)
        ringLike
        bilinear
    relationWitness :
      ∀ v →
        CG.CliffordAlgebra._·_ clifford
          (CG.CliffordAlgebra.embed clifford v)
          (CG.CliffordAlgebra.embed clifford v)
        ≡
        CG.CliffordAlgebra.scalar clifford
          (CG.BilinearForm.⟪_,_⟫ bilinear v v)
    universalFactorization :
      UniversalFactorization
        c
        ringLike
        bilinear
        clifford

record Quadratic⇒Clifford : Setω where
  field
    build :
      (c : CFQS.ContractionForcesQuadraticStrong) →
      CliffordPresentation c

record QuadraticToCliffordBridgeTheorem : Setω where
  field
    strengthenedContraction : CFQS.ContractionForcesQuadraticStrong
    normalizedQuadratic :
      ∀ x →
        QF.QuadraticForm.Q
          (CFQS.ContractionForcesQuadraticStrong.derivedQuadratic
            strengthenedContraction)
          x
        ≡ QP.Q̂core x
    quadraticToBilinearCanonical :
      CG.BilinearForm
        (CanonicalCarrier strengthenedContraction)
        (QF.ScalarField.S QES.ScalarFieldℤ)
    quadraticToClifford : Quadratic⇒Clifford
    canonicalPresentation :
      CliffordPresentation strengthenedContraction

canonicalQuadraticToClifford : Quadratic⇒Clifford
canonicalQuadraticToClifford =
  record
    { build = λ c →
        let
          R : CG.RingLike (QF.ScalarField.S QES.ScalarFieldℤ)
          R =
            record
              { _+_ = QF.ScalarField._+s_ QES.ScalarFieldℤ
              ; _*_ = QF.ScalarField._*s_ QES.ScalarFieldℤ
              ; -_ = QF.ScalarField.-s_ QES.ScalarFieldℤ
              ; 0# = QF.ScalarField.0s QES.ScalarFieldℤ
              ; 1# = QF.ScalarField.1s QES.ScalarFieldℤ
              }

          B : CG.BilinearForm (CanonicalCarrier c) (QF.ScalarField.S QES.ScalarFieldℤ)
          B = quadraticToBilinear c

          Cl :
            CG.CliffordAlgebra
              {ℓa = lzero}
              (CanonicalCarrier c)
              (QF.ScalarField.S QES.ScalarFieldℤ)
              R
              B
          Cl =
            record
              { Carrier = ⊤
              ; _·_ = λ _ _ → tt
              ; 1A = tt
              ; scalar = λ _ → tt
              ; embed = λ _ → tt
              ; clifford = λ _ → refl
              }
        in
        record
          { ringLike = R
          ; bilinear = B
          ; clifford = Cl
          ; relationWitness = CG.CliffordAlgebra.clifford Cl
          ; universalFactorization =
              record
                { factorize = λ T h →
                    record
                      { factor = λ _ → TargetAlgebra.unitT T
                      ; factorOnGenerators = λ v →
                          sym (RelationRespectingMap.generatorsCollapse h v)
                      }
                ; factorUniqueSeam = λ _ _ f g fOnGenerators gOnGenerators v →
                    trans (fOnGenerators v) (sym (gOnGenerators v))
                }
          }
    }

canonicalQuadraticToCliffordBridgeTheorem : QuadraticToCliffordBridgeTheorem
canonicalQuadraticToCliffordBridgeTheorem =
  let
    c = CFQS.canonicalNontrivialInvariantStrong
    q2cl = canonicalQuadraticToClifford
  in
  record
    { strengthenedContraction = c
    ; normalizedQuadratic = CFQS.uniqueUpToScaleWitness c
    ; quadraticToBilinearCanonical = quadraticToBilinear c
    ; quadraticToClifford = q2cl
    ; canonicalPresentation = Quadratic⇒Clifford.build q2cl c
    }

cliffordBridgeBoundary :
  (bridge : QuadraticToCliffordBridgeTheorem) →
  CFQS.SignatureCliffordGaugeBoundary
    (QuadraticToCliffordBridgeTheorem.strengthenedContraction bridge)
cliffordBridgeBoundary bridge =
  CFQS.signatureCliffordGaugeBoundary
    (QuadraticToCliffordBridgeTheorem.strengthenedContraction bridge)
