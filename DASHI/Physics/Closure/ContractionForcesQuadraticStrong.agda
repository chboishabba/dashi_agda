module DASHI.Physics.Closure.ContractionForcesQuadraticStrong where

-- Assumptions:
-- - projection-defect/parallelogram package on the shift carrier
-- - chosen dynamics map with quadratic invariance witness
-- - uniqueness seam to normalized quadratic core
--
-- Output:
-- - strong contraction=>quadratic package with explicit invariance and
--   uniqueness witnesses.
--
-- Classification:
-- - strong

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (z≤n)
open import Data.Sign.Base as Sign using (Sign)
open import Data.Sign.Properties as SignP
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; cong₂; subst)
open import Data.Bool using (true; false)
open import Data.Vec using (_∷_; [])
open import Data.Product using (Σ; proj₁; proj₂; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
import Data.Integer as Int
open import Data.Integer.Properties as IntP
import Data.Sign.Base as Sign
import Data.Sign.Properties as SignP

open import DASHI.Geometry.ProjectionDefect as PD
open import DASHI.Geometry.QuadraticForm as QF
open import DASHI.Geometry.Signature.HyperbolicFormZ as HFZ
open import DASHI.Geometry.ProjectionDefectToParallelogram as PDP
open import DASHI.Geometry.ProjectionDefectSplitForcesParallelogram as PDSP
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
open import DASHI.Physics.QuadraticPolarization as QP
open import DASHI.Physics.Signature31InstanceShiftZ as S31
open import DASHI.Physics.SignedPerm4 as SP

record NondegeneracySeam
  (m : Nat)
  (q : QF.QuadraticForm (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ) : Setω where
  field
    normalizeToQ̂core :
      ∀ x →
        QF.QuadraticForm.Q q x
        ≡
        QP.Q̂core x
    zeroNormalized :
      QF.QuadraticForm.Q q (QP.zeroVecℤ {m})
      ≡
      QF.ScalarField.0s QES.ScalarFieldℤ

record ExplicitIsotropyStructure
  (m : Nat)
  (Δ : PD.Additive.Carrier (QES.AdditiveVecℤ {m}) →
       PD.Additive.Carrier (QES.AdditiveVecℤ {m}))
  (q : QF.QuadraticForm (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ) : Setω where
  field
    imageMatchesQ̂core :
      ∀ x →
        QF.QuadraticForm.Q q (Δ x)
        ≡
        QP.Q̂core x
    shellRespectingAlongΔ :
      ∀ x y →
        QP.Q̂core x ≡ QP.Q̂core y →
        QF.QuadraticForm.Q q (Δ x)
        ≡
        QF.QuadraticForm.Q q (Δ y)

mkExplicitIsotropyStructure :
  ∀ {m Δ q} →
  (∀ x →
    QF.QuadraticForm.Q q (Δ x)
    ≡
    QP.Q̂core x) →
  ExplicitIsotropyStructure m Δ q
mkExplicitIsotropyStructure imageMatches =
  record
    { imageMatchesQ̂core = imageMatches
    ; shellRespectingAlongΔ =
        λ x y sameShell →
          trans
            (imageMatches x)
            (trans sameShell (sym (imageMatches y)))
    }

record ResidualIsotropyGap (m : Nat) : Setω where
  field
    isotropyAction : Set
    applyIsotropyAction :
      isotropyAction →
      PD.Additive.Carrier (QES.AdditiveVecℤ {m}) →
      PD.Additive.Carrier (QES.AdditiveVecℤ {m})
    actionPreservesQ̂core :
      isotropyAction → Set
    actionPreservesQ̂coreWitness :
      ∀ {ρ} →
        actionPreservesQ̂core ρ →
        ∀ x →
          QP.Q̂core (applyIsotropyAction ρ x)
          ≡
          QP.Q̂core x
    shellTransportBoundary :
      ∀ (x y : PD.Additive.Carrier (QES.AdditiveVecℤ {m})) →
        QP.Q̂core x ≡ QP.Q̂core y →
        Set
    liftShellTransportToAction :
      ∀ (x y : PD.Additive.Carrier (QES.AdditiveVecℤ {m}))
        (sameShell : QP.Q̂core x ≡ QP.Q̂core y) →
        shellTransportBoundary x y sameShell →
        Σ
          isotropyAction
          (λ ρ →
            Σ
              (applyIsotropyAction ρ x ≡ y)
              (λ _ →
                actionPreservesQ̂core ρ))

defaultResidualIsotropyGap :
  ∀ {m} →
  ResidualIsotropyGap m
defaultResidualIsotropyGap {m} =
  record
    { isotropyAction =
        PD.Additive.Carrier (QES.AdditiveVecℤ {m}) →
        PD.Additive.Carrier (QES.AdditiveVecℤ {m})
    ; applyIsotropyAction = λ ρ → ρ
    ; actionPreservesQ̂core =
        λ ρ →
          ∀ x →
            QP.Q̂core (ρ x) ≡ QP.Q̂core x
    ; actionPreservesQ̂coreWitness = λ preserves → preserves
    ; shellTransportBoundary =
        λ x y _ →
          Σ
            (PD.Additive.Carrier (QES.AdditiveVecℤ {m}) →
             PD.Additive.Carrier (QES.AdditiveVecℤ {m}))
            (λ ρ →
              Σ
                (ρ x ≡ y)
                (λ _ →
                  ∀ z →
                    QP.Q̂core (ρ z) ≡ QP.Q̂core z))
    ; liftShellTransportToAction = λ _ _ _ boundaryWitness → boundaryWitness
    }

record IsotropyCompatibilitySeam
  (m : Nat)
  (Δ : PD.Additive.Carrier (QES.AdditiveVecℤ {m}) →
       PD.Additive.Carrier (QES.AdditiveVecℤ {m}))
  (q : QF.QuadraticForm (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ) : Setω where
  field
    explicitIsotropyStructure :
      ExplicitIsotropyStructure m Δ q
    residualIsotropyGap :
      ResidualIsotropyGap m

record InhabitedIsotropyTransport
  {m : Nat}
  (gap : ResidualIsotropyGap m)
  (x y : PD.Additive.Carrier (QES.AdditiveVecℤ {m})) : Setω where
  field
    transporter :
      ResidualIsotropyGap.isotropyAction gap
    transportsSourceToTarget :
      ResidualIsotropyGap.applyIsotropyAction
        gap
        transporter
        x
      ≡
      y
    preservesQ̂core :
      ResidualIsotropyGap.actionPreservesQ̂core
        gap
        transporter

  transportedPreservesQ̂core :
    ∀ z →
      QP.Q̂core
        (ResidualIsotropyGap.applyIsotropyAction
          gap
          transporter
          z)
      ≡
      QP.Q̂core z
  transportedPreservesQ̂core =
    ResidualIsotropyGap.actionPreservesQ̂coreWitness
      gap
      preservesQ̂core

compatibleWithQ̂core :
  ∀ {m Δ q} →
  IsotropyCompatibilitySeam m Δ q →
  ∀ x →
    QF.QuadraticForm.Q q (Δ x)
    ≡
    QP.Q̂core x
compatibleWithQ̂core seam =
  ExplicitIsotropyStructure.imageMatchesQ̂core
    (IsotropyCompatibilitySeam.explicitIsotropyStructure seam)

shellRespectingAlongΔ :
  ∀ {m Δ q} →
  IsotropyCompatibilitySeam m Δ q →
  ∀ x y →
    QP.Q̂core x ≡ QP.Q̂core y →
    QF.QuadraticForm.Q q (Δ x)
    ≡
    QF.QuadraticForm.Q q (Δ y)
shellRespectingAlongΔ seam =
  ExplicitIsotropyStructure.shellRespectingAlongΔ
    (IsotropyCompatibilitySeam.explicitIsotropyStructure seam)

shellBoundaryLiftsToActionTransport :
  ∀ {m Δ q} →
  (seam : IsotropyCompatibilitySeam m Δ q) →
  ∀ x y →
    (sameShell : QP.Q̂core x ≡ QP.Q̂core y) →
    ResidualIsotropyGap.shellTransportBoundary
      (IsotropyCompatibilitySeam.residualIsotropyGap seam)
      x y sameShell →
    Σ
      (ResidualIsotropyGap.isotropyAction
        (IsotropyCompatibilitySeam.residualIsotropyGap seam))
      (λ ρ →
        Σ
          (ResidualIsotropyGap.applyIsotropyAction
            (IsotropyCompatibilitySeam.residualIsotropyGap seam)
            ρ x
            ≡ y)
          (λ _ →
            ResidualIsotropyGap.actionPreservesQ̂core
              (IsotropyCompatibilitySeam.residualIsotropyGap seam)
              ρ))
shellBoundaryLiftsToActionTransport seam x y sameShell boundaryWitness =
  ResidualIsotropyGap.liftShellTransportToAction
    (IsotropyCompatibilitySeam.residualIsotropyGap seam)
    x y sameShell boundaryWitness

shellBoundaryLiftsToActionTransportWitness :
  ∀ {m Δ q} →
  (seam : IsotropyCompatibilitySeam m Δ q) →
  ∀ x y →
    (sameShell : QP.Q̂core x ≡ QP.Q̂core y) →
    ResidualIsotropyGap.shellTransportBoundary
      (IsotropyCompatibilitySeam.residualIsotropyGap seam)
      x y sameShell →
    Σ
      (ResidualIsotropyGap.isotropyAction
        (IsotropyCompatibilitySeam.residualIsotropyGap seam))
      (λ ρ →
        Σ
          (ResidualIsotropyGap.applyIsotropyAction
            (IsotropyCompatibilitySeam.residualIsotropyGap seam)
            ρ x
            ≡ y)
          (λ _ →
            ∀ z →
              QP.Q̂core
                (ResidualIsotropyGap.applyIsotropyAction
                  (IsotropyCompatibilitySeam.residualIsotropyGap seam)
                  ρ z)
              ≡
              QP.Q̂core z))
shellBoundaryLiftsToActionTransportWitness seam x y sameShell boundaryWitness =
  let
    gap = IsotropyCompatibilitySeam.residualIsotropyGap seam
    lifted = shellBoundaryLiftsToActionTransport seam x y sameShell boundaryWitness
    ρ = proj₁ lifted
    reachesY = proj₁ (proj₂ lifted)
    preserves = proj₂ (proj₂ lifted)
  in
  ρ
  ,
  reachesY
  ,
  ResidualIsotropyGap.actionPreservesQ̂coreWitness gap preserves

shellBoundaryInhabitsIsotropyTransport :
  ∀ {m Δ q} →
  (seam : IsotropyCompatibilitySeam m Δ q) →
  ∀ x y →
    (sameShell : QP.Q̂core x ≡ QP.Q̂core y) →
    ResidualIsotropyGap.shellTransportBoundary
      (IsotropyCompatibilitySeam.residualIsotropyGap seam)
      x y sameShell →
    InhabitedIsotropyTransport
      (IsotropyCompatibilitySeam.residualIsotropyGap seam)
      x y
shellBoundaryInhabitsIsotropyTransport seam x y sameShell boundaryWitness =
  let
    lifted = shellBoundaryLiftsToActionTransport seam x y sameShell boundaryWitness
  in
  record
    { transporter = proj₁ lifted
    ; transportsSourceToTarget = proj₁ (proj₂ lifted)
    ; preservesQ̂core = proj₂ (proj₂ lifted)
    }

inhabitedIsotropyTransportPreservesDerivedQuadratic :
  ∀ {m Δ q} →
  (seam : IsotropyCompatibilitySeam m Δ q) →
  ∀ {x y} →
    (it :
      InhabitedIsotropyTransport
        (IsotropyCompatibilitySeam.residualIsotropyGap seam)
        x y) →
    (z : PD.Additive.Carrier (QES.AdditiveVecℤ {m})) →
    QF.QuadraticForm.Q q
      (Δ
        (ResidualIsotropyGap.applyIsotropyAction
          (IsotropyCompatibilitySeam.residualIsotropyGap seam)
          (InhabitedIsotropyTransport.transporter it)
          z))
    ≡
    QF.QuadraticForm.Q q (Δ z)
inhabitedIsotropyTransportPreservesDerivedQuadratic seam it z =
  trans
    (compatibleWithQ̂core seam
      (ResidualIsotropyGap.applyIsotropyAction
        (IsotropyCompatibilitySeam.residualIsotropyGap seam)
        (InhabitedIsotropyTransport.transporter it)
        z))
    (trans
      (InhabitedIsotropyTransport.transportedPreservesQ̂core it z)
      (sym (compatibleWithQ̂core seam z)))

inhabitedIsotropyTransportPreservesTargetQuadratic :
  ∀ {m Δ q} →
  (seam : IsotropyCompatibilitySeam m Δ q) →
  ∀ {x y} →
    (transport :
      InhabitedIsotropyTransport
        (IsotropyCompatibilitySeam.residualIsotropyGap seam)
        x y) →
    QF.QuadraticForm.Q q (Δ y)
    ≡
    QF.QuadraticForm.Q q (Δ x)
inhabitedIsotropyTransportPreservesTargetQuadratic seam {x} {y} transport =
  trans
    (compatibleWithQ̂core seam y)
    (trans
      (sym
        (cong QP.Q̂core
          (InhabitedIsotropyTransport.transportsSourceToTarget
            {gap = IsotropyCompatibilitySeam.residualIsotropyGap seam}
            transport)))
      (trans
        (InhabitedIsotropyTransport.transportedPreservesQ̂core
          {gap = IsotropyCompatibilitySeam.residualIsotropyGap seam}
          transport
          x)
        (sym (compatibleWithQ̂core seam x))))

mkNondegeneracySeam :
  ∀ {m q} →
  (∀ x →
    QF.QuadraticForm.Q q x
    ≡
    QP.Q̂core x) →
  NondegeneracySeam m q
mkNondegeneracySeam {m} normalizeToQ̂core =
  record
    { normalizeToQ̂core = normalizeToQ̂core
    ; zeroNormalized =
        trans
          (normalizeToQ̂core (QP.zeroVecℤ {m}))
          (QES.Q̂core-zeroVec {m})
    }

mkIsotropyCompatibilitySeam :
  ∀ {m Δ q} →
  (∀ x →
    QF.QuadraticForm.Q q (Δ x)
    ≡
    QP.Q̂core x) →
  ResidualIsotropyGap m →
  IsotropyCompatibilitySeam m Δ q
mkIsotropyCompatibilitySeam w gap =
  record
    { explicitIsotropyStructure = mkExplicitIsotropyStructure w
    ; residualIsotropyGap = gap
    }

record UniqueUpToScaleSeam
  (m : Nat)
  (q : QF.QuadraticForm (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ) : Setω where
  field
    scaleFactor : QF.ScalarField.S QES.ScalarFieldℤ
    normalizeToScaledQ̂core :
      ∀ x →
        QF.QuadraticForm.Q q x
        ≡
        QF.ScalarField._*s_ QES.ScalarFieldℤ
          scaleFactor
          (QP.Q̂core x)
    normalizeToQ̂core :
      ∀ x →
        QF.QuadraticForm.Q q x ≡ QP.Q̂core x

mkUniqueUpToScaleSeamAtScale :
  ∀ {m q} →
  (scale :
    QF.ScalarField.S QES.ScalarFieldℤ) →
  (∀ x →
    QF.QuadraticForm.Q q x
    ≡
    QF.ScalarField._*s_ QES.ScalarFieldℤ
      scale
      (QP.Q̂core x)) →
  (∀ x → QF.QuadraticForm.Q q x ≡ QP.Q̂core x) →
  UniqueUpToScaleSeam m q
mkUniqueUpToScaleSeamAtScale scale scaled normalize =
  record
    { scaleFactor = scale
    ; normalizeToScaledQ̂core = scaled
    ; normalizeToQ̂core = normalize
    }

record CoreScaleSeam
  (m : Nat)
  (scale : QF.ScalarField.S QES.ScalarFieldℤ) : Setω where
  field
    scaleQ̂core :
      ∀ (x : PD.Additive.Carrier (QES.AdditiveVecℤ {m})) →
        QP.Q̂core x
        ≡
        QF.ScalarField._*s_ QES.ScalarFieldℤ
          scale
          (QP.Q̂core x)

record CoreScaleCarrierSeam
  (m : Nat)
  (scale : QF.ScalarField.S QES.ScalarFieldℤ) : Setω where
  field
    carrierPredicate :
      PD.Additive.Carrier (QES.AdditiveVecℤ {m}) → Set
    scaleQ̂coreOnCarrier :
      ∀ {x} →
        carrierPredicate x →
        QP.Q̂core x
        ≡
        QF.ScalarField._*s_ QES.ScalarFieldℤ
          scale
          (QP.Q̂core x)

mkCoreScaleSeam :
  ∀ {m} →
  (scale : QF.ScalarField.S QES.ScalarFieldℤ) →
  (∀ (x : PD.Additive.Carrier (QES.AdditiveVecℤ {m})) →
    QP.Q̂core x
    ≡
    QF.ScalarField._*s_ QES.ScalarFieldℤ
      scale
      (QP.Q̂core x)) →
  CoreScaleSeam m scale
mkCoreScaleSeam _ witness =
  record
    { scaleQ̂core = witness
    }

mkCoreScaleSeamFromScalarFixedPoint :
  ∀ {m} →
  (scale : QF.ScalarField.S QES.ScalarFieldℤ) →
  (∀ z →
    z
    ≡
    QF.ScalarField._*s_ QES.ScalarFieldℤ
      scale
      z) →
  CoreScaleSeam m scale
mkCoreScaleSeamFromScalarFixedPoint scale scalarFixedPoint =
  mkCoreScaleSeam
    scale
    (λ x → scalarFixedPoint (QP.Q̂core x))

mkCoreScaleCarrierSeam :
  ∀ {m} →
  (scale : QF.ScalarField.S QES.ScalarFieldℤ) →
  (carrierPredicate :
    PD.Additive.Carrier (QES.AdditiveVecℤ {m}) → Set) →
  (∀ {x} →
    carrierPredicate x →
    QP.Q̂core x
    ≡
    QF.ScalarField._*s_ QES.ScalarFieldℤ
      scale
      (QP.Q̂core x)) →
  CoreScaleCarrierSeam m scale
mkCoreScaleCarrierSeam _ carrierPredicate witness =
  record
    { carrierPredicate = carrierPredicate
    ; scaleQ̂coreOnCarrier = witness
    }

oneℤ : QF.ScalarField.S QES.ScalarFieldℤ
oneℤ = QF.ScalarField.1s QES.ScalarFieldℤ

unitCoreVector :
  ∀ {m} →
  PD.Additive.Carrier (QES.AdditiveVecℤ {suc m})
unitCoreVector {m} = oneℤ ∷ QP.zeroVecℤ {m}

unitCoreVectorQ̂core :
  ∀ {m} →
  QP.Q̂core (unitCoreVector {m})
  ≡
  oneℤ
unitCoreVectorQ̂core {m} =
  trans
    (cong
      (λ n →
        Int._+_
          (Int._*_ oneℤ oneℤ)
          n)
      (QES.Q̂core-zeroVec {m}))
    (trans
      (IntP.+-identityʳ (Int._*_ oneℤ oneℤ))
      (IntP.*-identityʳ oneℤ))

positiveDimensionCoreScaleSeamForcesUnit :
  ∀ {m} {scale : QF.ScalarField.S QES.ScalarFieldℤ} →
  CoreScaleSeam (suc m) scale →
  scale ≡ oneℤ
positiveDimensionCoreScaleSeamForcesUnit {m} {scale} seam =
  let
    scaleOnUnit :
      oneℤ
      ≡
      QF.ScalarField._*s_ QES.ScalarFieldℤ
        scale
        oneℤ
    scaleOnUnit =
      trans
        (sym (unitCoreVectorQ̂core {m}))
        (trans
          (CoreScaleSeam.scaleQ̂core seam (unitCoreVector {m}))
          (cong
            (QF.ScalarField._*s_ QES.ScalarFieldℤ scale)
            (unitCoreVectorQ̂core {m})))
  in
  trans
    (sym (IntP.*-identityʳ scale))
    (sym scaleOnUnit)

zeroShellCoreScaleCarrierSeam :
  ∀ {m} →
  (scale : QF.ScalarField.S QES.ScalarFieldℤ) →
  CoreScaleCarrierSeam m scale
zeroShellCoreScaleCarrierSeam scale =
  mkCoreScaleCarrierSeam
    scale
    (λ x →
      QP.Q̂core x
      ≡
      QF.ScalarField.0s QES.ScalarFieldℤ)
    (λ {x} q̂x=0 →
      trans
        q̂x=0
        (trans
          (sym (IntP.*-zeroʳ scale))
          (cong
            (λ z → Int._*_ scale z)
            (sym q̂x=0))))

positiveDimensionZeroShellCoreScaleCarrierSeam :
  ∀ {m} →
  (scale : QF.ScalarField.S QES.ScalarFieldℤ) →
  CoreScaleCarrierSeam (suc m) scale
positiveDimensionZeroShellCoreScaleCarrierSeam =
  zeroShellCoreScaleCarrierSeam

positiveDimensionZeroShellCarrierInhabited :
  ∀ {m} (scale : QF.ScalarField.S QES.ScalarFieldℤ) →
  CoreScaleCarrierSeam.carrierPredicate
    (positiveDimensionZeroShellCoreScaleCarrierSeam {m} scale)
    (QP.zeroVecℤ {suc m})
positiveDimensionZeroShellCarrierInhabited {m} _ =
  QES.Q̂core-zeroVec {suc m}

mkUniqueUpToScaleSeam :
  ∀ {m q} →
  (∀ x → QF.QuadraticForm.Q q x ≡ QP.Q̂core x) →
  UniqueUpToScaleSeam m q
mkUniqueUpToScaleSeam f =
  mkUniqueUpToScaleSeamAtScale
    (QF.ScalarField.1s QES.ScalarFieldℤ)
    (λ x →
      trans
        (f x)
        (sym (IntP.*-identityˡ (QP.Q̂core x))))
    f

Q̂core≡sumSq :
  ∀ {m} (x : PD.Additive.Carrier (QES.AdditiveVecℤ {m})) →
    QP.Q̂core x ≡ HFZ.sumSq x
Q̂core≡sumSq [] = refl
Q̂core≡sumSq (x ∷ xs) =
  cong (λ n → Int._+_ (Int._*_ x x) n) (Q̂core≡sumSq xs)

SquareZeroResidualPremise : Set
SquareZeroResidualPremise =
  ∀ z →
    Int._*_ z z
    ≡
    QF.ScalarField.0s QES.ScalarFieldℤ
    →
    z ≡ QF.ScalarField.0s QES.ScalarFieldℤ

SumSqZeroDecompositionPremise : Set
SumSqZeroDecompositionPremise =
  ∀ {m} →
  (x : Int.ℤ) →
  (xs : PD.Additive.Carrier (QES.AdditiveVecℤ {m})) →
  HFZ.sumSq (x ∷ xs)
  ≡
  QF.ScalarField.0s QES.ScalarFieldℤ
  →
  Σ
    (Int._*_ x x
      ≡
      QF.ScalarField.0s QES.ScalarFieldℤ)
    (λ _ →
      HFZ.sumSq xs
      ≡
      QF.ScalarField.0s QES.ScalarFieldℤ)

squareNonnegative :
  ∀ z →
    Int._≤_ Int.0ℤ (Int._*_ z z)
squareNonnegative (Int.+ zero) = Int.+≤+ z≤n
squareNonnegative (Int.+[1+ n ])
  rewrite sym (IntP.◃-distrib-* Sign.+ Sign.+ (suc n) (suc n))
        | SignP.s*s≡+ Sign.+
        | IntP.+◃n≡+n ((suc n) Data.Nat.* (suc n))
  = Int.+≤+ z≤n
squareNonnegative (Int.-[1+ n ])
  rewrite sym (IntP.◃-distrib-* Sign.- Sign.- (suc n) (suc n))
        | SignP.s*s≡+ Sign.-
        | IntP.+◃n≡+n ((suc n) Data.Nat.* (suc n))
  = Int.+≤+ z≤n

sumSqNonnegative :
  ∀ {m} →
  (xs : PD.Additive.Carrier (QES.AdditiveVecℤ {m})) →
  Int._≤_ Int.0ℤ (HFZ.sumSq xs)
sumSqNonnegative [] = Int.+≤+ z≤n
sumSqNonnegative (x ∷ xs) =
  IntP.i≤j⇒i≤k+j
    (Int._*_ x x)
    {{Int.nonNegative (squareNonnegative x)}}
    (sumSqNonnegative xs)

zeroSumSplitFromNonnegative :
  ∀ a b →
  Int._≤_ Int.0ℤ a →
  Int._≤_ Int.0ℤ b →
  Int._+_ a b ≡ Int.0ℤ →
  Σ
    (a ≡ Int.0ℤ)
    (λ _ → b ≡ Int.0ℤ)
zeroSumSplitFromNonnegative a b a≥0 b≥0 a+b=0 =
  a=0 , b=0
  where
    a≤a+b : a Int.≤ a Int.+ b
    a≤a+b =
      IntP.i≤i+j a b
        {{Int.nonNegative b≥0}}

    a≤0 : a Int.≤ Int.0ℤ
    a≤0 = subst (a Int.≤_) a+b=0 a≤a+b

    a=0 : a ≡ Int.0ℤ
    a=0 = IntP.≤-antisym a≤0 a≥0

    b≤b+a : b Int.≤ b Int.+ a
    b≤b+a =
      IntP.i≤i+j b a
        {{Int.nonNegative a≥0}}

    b≤0 : b Int.≤ Int.0ℤ
    b≤0 =
      subst
        (b Int.≤_)
        (trans (IntP.+-comm b a) a+b=0)
        b≤b+a

    b=0 : b ≡ Int.0ℤ
    b=0 = IntP.≤-antisym b≤0 b≥0

squareZeroResidualTheorem : SquareZeroResidualPremise
squareZeroResidualTheorem z z²=0 with IntP.i*j≡0⇒i≡0∨j≡0 z z²=0
... | inj₁ z=0 = z=0
... | inj₂ z=0 = z=0

sumSqZeroDecompositionTheorem : SumSqZeroDecompositionPremise
sumSqZeroDecompositionTheorem x xs sumSq=0 =
  zeroSumSplitFromNonnegative
    (Int._*_ x x)
    (HFZ.sumSq xs)
    (squareNonnegative x)
    (sumSqNonnegative xs)
    sumSq=0

CoreAnisotropyResidualPremise :
  Nat → Set
CoreAnisotropyResidualPremise m =
  ∀ x →
    HFZ.sumSq x
    ≡
    QF.ScalarField.0s QES.ScalarFieldℤ
    →
    x ≡ QP.zeroVecℤ {m}

sumSq-zero-only-at-origin-from-local-kernel :
  SquareZeroResidualPremise →
  SumSqZeroDecompositionPremise →
  ∀ {m} →
  CoreAnisotropyResidualPremise m
sumSq-zero-only-at-origin-from-local-kernel
  square-zero-only-at-origin
  sumSq-zero-splits
  [] _ = refl
sumSq-zero-only-at-origin-from-local-kernel
  square-zero-only-at-origin
  sumSq-zero-splits
  (x ∷ xs) sumSq=0
  with sumSq-zero-splits x xs sumSq=0
... | x²=0 , tail=0 =
  cong₂ _∷_
    (square-zero-only-at-origin x x²=0)
    (sumSq-zero-only-at-origin-from-local-kernel
      square-zero-only-at-origin
      sumSq-zero-splits
      xs
      tail=0)

q̂core-zero→sumSq-zero :
  ∀ {m} →
  (x : PD.Additive.Carrier (QES.AdditiveVecℤ {m})) →
  QP.Q̂core x
  ≡
  QF.ScalarField.0s QES.ScalarFieldℤ
  →
  HFZ.sumSq x
  ≡
  QF.ScalarField.0s QES.ScalarFieldℤ
q̂core-zero→sumSq-zero x q̂x=0 =
  trans
    (sym (Q̂core≡sumSq x))
    q̂x=0

q̂core-zero-only-at-origin-from-sumSq :
  ∀ {m} →
  CoreAnisotropyResidualPremise m →
  (x : PD.Additive.Carrier (QES.AdditiveVecℤ {m})) →
  QP.Q̂core x
  ≡
  QF.ScalarField.0s QES.ScalarFieldℤ
  →
  x ≡ QP.zeroVecℤ {m}
q̂core-zero-only-at-origin-from-sumSq sumSq-zero-only-at-origin x q̂x=0 =
  sumSq-zero-only-at-origin x (q̂core-zero→sumSq-zero x q̂x=0)

record CoreAnisotropyAssumption
  (m : Nat) : Setω where
  field
    square-zero-only-at-origin :
      SquareZeroResidualPremise
    sumSq-zero-splits :
      SumSqZeroDecompositionPremise

  sumSq-zero-only-at-origin :
    CoreAnisotropyResidualPremise m
  sumSq-zero-only-at-origin =
    sumSq-zero-only-at-origin-from-local-kernel
      square-zero-only-at-origin
      sumSq-zero-splits

  q̂core-zero-only-at-origin :
    ∀ x →
      QP.Q̂core x
      ≡
      QF.ScalarField.0s QES.ScalarFieldℤ
      →
      x ≡ QP.zeroVecℤ {m}
  q̂core-zero-only-at-origin x q̂x=0 =
    q̂core-zero-only-at-origin-from-sumSq
      sumSq-zero-only-at-origin
      x
      q̂x=0

mkCoreAnisotropyAssumption :
  ∀ {m} →
  SquareZeroResidualPremise →
  SumSqZeroDecompositionPremise →
  CoreAnisotropyAssumption m
mkCoreAnisotropyAssumption
  square-zero-only-at-origin
  sumSq-zero-splits =
  record
    { square-zero-only-at-origin = square-zero-only-at-origin
    ; sumSq-zero-splits = sumSq-zero-splits
    }

dischargedCoreAnisotropyAssumption :
  ∀ {m} →
  CoreAnisotropyAssumption m
dischargedCoreAnisotropyAssumption =
  mkCoreAnisotropyAssumption
    squareZeroResidualTheorem
    sumSqZeroDecompositionTheorem

record AdmissibleFor
  (m : Nat)
  (Δ : PD.Additive.Carrier (QES.AdditiveVecℤ {m}) →
       PD.Additive.Carrier (QES.AdditiveVecℤ {m}))
  (q : QF.QuadraticForm (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ) : Setω where
  field
    invariantUnderΔ :
      ∀ x →
        QF.QuadraticForm.Q q (Δ x) ≡ QF.QuadraticForm.Q q x
    nondegeneracySeam : NondegeneracySeam m q
    isotropyCompatibilitySeam : IsotropyCompatibilitySeam m Δ q
    nondegenerate : ⊤
    compatibleWithIsotropy : ⊤
    uniqueUpToScale : UniqueUpToScaleSeam m q

admissibleForNormalization :
  ∀ {m Δ q} →
  AdmissibleFor m Δ q →
  ∀ x →
    QF.QuadraticForm.Q q x ≡ QP.Q̂core x
admissibleForNormalization a x =
  UniqueUpToScaleSeam.normalizeToQ̂core
    (AdmissibleFor.uniqueUpToScale a)
    x

admissibleForScaledNormalization :
  ∀ {m Δ q} →
  (a : AdmissibleFor m Δ q) →
  ∀ x →
    QF.QuadraticForm.Q q x
    ≡
    QF.ScalarField._*s_ QES.ScalarFieldℤ
      (UniqueUpToScaleSeam.scaleFactor
        (AdmissibleFor.uniqueUpToScale a))
      (QP.Q̂core x)
admissibleForScaledNormalization a x =
  UniqueUpToScaleSeam.normalizeToScaledQ̂core
    (AdmissibleFor.uniqueUpToScale a)
    x

admissibleForCoreScaleSeam :
  ∀ {m Δ q} →
  (a : AdmissibleFor m Δ q) →
  CoreScaleSeam
    m
    (UniqueUpToScaleSeam.scaleFactor
      (AdmissibleFor.uniqueUpToScale a))
admissibleForCoreScaleSeam a =
  mkCoreScaleSeam
    (UniqueUpToScaleSeam.scaleFactor
      (AdmissibleFor.uniqueUpToScale a))
    (λ x →
      trans
        (sym (admissibleForNormalization a x))
        (admissibleForScaledNormalization a x))

admissibleForPositiveDimensionScaleFactorUnit :
  ∀ {m Δ q} →
  (a : AdmissibleFor (suc m) Δ q) →
  UniqueUpToScaleSeam.scaleFactor
    (AdmissibleFor.uniqueUpToScale a)
  ≡
  oneℤ
admissibleForPositiveDimensionScaleFactorUnit a =
  positiveDimensionCoreScaleSeamForcesUnit
    (admissibleForCoreScaleSeam a)

admissibleForNondegeneracyNormalization :
  ∀ {m Δ q} →
  AdmissibleFor m Δ q →
  ∀ x →
    QF.QuadraticForm.Q q x ≡ QP.Q̂core x
admissibleForNondegeneracyNormalization a =
  NondegeneracySeam.normalizeToQ̂core
    (AdmissibleFor.nondegeneracySeam a)

record QuadraticUniquenessBridge
  (m : Nat)
  (q : QF.QuadraticForm (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ) : Setω where
  field
    referenceQuadratic :
      QF.QuadraticForm (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ
    invariantMatchesReference :
      ∀ x →
        QF.QuadraticForm.Q q x
        ≡
        QF.QuadraticForm.Q referenceQuadratic x
    uniqueness :
      UniqueUpToScaleSeam m referenceQuadratic

mkQuadraticUniquenessBridge :
  ∀ {m}
  (q : QF.QuadraticForm (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ) →
  (∀ x → QF.QuadraticForm.Q q x ≡ QF.QuadraticForm.Q q x) →
  (∀ x → QF.QuadraticForm.Q q x ≡ QP.Q̂core x) →
  QuadraticUniquenessBridge m q
mkQuadraticUniquenessBridge q matches uniqueness =
  record
    { referenceQuadratic = q
    ; invariantMatchesReference = matches
    ; uniqueness = mkUniqueUpToScaleSeam uniqueness
    }

record ContractionForcesQuadraticStrong : Setω where
  field
    dimension : Nat
    projection : PD.ProjectionDefect (QES.AdditiveVecℤ {dimension})
    projectionParallelogram :
      PDP.ProjectionDefectParallelogramPackage
        (QES.AdditiveVecℤ {dimension}) QES.ScalarFieldℤ
    projectionQuadraticWitness :
      PDP.ProjectionDefectQuadraticWitness
        (QES.AdditiveVecℤ {dimension}) QES.ScalarFieldℤ
    derivedQuadratic :
      QF.QuadraticForm (QES.AdditiveVecℤ {dimension}) QES.ScalarFieldℤ
    dynamicsMap :
      PD.Additive.Carrier (QES.AdditiveVecℤ {dimension}) →
      PD.Additive.Carrier (QES.AdditiveVecℤ {dimension})
    invariantUnderT :
      ∀ x →
        QF.QuadraticForm.Q derivedQuadratic (dynamicsMap x)
        ≡
        QF.QuadraticForm.Q derivedQuadratic x
    nondegeneracySeam :
      NondegeneracySeam dimension derivedQuadratic
    isotropyCompatibilitySeam :
      IsotropyCompatibilitySeam dimension dynamicsMap derivedQuadratic
    nondegenerate : ⊤
    compatibleWithIsotropy : ⊤
    quadraticUniquenessBridge :
      QuadraticUniquenessBridge dimension derivedQuadratic

record SignatureCliffordGaugeBoundary
  (c : ContractionForcesQuadraticStrong) : Setω where
  field
    normalizedQuadraticOnly :
      ∀ x →
        QF.QuadraticForm.Q
          (ContractionForcesQuadraticStrong.derivedQuadratic c)
          x
        ≡
        QP.Q̂core x

signatureCliffordGaugeBoundary :
  (c : ContractionForcesQuadraticStrong) →
  SignatureCliffordGaugeBoundary c
signatureCliffordGaugeBoundary c =
  record
    { normalizedQuadraticOnly =
        λ x →
          trans
            (QuadraticUniquenessBridge.invariantMatchesReference
              (ContractionForcesQuadraticStrong.quadraticUniquenessBridge c) x)
            (UniqueUpToScaleSeam.normalizeToQ̂core
              (QuadraticUniquenessBridge.uniqueness
                (ContractionForcesQuadraticStrong.quadraticUniquenessBridge c))
              x)
    }

invariantQuadraticWitness :
  (c : ContractionForcesQuadraticStrong) →
  ∀ x →
    QF.QuadraticForm.Q
      (ContractionForcesQuadraticStrong.derivedQuadratic c)
      (ContractionForcesQuadraticStrong.dynamicsMap c x)
    ≡
    QF.QuadraticForm.Q
      (ContractionForcesQuadraticStrong.derivedQuadratic c)
      x
invariantQuadraticWitness c =
  ContractionForcesQuadraticStrong.invariantUnderT c

strongExplicitIsotropyStructure :
  (c : ContractionForcesQuadraticStrong) →
  ExplicitIsotropyStructure
    (ContractionForcesQuadraticStrong.dimension c)
    (ContractionForcesQuadraticStrong.dynamicsMap c)
    (ContractionForcesQuadraticStrong.derivedQuadratic c)
strongExplicitIsotropyStructure c =
  IsotropyCompatibilitySeam.explicitIsotropyStructure
    (ContractionForcesQuadraticStrong.isotropyCompatibilitySeam c)

strongResidualIsotropyGap :
  (c : ContractionForcesQuadraticStrong) →
  ResidualIsotropyGap (ContractionForcesQuadraticStrong.dimension c)
strongResidualIsotropyGap c =
  IsotropyCompatibilitySeam.residualIsotropyGap
    (ContractionForcesQuadraticStrong.isotropyCompatibilitySeam c)

strongShellBoundaryLiftsToActionTransport :
  (c : ContractionForcesQuadraticStrong) →
  ∀ x y →
    (sameShell : QP.Q̂core x ≡ QP.Q̂core y) →
    ResidualIsotropyGap.shellTransportBoundary
      (strongResidualIsotropyGap c)
      x y sameShell →
    Σ
      (ResidualIsotropyGap.isotropyAction (strongResidualIsotropyGap c))
      (λ ρ →
        Σ
          (ResidualIsotropyGap.applyIsotropyAction
            (strongResidualIsotropyGap c)
            ρ x
            ≡ y)
          (λ _ →
            ResidualIsotropyGap.actionPreservesQ̂core
              (strongResidualIsotropyGap c)
              ρ))
strongShellBoundaryLiftsToActionTransport c =
  shellBoundaryLiftsToActionTransport
    (ContractionForcesQuadraticStrong.isotropyCompatibilitySeam c)

strongShellBoundaryLiftsToActionTransportWitness :
  (c : ContractionForcesQuadraticStrong) →
  ∀ x y →
    (sameShell : QP.Q̂core x ≡ QP.Q̂core y) →
    ResidualIsotropyGap.shellTransportBoundary
      (strongResidualIsotropyGap c)
      x y sameShell →
    Σ
      (ResidualIsotropyGap.isotropyAction (strongResidualIsotropyGap c))
      (λ ρ →
        Σ
          (ResidualIsotropyGap.applyIsotropyAction
            (strongResidualIsotropyGap c)
            ρ x
            ≡ y)
          (λ _ →
            ∀ z →
              QP.Q̂core
                (ResidualIsotropyGap.applyIsotropyAction
                  (strongResidualIsotropyGap c)
                  ρ z)
              ≡
              QP.Q̂core z))
strongShellBoundaryLiftsToActionTransportWitness c =
  shellBoundaryLiftsToActionTransportWitness
    (ContractionForcesQuadraticStrong.isotropyCompatibilitySeam c)

strongShellBoundaryInhabitsIsotropyTransport :
  (c : ContractionForcesQuadraticStrong) →
  ∀ x y →
    (sameShell : QP.Q̂core x ≡ QP.Q̂core y) →
    ResidualIsotropyGap.shellTransportBoundary
      (strongResidualIsotropyGap c)
      x y sameShell →
    InhabitedIsotropyTransport
      (strongResidualIsotropyGap c)
      x y
strongShellBoundaryInhabitsIsotropyTransport c =
  shellBoundaryInhabitsIsotropyTransport
    (ContractionForcesQuadraticStrong.isotropyCompatibilitySeam c)

strongInhabitedIsotropyTransportPreservesDerivedQuadratic :
  (c : ContractionForcesQuadraticStrong) →
  ∀ {x y} →
    (transport :
      InhabitedIsotropyTransport
        (strongResidualIsotropyGap c)
        x y) →
    ∀ z →
      QF.QuadraticForm.Q
        (ContractionForcesQuadraticStrong.derivedQuadratic c)
        (ContractionForcesQuadraticStrong.dynamicsMap c
          (ResidualIsotropyGap.applyIsotropyAction
            (strongResidualIsotropyGap c)
            (InhabitedIsotropyTransport.transporter
              {gap = strongResidualIsotropyGap c}
              transport)
            z))
      ≡
      QF.QuadraticForm.Q
        (ContractionForcesQuadraticStrong.derivedQuadratic c)
        (ContractionForcesQuadraticStrong.dynamicsMap c z)
strongInhabitedIsotropyTransportPreservesDerivedQuadratic c =
  inhabitedIsotropyTransportPreservesDerivedQuadratic
    (ContractionForcesQuadraticStrong.isotropyCompatibilitySeam c)

strongInhabitedIsotropyTransportPreservesTargetQuadratic :
  (c : ContractionForcesQuadraticStrong) →
  ∀ {x y} →
    (transport :
      InhabitedIsotropyTransport
        (strongResidualIsotropyGap c)
        x y) →
    QF.QuadraticForm.Q
      (ContractionForcesQuadraticStrong.derivedQuadratic c)
      (ContractionForcesQuadraticStrong.dynamicsMap c y)
    ≡
    QF.QuadraticForm.Q
      (ContractionForcesQuadraticStrong.derivedQuadratic c)
      (ContractionForcesQuadraticStrong.dynamicsMap c x)
strongInhabitedIsotropyTransportPreservesTargetQuadratic c =
  inhabitedIsotropyTransportPreservesTargetQuadratic
    (ContractionForcesQuadraticStrong.isotropyCompatibilitySeam c)

strongShellRespectingAlongT :
  (c : ContractionForcesQuadraticStrong) →
  ∀ x y →
    QP.Q̂core x ≡ QP.Q̂core y →
    QF.QuadraticForm.Q
      (ContractionForcesQuadraticStrong.derivedQuadratic c)
      (ContractionForcesQuadraticStrong.dynamicsMap c x)
    ≡
    QF.QuadraticForm.Q
      (ContractionForcesQuadraticStrong.derivedQuadratic c)
      (ContractionForcesQuadraticStrong.dynamicsMap c y)
strongShellRespectingAlongT c =
  shellRespectingAlongΔ
    (ContractionForcesQuadraticStrong.isotropyCompatibilitySeam c)

strongNondegeneracyNormalization :
  (c : ContractionForcesQuadraticStrong) →
  ∀ x →
    QF.QuadraticForm.Q
      (ContractionForcesQuadraticStrong.derivedQuadratic c)
      x
    ≡
    QP.Q̂core x
strongNondegeneracyNormalization c =
  NondegeneracySeam.normalizeToQ̂core
    (ContractionForcesQuadraticStrong.nondegeneracySeam c)

strongZeroNormalized :
  (c : ContractionForcesQuadraticStrong) →
  QF.QuadraticForm.Q
    (ContractionForcesQuadraticStrong.derivedQuadratic c)
    (QP.zeroVecℤ {ContractionForcesQuadraticStrong.dimension c})
  ≡
  QF.ScalarField.0s QES.ScalarFieldℤ
strongZeroNormalized c =
  NondegeneracySeam.zeroNormalized
    (ContractionForcesQuadraticStrong.nondegeneracySeam c)

strongNullConeReflectsCore :
  (c : ContractionForcesQuadraticStrong) →
  ∀ x →
    QF.QuadraticForm.Q
      (ContractionForcesQuadraticStrong.derivedQuadratic c)
      x
    ≡
    QF.ScalarField.0s QES.ScalarFieldℤ
    →
    QP.Q̂core x
    ≡
    QF.ScalarField.0s QES.ScalarFieldℤ
strongNullConeReflectsCore c x qx=0 =
  trans
    (sym (strongNondegeneracyNormalization c x))
    qx=0

strongNondegeneracyFromCoreSumSqAnisotropy :
  (c : ContractionForcesQuadraticStrong) →
  CoreAnisotropyResidualPremise
    (ContractionForcesQuadraticStrong.dimension c) →
  ∀ x →
    QF.QuadraticForm.Q
      (ContractionForcesQuadraticStrong.derivedQuadratic c)
      x
    ≡
    QF.ScalarField.0s QES.ScalarFieldℤ
    →
    x ≡
      QP.zeroVecℤ
        {ContractionForcesQuadraticStrong.dimension c}
strongNondegeneracyFromCoreSumSqAnisotropy c sumSq-zero-only-at-origin x qx=0 =
  q̂core-zero-only-at-origin-from-sumSq
    sumSq-zero-only-at-origin
    x
    (strongNullConeReflectsCore c x qx=0)

strongNondegeneracyFromCoreAnisotropy :
  (c : ContractionForcesQuadraticStrong) →
  CoreAnisotropyAssumption
    (ContractionForcesQuadraticStrong.dimension c) →
  ∀ x →
    QF.QuadraticForm.Q
      (ContractionForcesQuadraticStrong.derivedQuadratic c)
      x
    ≡
    QF.ScalarField.0s QES.ScalarFieldℤ
    →
    x ≡
      QP.zeroVecℤ
        {ContractionForcesQuadraticStrong.dimension c}
strongNondegeneracyFromCoreAnisotropy c coreAnisotropy x qx=0 =
  strongNondegeneracyFromCoreSumSqAnisotropy
    c
    (CoreAnisotropyAssumption.sumSq-zero-only-at-origin coreAnisotropy)
    x
    qx=0

strongNondegeneracy :
  (c : ContractionForcesQuadraticStrong) →
  ∀ x →
    QF.QuadraticForm.Q
      (ContractionForcesQuadraticStrong.derivedQuadratic c)
      x
    ≡
    QF.ScalarField.0s QES.ScalarFieldℤ
    →
    x ≡
      QP.zeroVecℤ
        {ContractionForcesQuadraticStrong.dimension c}
strongNondegeneracy c =
  strongNondegeneracyFromCoreAnisotropy
    c
    dischargedCoreAnisotropyAssumption

uniqueUpToScaleScaledWitness :
  (c : ContractionForcesQuadraticStrong) →
  ∀ x →
    QF.QuadraticForm.Q
      (ContractionForcesQuadraticStrong.derivedQuadratic c) x
    ≡
    QF.ScalarField._*s_ QES.ScalarFieldℤ
      (UniqueUpToScaleSeam.scaleFactor
        (QuadraticUniquenessBridge.uniqueness
          (ContractionForcesQuadraticStrong.quadraticUniquenessBridge c)))
      (QP.Q̂core x)
uniqueUpToScaleScaledWitness c x =
  trans
    (QuadraticUniquenessBridge.invariantMatchesReference
      (ContractionForcesQuadraticStrong.quadraticUniquenessBridge c) x)
    (UniqueUpToScaleSeam.normalizeToScaledQ̂core
      (QuadraticUniquenessBridge.uniqueness
        (ContractionForcesQuadraticStrong.quadraticUniquenessBridge c))
      x)

uniqueUpToScaleWitness :
  (c : ContractionForcesQuadraticStrong) →
  ∀ x →
    QF.QuadraticForm.Q
      (ContractionForcesQuadraticStrong.derivedQuadratic c) x
    ≡
    QP.Q̂core x
uniqueUpToScaleWitness c x =
  trans
    (QuadraticUniquenessBridge.invariantMatchesReference
      (ContractionForcesQuadraticStrong.quadraticUniquenessBridge c) x)
    (UniqueUpToScaleSeam.normalizeToQ̂core
      (QuadraticUniquenessBridge.uniqueness
        (ContractionForcesQuadraticStrong.quadraticUniquenessBridge c))
      x)

-- Canonicality lemma: if an alternative admissible quadratic presentation is
-- also normalized to Q^core on the same carrier, it agrees pointwise with the
-- canonical strong output.
canonicalQuadraticAgreement :
  (c : ContractionForcesQuadraticStrong) →
  (q′ :
    QF.QuadraticForm
      (QES.AdditiveVecℤ
        {ContractionForcesQuadraticStrong.dimension c})
      QES.ScalarFieldℤ) →
  UniqueUpToScaleSeam
    (ContractionForcesQuadraticStrong.dimension c) q′ →
  ∀ x →
    QF.QuadraticForm.Q
      (ContractionForcesQuadraticStrong.derivedQuadratic c)
      x
    ≡
    QF.QuadraticForm.Q q′ x
canonicalQuadraticAgreement c q′ uniq′ x =
  trans
    (uniqueUpToScaleWitness c x)
    (sym (UniqueUpToScaleSeam.normalizeToQ̂core uniq′ x))

-- Scale-aware canonicality lemma: an admissible alternative quadratic agrees
-- with the canonical strong output up to its recorded scale factor.
canonicalQuadraticAgreementUpToScale :
  (c : ContractionForcesQuadraticStrong) →
  (q′ :
    QF.QuadraticForm
      (QES.AdditiveVecℤ
        {ContractionForcesQuadraticStrong.dimension c})
      QES.ScalarFieldℤ) →
  (uniq′ :
    UniqueUpToScaleSeam
      (ContractionForcesQuadraticStrong.dimension c) q′) →
  ∀ x →
    QF.QuadraticForm.Q q′ x
    ≡
    QF.ScalarField._*s_ QES.ScalarFieldℤ
      (UniqueUpToScaleSeam.scaleFactor uniq′)
      (QF.QuadraticForm.Q
        (ContractionForcesQuadraticStrong.derivedQuadratic c)
        x)
canonicalQuadraticAgreementUpToScale c q′ uniq′ x =
  trans
    (UniqueUpToScaleSeam.normalizeToScaledQ̂core uniq′ x)
    (cong
      (λ t →
        QF.ScalarField._*s_ QES.ScalarFieldℤ
          (UniqueUpToScaleSeam.scaleFactor uniq′)
          t)
      (sym (uniqueUpToScaleWitness c x)))

canonicalQuadraticAgreementToQ̂core :
  (c : ContractionForcesQuadraticStrong) →
  ∀ x →
    QF.QuadraticForm.Q
      (ContractionForcesQuadraticStrong.derivedQuadratic c)
      x
    ≡ QP.Q̂core x
canonicalQuadraticAgreementToQ̂core c =
  strongNondegeneracyNormalization c

buildContractionForcesQuadraticStrong :
  (m : Nat) →
  (dynamics :
    PD.Additive.Carrier (QES.AdditiveVecℤ {m}) →
    PD.Additive.Carrier (QES.AdditiveVecℤ {m})) →
  (invariantQ :
    ∀ x →
      QF.QuadraticForm.Q
        (proj₁
          (PDP.quadraticFromProjectionDefect
            (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ
            (PDSP.projectionDefectParallelogramFromSplit {m})))
        (dynamics x)
      ≡
      QF.QuadraticForm.Q
        (proj₁
          (PDP.quadraticFromProjectionDefect
            (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ
            (PDSP.projectionDefectParallelogramFromSplit {m})))
        x) →
  (uniqueness :
    ∀ x →
      QF.QuadraticForm.Q
        (proj₁
          (PDP.quadraticFromProjectionDefect
            (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ
            (PDSP.projectionDefectParallelogramFromSplit {m})))
        x
      ≡ QP.Q̂core x) →
  ContractionForcesQuadraticStrong
buildContractionForcesQuadraticStrong m dynamics invariantQ uniqueness =
  let
    proj = QES.PDzero {m}
    pkg = PDSP.projectionDefectParallelogramFromSplit {m}
    q = proj₁
          (PDP.quadraticFromProjectionDefect
             (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ pkg)
  in
  record
    { dimension = m
    ; projection = proj
    ; projectionParallelogram = pkg
    ; projectionQuadraticWitness =
        PDP.fromProjectionPackageWitness
          (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ pkg
    ; derivedQuadratic = q
    ; dynamicsMap = dynamics
    ; invariantUnderT = invariantQ
    ; nondegeneracySeam =
        mkNondegeneracySeam uniqueness
    ; isotropyCompatibilitySeam =
        mkIsotropyCompatibilitySeam
          (λ x → trans (invariantQ x) (uniqueness x))
          defaultResidualIsotropyGap
    ; nondegenerate = tt
    ; compatibleWithIsotropy = tt
    ; quadraticUniquenessBridge =
        mkQuadraticUniquenessBridge q (λ _ → refl) uniqueness
    }

admissibleForFromStrongAtScaleSeam :
  (c : ContractionForcesQuadraticStrong) →
  ∀ {scale : QF.ScalarField.S QES.ScalarFieldℤ} →
  CoreScaleSeam
    (ContractionForcesQuadraticStrong.dimension c)
    scale →
  AdmissibleFor
    (ContractionForcesQuadraticStrong.dimension c)
    (ContractionForcesQuadraticStrong.dynamicsMap c)
    (ContractionForcesQuadraticStrong.derivedQuadratic c)
admissibleForFromStrongAtScaleSeam c {scale} seam =
  record
    { invariantUnderΔ = ContractionForcesQuadraticStrong.invariantUnderT c
    ; nondegeneracySeam =
        ContractionForcesQuadraticStrong.nondegeneracySeam c
    ; isotropyCompatibilitySeam =
        ContractionForcesQuadraticStrong.isotropyCompatibilitySeam c
    ; nondegenerate = ContractionForcesQuadraticStrong.nondegenerate c
    ; compatibleWithIsotropy =
        ContractionForcesQuadraticStrong.compatibleWithIsotropy c
    ; uniqueUpToScale =
        mkUniqueUpToScaleSeamAtScale
          scale
          (λ x →
            trans
              (uniqueUpToScaleWitness c x)
              (CoreScaleSeam.scaleQ̂core seam x))
          (uniqueUpToScaleWitness c)
    }

admissibleForFromStrongAtScale :
  (c : ContractionForcesQuadraticStrong) →
  (scale :
    QF.ScalarField.S QES.ScalarFieldℤ) →
  (∀ x →
    QP.Q̂core x
    ≡
    QF.ScalarField._*s_ QES.ScalarFieldℤ
      scale
      (QP.Q̂core x)) →
  AdmissibleFor
    (ContractionForcesQuadraticStrong.dimension c)
    (ContractionForcesQuadraticStrong.dynamicsMap c)
    (ContractionForcesQuadraticStrong.derivedQuadratic c)
admissibleForFromStrongAtScale c scale scaleQ̂core =
  admissibleForFromStrongAtScaleSeam
    c
    (mkCoreScaleSeam scale scaleQ̂core)

admissibleForFromStrongAtScaleScalarFixedPoint :
  (c : ContractionForcesQuadraticStrong) →
  (scale :
    QF.ScalarField.S QES.ScalarFieldℤ) →
  (∀ z →
    z
    ≡
    QF.ScalarField._*s_ QES.ScalarFieldℤ
      scale
      z) →
  AdmissibleFor
    (ContractionForcesQuadraticStrong.dimension c)
    (ContractionForcesQuadraticStrong.dynamicsMap c)
    (ContractionForcesQuadraticStrong.derivedQuadratic c)
admissibleForFromStrongAtScaleScalarFixedPoint c scale scalarFixedPoint =
  admissibleForFromStrongAtScaleSeam
    c
    (mkCoreScaleSeamFromScalarFixedPoint scale scalarFixedPoint)

admissibleForFromStrong :
  (c : ContractionForcesQuadraticStrong) →
  AdmissibleFor
    (ContractionForcesQuadraticStrong.dimension c)
    (ContractionForcesQuadraticStrong.dynamicsMap c)
    (ContractionForcesQuadraticStrong.derivedQuadratic c)
admissibleForFromStrong c =
  admissibleForFromStrongAtScale
    c
    (QF.ScalarField.1s QES.ScalarFieldℤ)
    (λ x → sym (IntP.*-identityˡ (QP.Q̂core x)))

doubleScaleFactor : QF.ScalarField.S QES.ScalarFieldℤ
doubleScaleFactor =
  QF.ScalarField._+s_ QES.ScalarFieldℤ
    (QF.ScalarField.1s QES.ScalarFieldℤ)
    (QF.ScalarField.1s QES.ScalarFieldℤ)

zeroCoreScalesAtDimension :
  ∀ {m} →
  m ≡ 0 →
  (scale : QF.ScalarField.S QES.ScalarFieldℤ) →
  ∀ (x : PD.Additive.Carrier (QES.AdditiveVecℤ {m})) →
    QP.Q̂core x
    ≡
    QF.ScalarField._*s_ QES.ScalarFieldℤ
      scale
      (QP.Q̂core x)
zeroCoreScalesAtDimension {zero} refl scale [] =
  trans
    refl
    (sym (IntP.*-zeroʳ scale))

zeroDimensionalCoreScales :
  (scale : QF.ScalarField.S QES.ScalarFieldℤ) →
  ∀ (x : PD.Additive.Carrier (QES.AdditiveVecℤ {0})) →
    QP.Q̂core x
    ≡
    QF.ScalarField._*s_ QES.ScalarFieldℤ
      scale
      (QP.Q̂core x)
zeroDimensionalCoreScales scale =
  zeroCoreScalesAtDimension refl scale

zeroCoreScaleSeamAtDimension :
  ∀ {m} →
  m ≡ 0 →
  (scale : QF.ScalarField.S QES.ScalarFieldℤ) →
  CoreScaleSeam m scale
zeroCoreScaleSeamAtDimension dimensionZero scale =
  mkCoreScaleSeam
    scale
    (zeroCoreScalesAtDimension dimensionZero scale)

admissibleForFromStrongAtZeroDimensionScale :
  (c : ContractionForcesQuadraticStrong) →
  ContractionForcesQuadraticStrong.dimension c ≡ 0 →
  (scale : QF.ScalarField.S QES.ScalarFieldℤ) →
  AdmissibleFor
    (ContractionForcesQuadraticStrong.dimension c)
    (ContractionForcesQuadraticStrong.dynamicsMap c)
    (ContractionForcesQuadraticStrong.derivedQuadratic c)
admissibleForFromStrongAtZeroDimensionScale c dimensionZero scale =
  admissibleForFromStrongAtScaleSeam
    c
    (zeroCoreScaleSeamAtDimension dimensionZero scale)

canonicalZeroStrong : ContractionForcesQuadraticStrong
canonicalZeroStrong =
  buildContractionForcesQuadraticStrong
    0
    (λ x → x)
    (λ _ → refl)
    (λ _ → refl)

canonicalZeroDoubleScaleAdmissible :
  AdmissibleFor
    (ContractionForcesQuadraticStrong.dimension canonicalZeroStrong)
    (ContractionForcesQuadraticStrong.dynamicsMap canonicalZeroStrong)
    (ContractionForcesQuadraticStrong.derivedQuadratic canonicalZeroStrong)
canonicalZeroDoubleScaleAdmissible =
  admissibleForFromStrongAtZeroDimensionScale
    canonicalZeroStrong
    refl
    doubleScaleFactor

canonicalZeroDoubleScaleFactorWitness :
  UniqueUpToScaleSeam.scaleFactor
    (AdmissibleFor.uniqueUpToScale canonicalZeroDoubleScaleAdmissible)
  ≡
  doubleScaleFactor
canonicalZeroDoubleScaleFactorWitness = refl

canonicalIdentityInvariantStrong :
  (m : Nat) →
  ContractionForcesQuadraticStrong
canonicalIdentityInvariantStrong m =
  buildContractionForcesQuadraticStrong
    m
    (λ x → x)
    (λ _ → refl)
    (λ _ → refl)

canonicalSignedPerm4InvariantStrong :
  (sp : SP.SignedPerm4) →
  ContractionForcesQuadraticStrong
canonicalSignedPerm4InvariantStrong sp =
  buildContractionForcesQuadraticStrong
    4
    (S31.actIso4 sp)
    (S31.qcore-pres4 sp)
    (λ _ → refl)

nontrivialSignedPerm4 : SP.SignedPerm4
nontrivialSignedPerm4 =
  record
    { perm = SP.p120
    ; flipT = false
    ; flipS = false ∷ true ∷ false ∷ []
    }

canonicalNontrivialInvariantStrong : ContractionForcesQuadraticStrong
canonicalNontrivialInvariantStrong =
  canonicalSignedPerm4InvariantStrong nontrivialSignedPerm4
