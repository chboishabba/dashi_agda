module DASHI.Geometry.ShiftLorentzEmergenceInstance where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Nat using (Nat; _+_; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (trans)
open import Data.Bool using (true)
open import Data.Integer using (ℤ; _≤_; _*_; +_)
open import Data.Integer.Properties as IntP
open import Data.Nat using (z≤n; s≤s)
open import Data.Vec using (Vec; _∷_; [])

open import MDL.Core.Core as OldMDL
open import DASHI.Execution.Contract as Exec
open import DASHI.Execution.ShiftGeometryBridge as SGB
open import DASHI.Geometry.LorentzEmergence as LE
open import DASHI.Geometry.LorentzEmergenceFromCausalAxioms as LECA
open import DASHI.Geometry.CausalForcesLorentz31 as CFL
open import DASHI.Geometry.ParallelogramLaw using (AdditiveSpace)
open import DASHI.Geometry.ConeMetricCompatibility as CMC
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.LiftToFullState as LFS
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI
open import DASHI.Physics.Closure.MDLLyapunovShiftInstance as MDLL
open import DASHI.Physics.Closure.ContractionForcesQuadraticStrong as CFQS
open import DASHI.Physics.Closure.ShiftExecutionInvariantCore as SEIC
  using (shiftExecutionEigenProfile; zeroEigenProfile; shiftEigenOverlap; shiftIsoWitnessCore)
open import DASHI.MDL.MDLDescentTradeoff as MDL using (MDLParts)
open import DASHI.Algebra.Trit using (Trit; pos)
open import DASHI.Geometry.Signature.HyperbolicFormZ as HFZ
open import DASHI.Physics.QuadraticPolarization as QP
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
open import DASHI.Physics.TailCollapseProof as TCP
open import DASHI.Physics.SignedPerm4 as SP
open import DASHI.Physics.Signature31IntrinsicShiftInstance as S31I
open import DASHI.Physics.Signature31InstanceShiftZ as S31Z
open import Ontology.Hecke.PrimeHeckeEigenMotifPipeline as PHEM

private
  ShiftState : Nat → Nat → Set
  ShiftState m k = RTC.Carrier (m + k)

ShiftStep : ∀ {m k : Nat} → ShiftState m k → ShiftState m k
ShiftStep {suc zero} {suc (suc (suc zero))} =
  MDLParts.T (MSI.MDLPartsShift {suc zero} {suc (suc (suc zero))})
ShiftStep {_} {_} x = x

ShiftMDL : ∀ {m k : Nat} → ShiftState m k → Nat
ShiftMDL {suc zero} {suc (suc (suc zero))} =
  MDLParts.MDL (MSI.MDLPartsShift {suc zero} {suc (suc (suc zero))})
ShiftMDL {_} {_} _ = zero

ShiftProj : ∀ {m k : Nat} → ShiftState m k → ShiftState m k
ShiftProj x = x

ShiftDelta : ∀ {m k : Nat} → ShiftState m k → ShiftState m k
ShiftDelta {m} {k} = ShiftStep {m} {k}

ShiftProjectDelta : ∀ {m k : Nat} → ShiftState m k → ShiftState m k
ShiftProjectDelta x = x

ShiftArrow : ∀ {m k : Nat} → ShiftState m k → Nat
ShiftArrow _ = zero

ShiftQ : ∀ {m k : Nat} → ShiftState m k → Nat
ShiftQ _ = zero

ShiftCoarseHead :
  ShiftState (suc zero) (suc (suc (suc zero))) →
  Vec Trit (suc zero)
ShiftCoarseHead x =
  TCP.coarseOf (suc zero) (suc (suc (suc zero))) x

ShiftInBasin : ∀ {m k : Nat} → ShiftState m k → Set
ShiftInBasin {suc zero} {suc (suc (suc zero))} x = ShiftCoarseHead x ≡ pos ∷ []
ShiftInBasin {_} {_} _ = ⊤

ShiftEigen : Set
ShiftEigen = PHEM.EigenProfile

shiftExecToEigenState :
  ShiftState (suc zero) (suc (suc (suc zero))) →
  Vec ℤ S31Z.m
shiftExecToEigenState = QP.vecℤ

ShiftEigenOf : ∀ {m k : Nat} → ShiftState m k → ShiftEigen
ShiftEigenOf {suc zero} {suc (suc (suc zero))} x =
  shiftExecutionEigenProfile
    (shiftExecToEigenState x)
ShiftEigenOf {_} {_} _ = zeroEigenProfile

ShiftEigenOverlap : ShiftEigen → ShiftEigen → Nat
ShiftEigenOverlap = shiftEigenOverlap

ShiftOverlapFloor : ∀ {m k : Nat} → Nat
ShiftOverlapFloor {suc zero} {suc (suc (suc zero))} = suc zero
ShiftOverlapFloor {_} {_} = zero

-- Concrete runtime hook:
-- the shift stack already supplies the real carrier, step, and MDL descent.
canonicalShiftContract :
  Exec.Contract {ℓx = lzero} {ℓs = lzero} {ℓδ = lzero} {ℓπ = lzero} {ℓe = lzero}
canonicalShiftContract =
  record
    { State = ShiftState (suc zero) (suc (suc (suc zero)))
    ; Source = ShiftState (suc zero) (suc (suc (suc zero)))
    ; ΔState = ShiftState (suc zero) (suc (suc (suc zero)))
    ; ΔSource = ShiftState (suc zero) (suc (suc (suc zero)))
    ; Eigen = ShiftEigen
    ; step = ShiftStep {suc zero} {suc (suc (suc zero))}
    ; π = ShiftProj {suc zero} {suc (suc (suc zero))}
    ; Δ = ShiftDelta {suc zero} {suc (suc (suc zero))}
    ; projectΔ = ShiftProjectDelta {suc zero} {suc (suc (suc zero))}
    ; Arrow = ShiftArrow {suc zero} {suc (suc (suc zero))}
    ; Q = ShiftQ {suc zero} {suc (suc (suc zero))}
    ; L = ShiftMDL {suc zero} {suc (suc (suc zero))}
    ; InBasin = ShiftInBasin {suc zero} {suc (suc (suc zero))}
    ; eigenOf = ShiftEigenOf {suc zero} {suc (suc (suc zero))}
    ; eigenOverlap = ShiftEigenOverlap
    ; overlapFloor = ShiftOverlapFloor {suc zero} {suc (suc (suc zero))}
    }

fallbackShiftContract :
  ∀ {m k : Nat} →
  Exec.Contract {ℓx = lzero} {ℓs = lzero} {ℓδ = lzero} {ℓπ = lzero} {ℓe = lzero}
fallbackShiftContract {m} {k} =
  record
    { State = ShiftState m k
    ; Source = ShiftState m k
    ; ΔState = ShiftState m k
    ; ΔSource = ShiftState m k
    ; Eigen = ShiftEigen
    ; step = λ x → x
    ; π = ShiftProj {m} {k}
    ; Δ = λ x → x
    ; projectΔ = ShiftProjectDelta {m} {k}
    ; Arrow = ShiftArrow {m} {k}
    ; Q = ShiftQ {m} {k}
    ; L = λ _ → zero
    ; InBasin = ShiftInBasin {m} {k}
    ; eigenOf = λ _ → zeroEigenProfile
    ; eigenOverlap = ShiftEigenOverlap
    ; overlapFloor = zero
    }

canonicalShiftExecutionAdmissible :
  Exec.Contract.ExecutionAdmissible canonicalShiftContract
canonicalShiftExecutionAdmissible =
  let lyap = MDLL.lyapunovShift {m = suc zero} {k = suc (suc (suc zero))} in
  record
    { arrow-monotone = λ _ → z≤n
    ; cone-delta = λ _ → z≤n
    ; mdl-descent = OldMDL.Lyapunov.descent lyap
    ; basin-preserved = λ x h →
        trans
          (LFS.coarse-invariant-T (suc zero) (suc (suc (suc zero))) x)
          h
    ; eigen-overlap = λ _ → s≤s z≤n
    }

fallbackShiftExecutionAdmissible :
  ∀ {m k : Nat} →
  Exec.Contract.ExecutionAdmissible (fallbackShiftContract {m} {k})
fallbackShiftExecutionAdmissible =
  record
    { arrow-monotone = λ _ → z≤n
    ; cone-delta = λ _ → z≤n
    ; mdl-descent = λ _ → z≤n
    ; basin-preserved = λ _ b → b
    ; eigen-overlap = λ _ → z≤n
    }

record ShiftContractBundle {m k : Nat} : Set₁ where
  field
    contract :
      Exec.Contract {ℓx = lzero} {ℓs = lzero} {ℓδ = lzero} {ℓπ = lzero} {ℓe = lzero}
    admissible :
      Exec.Contract.ExecutionAdmissible contract

shiftContractBundle : ∀ {m k : Nat} → ShiftContractBundle {m} {k}
shiftContractBundle {m} {k} with m | k
... | suc zero | suc (suc (suc zero)) =
  record
    { contract = canonicalShiftContract
    ; admissible = canonicalShiftExecutionAdmissible
    }
... | _ | _ =
  record
    { contract = fallbackShiftContract {m} {k}
    ; admissible = fallbackShiftExecutionAdmissible {m} {k}
    }

shiftContract :
  ∀ {m k : Nat} →
  Exec.Contract {ℓx = lzero} {ℓs = lzero} {ℓδ = lzero} {ℓπ = lzero} {ℓe = lzero}
shiftContract {m} {k} = ShiftContractBundle.contract (shiftContractBundle {m} {k})

shiftExecutionAdmissible :
  ∀ {m k : Nat} →
  Exec.Contract.ExecutionAdmissible (shiftContract {m} {k})
shiftExecutionAdmissible {m} {k} =
  ShiftContractBundle.admissible (shiftContractBundle {m} {k})

ShiftGeoV : Set
ShiftGeoV = Vec ℤ S31Z.m

shiftAdditiveSpace : AdditiveSpace
shiftAdditiveSpace =
  record
    { V = ShiftGeoV
    ; _+_ = QP._+ᵥ_
    ; -_ = QES.negVec
    ; 0# = QP.zeroVecℤ {S31Z.m}
    }

shiftQuadratic : CMC.Quadratic shiftAdditiveSpace
shiftQuadratic =
  record
    { Scalar = ℤ
    ; Q = QP.Q̂core
    }

shiftCone : CMC.Cone shiftAdditiveSpace
shiftCone =
  record
    { InCone = λ x → HFZ.ConeBound (+ 1) (S31Z.toCounts x) }

shiftHyperbolicCompat :
  ∀ x → CMC.Cone.InCone shiftCone x → + 0 ≤ HFZ.F (+ 1) (+ 1) (S31Z.toCounts x)
shiftHyperbolicCompat (t ∷ s1 ∷ s2 ∷ s3 ∷ []) h
  rewrite IntP.*-identityˡ (t * t)
        | IntP.*-identityˡ (HFZ.sumSq (s1 ∷ s2 ∷ s3 ∷ [])) =
  IntP.i≤j⇒0≤j-i h

shiftConeCompat : CMC.ConeMetricCompat shiftAdditiveSpace shiftCone shiftQuadratic
shiftConeCompat =
  record
    { compat = λ x → + 0 ≤ HFZ.F (+ 1) (+ 1) (S31Z.toCounts x)
    ; cone⇒compat = shiftHyperbolicCompat
    }

shiftIso : Set
shiftIso = SP.SignedPerm4

shiftIsoWitness : shiftIso
shiftIsoWitness = shiftIsoWitnessCore

shiftFS : Set
shiftFS = Vec Trit (suc (suc (suc (suc zero))))

shiftArrowWitness : Set
shiftArrowWitness = HFZ.tau (S31Z.toCounts S31Z.zero4) ≡ (+ 0)

shiftConeWitness : CFL.ConeWitness shiftCone
shiftConeWitness =
  record
    { point = S31Z.shell1ConePoint
    ; pointInCone = S31Z.shell1ConeWitness
    }

shiftCausalPackage : CFL.CausalSymmetryPackage
shiftCausalPackage =
  record
    { coneNontrivial = CMC.Cone.InCone shiftCone (CFL.ConeWitness.point shiftConeWitness)
    ; coneNontrivialWitness = CFL.ConeWitness.pointInCone shiftConeWitness
    ; arrowOrientation = shiftArrowWitness
    ; arrowOrientationWitness = refl
    ; isotropyEvidence = shiftIso
    ; isotropyWitness = shiftIsoWitness
    ; finiteSpeed = shiftFS
    ; finiteSpeedWitness = S31Z.shell1SeedTrit
    ; involution = shiftIso
    ; involutionWitness = shiftIsoWitness
    ; nondegenerateQuadratic = ⊤
    ; nondegenerateQuadraticWitness =
        CFQS.ContractionForcesQuadraticStrong.nondegenerate
          CFQS.canonicalNontrivialInvariantStrong
    ; quotientContraction =
        ∀ x →
          TCP.coarseOf (suc zero) (suc (suc (suc zero))) (ShiftStep {suc zero} {suc (suc (suc zero))} x)
          ≡
          TCP.coarseOf (suc zero) (suc (suc (suc zero))) x
    ; quotientContractionWitness =
        MSI.coarse-invariant-T (suc zero) (suc (suc (suc zero)))
    }

shiftLorentzLock : CFL.LorentzSignatureLock
shiftLorentzLock =
  S31I.lorentzLock
    shiftQuadratic
    shiftCone
    shiftConeCompat
    shiftIso
    shiftFS
    shiftArrowWitness

shiftCausalBridgeInput :
  ∀ {m k : Nat} →
  LECA.CausalBridgeInput (shiftContract {m} {k})
shiftCausalBridgeInput {m} {k} =
  record
    { admissible = shiftExecutionAdmissible {m} {k}
    ; A = shiftAdditiveSpace
    ; q = shiftQuadratic
    ; cone = shiftCone
    ; compatibility = shiftConeCompat
    ; iso = shiftIso
    ; isoWitness = shiftIsoWitness
    ; fs = shiftFS
    ; arrow = shiftArrowWitness
    ; arrowWitness = refl
    ; coneWitness = shiftConeWitness
    ; pkg = shiftCausalPackage
    ; lock = shiftLorentzLock
    }

canonicalShiftGeometryBridge :
  SGB.DeltaToShiftGeometry (shiftContract {suc zero} {suc (suc (suc zero))})
canonicalShiftGeometryBridge =
  SGB.mkTernaryVec4Bridge
    (λ x → x)
    (λ x → x)

canonicalShiftStateWitness : ShiftState (suc zero) (suc (suc (suc zero)))
canonicalShiftStateWitness = S31Z.shell1SeedTrit

canonicalShiftExecutionConePoint : ShiftGeoV
canonicalShiftExecutionConePoint =
  SGB.execSourceVec4 canonicalShiftGeometryBridge canonicalShiftStateWitness

canonicalShiftExecutionConeWitness :
  CMC.Cone.InCone shiftCone canonicalShiftExecutionConePoint
canonicalShiftExecutionConeWitness = S31Z.shell1ConeWitness

canonicalShiftConeWitnessFromExecution : CFL.ConeWitness shiftCone
canonicalShiftConeWitnessFromExecution =
  record
    { point = canonicalShiftExecutionConePoint
    ; pointInCone = canonicalShiftExecutionConeWitness
    }

canonicalShiftCausalBridgeInput :
  LECA.CausalBridgeInput (shiftContract {suc zero} {suc (suc (suc zero))})
canonicalShiftCausalBridgeInput =
  record
    { admissible = shiftExecutionAdmissible {m = suc zero} {k = suc (suc (suc zero))}
    ; A = shiftAdditiveSpace
    ; q = shiftQuadratic
    ; cone = shiftCone
    ; compatibility = shiftConeCompat
    ; iso = shiftIso
    ; isoWitness = shiftIsoWitness
    ; fs = shiftFS
    ; arrow = shiftArrowWitness
    ; arrowWitness = refl
    ; coneWitness = canonicalShiftConeWitnessFromExecution
    ; pkg = shiftCausalPackage
    ; lock = shiftLorentzLock
    }

canonicalShiftLorentzEmergence :
  LE.LorentzEmergence (shiftContract {suc zero} {suc (suc (suc zero))})
canonicalShiftLorentzEmergence =
  LECA.lorentzEmergenceFromCausalAxioms canonicalShiftCausalBridgeInput

shiftLorentzEmergence :
  ∀ {m k : Nat} →
  LE.LorentzEmergence (shiftContract {m} {k})
shiftLorentzEmergence {m} {k} =
  LECA.lorentzEmergenceFromCausalAxioms (shiftCausalBridgeInput {m} {k})
