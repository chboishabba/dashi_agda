module DASHI.Physics.Closure.ShiftRGObservableInstance where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym; subst)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
import Data.Integer as Int
open import Data.Integer using (ℤ; +_)
open import Data.Nat.Properties as NatP using (_≟_)
open import Data.Vec using (_∷_; []; replicate)
open import Relation.Nullary.Decidable.Core using (yes; no)

open import DASHI.Execution.Contract as EC
open import DASHI.Execution.ShiftGeometryBridge as SGB
open import DASHI.Algebra.Trit using (Trit; zer)
open import DASHI.Geometry.ConeMetricCompatibility as CMC
open import DASHI.Geometry.ShiftLorentzEmergenceInstance as SLEI
open import DASHI.Physics.Closure.RGObservableInvariance as RGOI
open import DASHI.Physics.LiftToFullState as LFS
open import DASHI.Physics.Signature31InstanceShiftZ as S31Z
open import DASHI.Physics.SignedPerm4 as SP
open import DASHI.Physics.TailCollapseProof as TCP
open import Ontology.GodelLattice as GL
open import Ontology.Hecke.Scan as HS
open import Ontology.Hecke.PrimeHeckeEigenMotifPipeline as PHEM
open import MonsterOntos using (SSP; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31; p41; p47; p59; p71)

private
  ShiftC : EC.Contract
  ShiftC = SLEI.shiftContract {suc zero} {suc (suc (suc zero))}

  ShiftM : Nat
  ShiftM = suc zero

  ShiftK : Nat
  ShiftK = suc (suc (suc zero))

ShiftCanonicalInBasin : EC.Contract.State ShiftC → Set
ShiftCanonicalInBasin =
  SLEI.ShiftInBasin {m = ShiftM} {k = ShiftK}

data ShiftBasin : Set where
  canonicalBasin : ShiftBasin

data ShiftMotif : Set where
  earthMotif : ShiftMotif
  spokeMotif : ShiftMotif
  hubMotif : ShiftMotif
  balancedMotif : ShiftMotif

decToBool : ∀ {ℓ} {A : Set ℓ} → Relation.Nullary.Decidable.Core.Dec A → Bool
decToBool (yes _) = true
decToBool (no _) = false

countBool : Bool → Nat
countBool true = suc zero
countBool false = zero

timeCoord : SLEI.ShiftGeoV → ℤ
timeCoord (t ∷ _ ∷ _ ∷ _ ∷ []) = t

space1Coord : SLEI.ShiftGeoV → ℤ
space1Coord (_ ∷ s1 ∷ _ ∷ _ ∷ []) = s1

space2Coord : SLEI.ShiftGeoV → ℤ
space2Coord (_ ∷ _ ∷ s2 ∷ _ ∷ []) = s2

space3Coord : SLEI.ShiftGeoV → ℤ
space3Coord (_ ∷ _ ∷ _ ∷ s3 ∷ []) = s3

isZeroℤ : ℤ → Bool
isZeroℤ z = decToBool (Int._≟_ z (+ 0))

timeFlipIso : SP.SignedPerm4
timeFlipIso =
  record
    { perm = SP.p012
    ; flipT = false
    ; flipS = true ∷ true ∷ true ∷ []
    }

shiftHeckeAction : SSP → SLEI.ShiftGeoV → SLEI.ShiftGeoV
shiftHeckeAction p x with p
... | p2  = x
... | p3  = x
... | p5  = x
... | p7  = x
... | p11 = x
... | p13 = S31Z.actIso4 SLEI.shiftIsoWitness x
... | p17 = S31Z.actIso4 SLEI.shiftIsoWitness x
... | p19 = S31Z.actIso4 SLEI.shiftIsoWitness x
... | p23 = S31Z.actIso4 SLEI.shiftIsoWitness x
... | p29 = S31Z.actIso4 SLEI.shiftIsoWitness x
... | p31 = S31Z.actIso4 timeFlipIso x
... | p41 = S31Z.actIso4 timeFlipIso x
... | p47 = S31Z.actIso4 timeFlipIso x
... | p59 = S31Z.actIso4 timeFlipIso x
... | p71 = S31Z.actIso4 timeFlipIso x

shiftCompat : SSP → SLEI.ShiftGeoV → Bool
shiftCompat p x with p
... | p2  = isZeroℤ (timeCoord x)
... | p3  = isZeroℤ (space1Coord x)
... | p5  = isZeroℤ (space2Coord x)
... | p7  = isZeroℤ (space3Coord x)
... | p11 = decToBool (Int._≟_ (timeCoord (shiftHeckeAction p x)) (timeCoord x))
... | p13 = decToBool (Int._≟_ (space1Coord (shiftHeckeAction p x)) (space1Coord x))
... | p17 = decToBool (Int._≟_ (space2Coord (shiftHeckeAction p x)) (space2Coord x))
... | p19 = decToBool (Int._≟_ (space3Coord (shiftHeckeAction p x)) (space3Coord x))
... | p23 = decToBool (Int._≟_ (timeCoord (shiftHeckeAction p x)) (+ 0))
... | p29 = decToBool (Int._≟_ (space1Coord (shiftHeckeAction p x)) (+ 0))
... | p31 = decToBool (Int._≟_ (timeCoord (shiftHeckeAction p x)) (timeCoord x))
... | p41 = decToBool (Int._≟_ (space1Coord (shiftHeckeAction p x)) (space1Coord x))
... | p47 = decToBool (Int._≟_ (space2Coord (shiftHeckeAction p x)) (space2Coord x))
... | p59 = decToBool (Int._≟_ (space3Coord (shiftHeckeAction p x)) (space3Coord x))
... | p71 = decToBool (Int._≟_ (timeCoord (shiftHeckeAction p x)) (+ 0))

record ShiftHeckeAdapter : Set₁ where
  field
    fromGeometry : SLEI.ShiftGeoV → SLEI.ShiftGeoV
    toHeckeState : EC.Contract.State ShiftC → SLEI.ShiftGeoV
    toHeckeState≡fromGeometry :
      ∀ x →
      toHeckeState x
      ≡
      fromGeometry (SGB.execSourceVec4 SLEI.canonicalShiftGeometryBridge x)

open ShiftHeckeAdapter public

shiftHeckeAdapter : ShiftHeckeAdapter
shiftHeckeAdapter =
  record
    { fromGeometry = λ x → x
    ; toHeckeState = SGB.execSourceVec4 SLEI.canonicalShiftGeometryBridge
    ; toHeckeState≡fromGeometry = λ _ → refl
    }

canonicalShiftHeckeState :
  EC.Contract.State ShiftC → SLEI.ShiftGeoV
canonicalShiftHeckeState x =
  ShiftHeckeAdapter.fromGeometry
    shiftHeckeAdapter
    (SGB.execSourceVec4 SLEI.canonicalShiftGeometryBridge x)

zeroFactorVec : GL.FactorVec
zeroFactorVec =
  GL.v15
    zero zero zero zero zero
    zero zero zero zero zero
    zero zero zero zero zero

shiftPrimeEmbedding : SLEI.ShiftGeoV → GL.FactorVec
shiftPrimeEmbedding x =
  GL.v15
    (countBool (shiftCompat p2 x))
    (countBool (shiftCompat p3 x))
    (countBool (shiftCompat p5 x))
    (countBool (shiftCompat p7 x))
    (countBool (shiftCompat p11 x))
    (countBool (shiftCompat p13 x))
    (countBool (shiftCompat p17 x))
    (countBool (shiftCompat p19 x))
    (countBool (shiftCompat p23 x))
    (countBool (shiftCompat p29 x))
    (countBool (shiftCompat p31 x))
    (countBool (shiftCompat p41 x))
    (countBool (shiftCompat p47 x))
    (countBool (shiftCompat p59 x))
    (countBool (shiftCompat p71 x))

shiftSignatureEigenProfile : HS.Sig15 → PHEM.EigenProfile
shiftSignatureEigenProfile sig =
  PHEM.eigenProfile
    (countBool (HS.Sig15.b2 sig)
      + countBool (HS.Sig15.b3 sig)
      + countBool (HS.Sig15.b5 sig)
      + countBool (HS.Sig15.b7 sig)
      + countBool (HS.Sig15.b11 sig))
    (countBool (HS.Sig15.b13 sig)
      + countBool (HS.Sig15.b17 sig)
      + countBool (HS.Sig15.b19 sig)
      + countBool (HS.Sig15.b23 sig)
      + countBool (HS.Sig15.b29 sig))
    (countBool (HS.Sig15.b31 sig)
      + countBool (HS.Sig15.b41 sig)
      + countBool (HS.Sig15.b47 sig)
      + countBool (HS.Sig15.b59 sig)
      + countBool (HS.Sig15.b71 sig))

shiftDeltaEigenProfile : SLEI.ShiftGeoV → PHEM.EigenProfile
shiftDeltaEigenProfile δ =
  PHEM.eigenProfile
    (countBool (isZeroℤ (timeCoord δ))
      + countBool (isZeroℤ (space1Coord δ)))
    (countBool (isZeroℤ (space2Coord δ))
      + countBool (isZeroℤ (space3Coord δ)))
    (countBool (decToBool (Int._≟_ (timeCoord δ) (space1Coord δ)))
      + countBool (decToBool (Int._≟_ (space2Coord δ) (space3Coord δ))))

shiftMotifOf : PHEM.EigenProfile → ShiftMotif
shiftMotifOf ep with PHEM.EigenProfile.hub ep NatP.≟ zero
... | no _ = hubMotif
... | yes _ with PHEM.EigenProfile.spoke ep NatP.≟ zero
...   | no _ = spokeMotif
...   | yes _ with PHEM.EigenProfile.earth ep NatP.≟ zero
...     | no _ = earthMotif
...     | yes _ = balancedMotif

shiftPipeline : PHEM.PrimeHeckeEigenMotifPipelineOn SLEI.ShiftGeoV ShiftMotif
shiftPipeline =
  record
    { primeEmbedding = shiftPrimeEmbedding
    ; hecke = record
        { T = shiftHeckeAction
        ; compat = shiftCompat
        }
    ; ΔState = SLEI.ShiftGeoV
    ; Δ = λ x y → y
    ; signatureEigenProfile = shiftSignatureEigenProfile
    ; deltaEigenProfile = shiftDeltaEigenProfile
    ; motifOf = shiftMotifOf
    ; resonance =
        λ δ₁ δ₂ →
          (PHEM.EigenProfile.earth (shiftDeltaEigenProfile δ₁)
            ≡
           PHEM.EigenProfile.earth (shiftDeltaEigenProfile δ₂))
          ×
          (PHEM.EigenProfile.spoke (shiftDeltaEigenProfile δ₁)
            ≡
           PHEM.EigenProfile.spoke (shiftDeltaEigenProfile δ₂))
          ×
          (PHEM.EigenProfile.hub (shiftDeltaEigenProfile δ₁)
            ≡
           PHEM.EigenProfile.hub (shiftDeltaEigenProfile δ₂))
    }

shiftCoarse : EC.Contract.State ShiftC → EC.Contract.State ShiftC
shiftCoarse =
  LFS.embedCoarse (suc zero) (suc (suc (suc zero)))
    ∘
  LFS.coarseProj (suc zero) (suc (suc (suc zero)))
  where
  _∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
  (f ∘ g) x = f (g x)

ShiftConeCompatible : EC.Contract.State ShiftC → Set
ShiftConeCompatible x =
  CMC.Cone.InCone
    SLEI.shiftCone
    (canonicalShiftHeckeState (shiftCoarse x))

shiftRGSurface :
  RGOI.RGObservableSurface ShiftC SLEI.ShiftGeoV ShiftBasin ShiftMotif
shiftRGSurface =
  record
    { toHeckeState = canonicalShiftHeckeState
    ; classifyBasin = λ _ → canonicalBasin
    ; pipeline = shiftPipeline
    ; coneWitness = ShiftConeCompatible
    }

shiftRGConeWitness : EC.Contract.State ShiftC → Set
shiftRGConeWitness = ShiftConeCompatible

shiftRGAdmissible : EC.Contract.State ShiftC → Set
shiftRGAdmissible x = ShiftCanonicalInBasin x × ShiftConeCompatible x

projShiftTail-id :
  ∀ {k : Nat} (t : Data.Vec.Vec Trit k) →
  TCP.projTail (TCP.shiftTail t) ≡ TCP.shiftTail t
projShiftTail-id t = TCP.tailStep≡shiftTail t

shiftCoarseStep-commute :
  ∀ x →
  shiftCoarse (EC.Contract.step ShiftC x)
    ≡
  EC.Contract.step ShiftC (shiftCoarse x)
shiftCoarseStep-commute x =
  trans
    (cong
      (LFS.embedCoarse (suc zero) (suc (suc (suc zero))))
      (LFS.coarse-invariant-T (suc zero) (suc (suc (suc zero))) x))
    (sym
      (LFS.invariantCoarseSubspace
        (suc zero)
        (suc (suc (suc zero)))
        (LFS.coarseProj (suc zero) (suc (suc (suc zero))) x)))

shiftCoarse-idem :
  ∀ x →
  shiftCoarse (shiftCoarse x) ≡ shiftCoarse x
shiftCoarse-idem x
  rewrite
    TCP.split-++
      (suc zero)
      (suc (suc (suc zero)))
      (LFS.coarseProj (suc zero) (suc (suc (suc zero))) x)
      (replicate (suc (suc (suc zero))) zer)
  = refl

shiftCoarseFixed :
  ∀ x →
  EC.Contract.step ShiftC (shiftCoarse x) ≡ shiftCoarse x
shiftCoarseFixed x =
  LFS.invariantCoarseSubspace
    (suc zero)
    (suc (suc (suc zero)))
    (LFS.coarseProj (suc zero) (suc (suc (suc zero))) x)

shiftCoarseAlt : EC.Contract.State ShiftC → EC.Contract.State ShiftC
shiftCoarseAlt x = EC.Contract.step ShiftC (shiftCoarse x)

shiftCoarseAlt≡shiftCoarse :
  ∀ x →
  shiftCoarseAlt x ≡ shiftCoarse (EC.Contract.step ShiftC x)
shiftCoarseAlt≡shiftCoarse x =
  sym (shiftCoarseStep-commute x)

shiftCoarseAltStep-commute :
  ∀ x →
  shiftCoarseAlt (EC.Contract.step ShiftC x)
    ≡
  EC.Contract.step ShiftC (shiftCoarseAlt x)
shiftCoarseAltStep-commute x
  rewrite shiftCoarseStep-commute x
        | shiftCoarseFixed (EC.Contract.step ShiftC x)
        | shiftCoarseFixed x
  = refl

shiftConeTransportStep :
  ∀ x →
  shiftRGConeWitness x →
  shiftRGConeWitness (EC.Contract.step ShiftC x)
shiftConeTransportStep x w
  rewrite shiftCoarseStep-commute x
        | shiftCoarseFixed x
  = w

shiftConeTransportCoarse :
  ∀ x →
  shiftRGConeWitness x →
  shiftRGConeWitness (shiftCoarse x)
shiftConeTransportCoarse x w
  rewrite shiftCoarse-idem x
  = w

shiftConeTransportCoarseAlt :
  ∀ x →
  shiftRGConeWitness x →
  ShiftConeCompatible (shiftCoarseAlt x)
shiftConeTransportCoarseAlt x w
  = shiftConeTransportStep (shiftCoarse x) (shiftConeTransportCoarse x w)

shiftBasinTransportStep :
  ∀ x →
  ShiftCanonicalInBasin x →
  ShiftCanonicalInBasin (EC.Contract.step ShiftC x)
shiftBasinTransportStep x =
  EC.Contract.ExecutionAdmissible.basin-preserved
    (SLEI.shiftExecutionAdmissible {m = ShiftM} {k = ShiftK})
    x

shiftBasinTransportCoarse :
  ∀ x →
  ShiftCanonicalInBasin x →
  ShiftCanonicalInBasin (shiftCoarse x)
shiftBasinTransportCoarse x h
  rewrite
    TCP.split-++
      ShiftM
      ShiftK
      (LFS.coarseProj ShiftM ShiftK x)
      (replicate ShiftK zer)
  = h

shiftObservableQuotient :
  ∀ (o₁ o₂ : RGOI.RGObservable ShiftBasin ShiftMotif) →
  RGOI.RGObservable.mdlLevel o₁ ≡ RGOI.RGObservable.mdlLevel o₂ →
  RGOI.RGObservable.basinLabel o₁ ≡ RGOI.RGObservable.basinLabel o₂ →
  RGOI.RGObservable.heckeSignature o₁ ≡ RGOI.RGObservable.heckeSignature o₂ →
  RGOI.RGObservable.eigenSummary o₁ ≡ RGOI.RGObservable.eigenSummary o₂ →
  RGOI.RGObservable.motifClass o₁ ≡ RGOI.RGObservable.motifClass o₂ →
  (RGOI.RGObservable.mdlLevel o₁ ≡ RGOI.RGObservable.mdlLevel o₂)
  × (RGOI.RGObservable.basinLabel o₁ ≡ RGOI.RGObservable.basinLabel o₂)
  × (RGOI.RGObservable.heckeSignature o₁ ≡ RGOI.RGObservable.heckeSignature o₂)
  × (RGOI.RGObservable.eigenSummary o₁ ≡ RGOI.RGObservable.eigenSummary o₂)
  × (RGOI.RGObservable.motifClass o₁ ≡ RGOI.RGObservable.motifClass o₂)
shiftObservableQuotient _ _ mdlEq basinEq sigEq eigEq motifEq
  = mdlEq , basinEq , sigEq , eigEq , motifEq

shiftConePreservedLeft :
  ∀ x →
  shiftRGAdmissible x →
  RGOI.RGObservableSurface.coneWitness shiftRGSurface x →
  RGOI.RGObservableSurface.coneWitness shiftRGSurface (shiftCoarse (EC.Contract.step ShiftC x))
shiftConePreservedLeft x _ w = shiftConeTransportCoarse (EC.Contract.step ShiftC x) (shiftConeTransportStep x w)

shiftConePreservedRight :
  ∀ x →
  shiftRGAdmissible x →
  RGOI.RGObservableSurface.coneWitness shiftRGSurface x →
  RGOI.RGObservableSurface.coneWitness shiftRGSurface (EC.Contract.step ShiftC (shiftCoarse x))
shiftConePreservedRight x _ w = shiftConeTransportStep (shiftCoarse x) (shiftConeTransportCoarse x w)

shiftConePreservedLeftAlt :
  ∀ x →
  shiftRGAdmissible x →
  RGOI.RGObservableSurface.coneWitness shiftRGSurface x →
  RGOI.RGObservableSurface.coneWitness shiftRGSurface (shiftCoarseAlt (EC.Contract.step ShiftC x))
shiftConePreservedLeftAlt x _ w =
  shiftConeTransportCoarseAlt (EC.Contract.step ShiftC x) (shiftConeTransportStep x w)

shiftMDLSchedule :
  ∀ x →
  shiftRGAdmissible x →
  RGOI.RGObservable.mdlLevel
    (RGOI.RGObservableSurface.observe shiftRGSurface
      (shiftCoarse (EC.Contract.step ShiftC x)))
    ≡
  RGOI.RGObservable.mdlLevel
    (RGOI.RGObservableSurface.observe shiftRGSurface
      (EC.Contract.step ShiftC (shiftCoarse x)))
shiftMDLSchedule x _ =
  cong
    (λ s → RGOI.RGObservable.mdlLevel (RGOI.RGObservableSurface.observe shiftRGSurface s))
    (shiftCoarseStep-commute x)

shiftBasinSchedule :
  ∀ x →
  shiftRGAdmissible x →
  RGOI.RGObservable.basinLabel
    (RGOI.RGObservableSurface.observe shiftRGSurface
      (shiftCoarse (EC.Contract.step ShiftC x)))
    ≡
  RGOI.RGObservable.basinLabel
    (RGOI.RGObservableSurface.observe shiftRGSurface
      (EC.Contract.step ShiftC (shiftCoarse x)))
shiftBasinSchedule x _ =
  cong
    (λ s → RGOI.RGObservable.basinLabel (RGOI.RGObservableSurface.observe shiftRGSurface s))
    (shiftCoarseStep-commute x)

shiftSignatureSchedule :
  ∀ x →
  shiftRGAdmissible x →
  RGOI.RGObservable.heckeSignature
    (RGOI.RGObservableSurface.observe shiftRGSurface
      (shiftCoarse (EC.Contract.step ShiftC x)))
    ≡
  RGOI.RGObservable.heckeSignature
    (RGOI.RGObservableSurface.observe shiftRGSurface
      (EC.Contract.step ShiftC (shiftCoarse x)))
shiftSignatureSchedule x _ =
  cong
    (λ s → RGOI.RGObservable.heckeSignature (RGOI.RGObservableSurface.observe shiftRGSurface s))
    (shiftCoarseStep-commute x)

shiftEigenSchedule :
  ∀ x →
  shiftRGAdmissible x →
  RGOI.RGObservable.eigenSummary
    (RGOI.RGObservableSurface.observe shiftRGSurface
      (shiftCoarse (EC.Contract.step ShiftC x)))
    ≡
  RGOI.RGObservable.eigenSummary
    (RGOI.RGObservableSurface.observe shiftRGSurface
      (EC.Contract.step ShiftC (shiftCoarse x)))
shiftEigenSchedule x _ =
  cong
    (λ s → RGOI.RGObservable.eigenSummary (RGOI.RGObservableSurface.observe shiftRGSurface s))
    (shiftCoarseStep-commute x)

shiftMotifSchedule :
  ∀ x →
  shiftRGAdmissible x →
  RGOI.RGObservable.motifClass
    (RGOI.RGObservableSurface.observe shiftRGSurface
      (shiftCoarse (EC.Contract.step ShiftC x)))
    ≡
  RGOI.RGObservable.motifClass
    (RGOI.RGObservableSurface.observe shiftRGSurface
      (EC.Contract.step ShiftC (shiftCoarse x)))
shiftMotifSchedule x _ =
  cong
    (λ s → RGOI.RGObservable.motifClass (RGOI.RGObservableSurface.observe shiftRGSurface s))
    (shiftCoarseStep-commute x)

shiftRGWitnessPackage :
  RGOI.RGCoarseWitnessPackage ShiftC shiftRGSurface
shiftRGWitnessPackage =
  record
    { evolve = EC.Contract.step ShiftC
    ; coarse = shiftCoarse
    ; admissible = shiftRGAdmissible
    ; execution = SLEI.shiftExecutionAdmissible {m = suc zero} {k = suc (suc (suc zero))}
    ; admissible⇒basin = λ _ a → Data.Product.proj₁ a
    ; admissible-evolve = λ x (b , w) → shiftBasinTransportStep x b , shiftConeTransportStep x w
    ; admissible-coarse = λ x (b , w) → shiftBasinTransportCoarse x b , shiftConeTransportCoarse x w
    ; mdl-schedule = shiftMDLSchedule
    ; basin-schedule = shiftBasinSchedule
    ; signature-schedule = shiftSignatureSchedule
    ; eigen-schedule = shiftEigenSchedule
    ; motif-schedule = shiftMotifSchedule
    ; cone-preserved-left = shiftConePreservedLeft
    ; cone-preserved-right = shiftConePreservedRight
    ; Observable≈ =
        λ o₁ o₂ →
          (RGOI.RGObservable.mdlLevel o₁ ≡ RGOI.RGObservable.mdlLevel o₂)
          × (RGOI.RGObservable.basinLabel o₁ ≡ RGOI.RGObservable.basinLabel o₂)
          × (RGOI.RGObservable.heckeSignature o₁ ≡ RGOI.RGObservable.heckeSignature o₂)
          × (RGOI.RGObservable.eigenSummary o₁ ≡ RGOI.RGObservable.eigenSummary o₂)
          × (RGOI.RGObservable.motifClass o₁ ≡ RGOI.RGObservable.motifClass o₂)
    ; quotient-from-components = shiftObservableQuotient
    }

shiftObservableRGInvariance :
  RGOI.ObservableRGInvariance
    (EC.Contract.State ShiftC)
    (RGOI.RGObservable ShiftBasin ShiftMotif)
shiftObservableRGInvariance =
  RGOI.fromRGCoarseWitnessPackage
    ShiftC
    shiftRGSurface
    shiftRGWitnessPackage

shiftMDLScheduleAlt :
  ∀ x →
  shiftRGAdmissible x →
  RGOI.RGObservable.mdlLevel
    (RGOI.RGObservableSurface.observe shiftRGSurface
      (shiftCoarseAlt (EC.Contract.step ShiftC x)))
    ≡
  RGOI.RGObservable.mdlLevel
    (RGOI.RGObservableSurface.observe shiftRGSurface
      (EC.Contract.step ShiftC (shiftCoarseAlt x)))
shiftMDLScheduleAlt x _ =
  cong
    (λ s → RGOI.RGObservable.mdlLevel (RGOI.RGObservableSurface.observe shiftRGSurface s))
    (shiftCoarseAltStep-commute x)

shiftBasinScheduleAlt :
  ∀ x →
  shiftRGAdmissible x →
  RGOI.RGObservable.basinLabel
    (RGOI.RGObservableSurface.observe shiftRGSurface
      (shiftCoarseAlt (EC.Contract.step ShiftC x)))
    ≡
  RGOI.RGObservable.basinLabel
    (RGOI.RGObservableSurface.observe shiftRGSurface
      (EC.Contract.step ShiftC (shiftCoarseAlt x)))
shiftBasinScheduleAlt x _ =
  cong
    (λ s → RGOI.RGObservable.basinLabel (RGOI.RGObservableSurface.observe shiftRGSurface s))
    (shiftCoarseAltStep-commute x)

shiftSignatureScheduleAlt :
  ∀ x →
  shiftRGAdmissible x →
  RGOI.RGObservable.heckeSignature
    (RGOI.RGObservableSurface.observe shiftRGSurface
      (shiftCoarseAlt (EC.Contract.step ShiftC x)))
    ≡
  RGOI.RGObservable.heckeSignature
    (RGOI.RGObservableSurface.observe shiftRGSurface
      (EC.Contract.step ShiftC (shiftCoarseAlt x)))
shiftSignatureScheduleAlt x _ =
  cong
    (λ s → RGOI.RGObservable.heckeSignature (RGOI.RGObservableSurface.observe shiftRGSurface s))
    (shiftCoarseAltStep-commute x)

shiftEigenScheduleAlt :
  ∀ x →
  shiftRGAdmissible x →
  RGOI.RGObservable.eigenSummary
    (RGOI.RGObservableSurface.observe shiftRGSurface
      (shiftCoarseAlt (EC.Contract.step ShiftC x)))
    ≡
  RGOI.RGObservable.eigenSummary
    (RGOI.RGObservableSurface.observe shiftRGSurface
      (EC.Contract.step ShiftC (shiftCoarseAlt x)))
shiftEigenScheduleAlt x _ =
  cong
    (λ s → RGOI.RGObservable.eigenSummary (RGOI.RGObservableSurface.observe shiftRGSurface s))
    (shiftCoarseAltStep-commute x)

shiftMotifScheduleAlt :
  ∀ x →
  shiftRGAdmissible x →
  RGOI.RGObservable.motifClass
    (RGOI.RGObservableSurface.observe shiftRGSurface
      (shiftCoarseAlt (EC.Contract.step ShiftC x)))
    ≡
  RGOI.RGObservable.motifClass
    (RGOI.RGObservableSurface.observe shiftRGSurface
      (EC.Contract.step ShiftC (shiftCoarseAlt x)))
shiftMotifScheduleAlt x _ =
  cong
    (λ s → RGOI.RGObservable.motifClass (RGOI.RGObservableSurface.observe shiftRGSurface s))
    (shiftCoarseAltStep-commute x)

shiftRGWitnessPackageAlt :
  RGOI.RGCoarseWitnessPackage ShiftC shiftRGSurface
shiftRGWitnessPackageAlt =
  record
    { evolve = EC.Contract.step ShiftC
    ; coarse = shiftCoarseAlt
    ; admissible = shiftRGAdmissible
    ; execution = SLEI.shiftExecutionAdmissible {m = suc zero} {k = suc (suc (suc zero))}
    ; admissible⇒basin = λ _ a → Data.Product.proj₁ a
    ; admissible-evolve = λ x (b , w) → shiftBasinTransportStep x b , shiftConeTransportStep x w
    ; admissible-coarse = λ x (b , w) → shiftBasinTransportStep (shiftCoarse x) (shiftBasinTransportCoarse x b) , shiftConeTransportCoarseAlt x w
    ; mdl-schedule = shiftMDLScheduleAlt
    ; basin-schedule = shiftBasinScheduleAlt
    ; signature-schedule = shiftSignatureScheduleAlt
    ; eigen-schedule = shiftEigenScheduleAlt
    ; motif-schedule = shiftMotifScheduleAlt
    ; cone-preserved-left = shiftConePreservedLeftAlt
    ; cone-preserved-right =
        λ x _ w →
          shiftConeTransportStep (shiftCoarseAlt x) (shiftConeTransportCoarseAlt x w)
    ; Observable≈ =
        λ o₁ o₂ →
          (RGOI.RGObservable.mdlLevel o₁ ≡ RGOI.RGObservable.mdlLevel o₂)
          × (RGOI.RGObservable.basinLabel o₁ ≡ RGOI.RGObservable.basinLabel o₂)
          × (RGOI.RGObservable.heckeSignature o₁ ≡ RGOI.RGObservable.heckeSignature o₂)
          × (RGOI.RGObservable.eigenSummary o₁ ≡ RGOI.RGObservable.eigenSummary o₂)
          × (RGOI.RGObservable.motifClass o₁ ≡ RGOI.RGObservable.motifClass o₂)
    ; quotient-from-components = shiftObservableQuotient
    }

shiftObservableUniversality :
  ∀ x →
  shiftRGAdmissible x →
  RGOI.RGCoarseWitnessPackage.Observable≈
    shiftRGWitnessPackage
    (RGOI.RGObservableSurface.observe shiftRGSurface
      (shiftCoarse (EC.Contract.step ShiftC x)))
    (RGOI.RGObservableSurface.observe shiftRGSurface
      (EC.Contract.step ShiftC (shiftCoarse x)))
shiftObservableUniversality x ax =
  RGOI.RGCoarseWitnessPackage.schedule-invariant-quotient
    shiftRGWitnessPackage
    x
    ax

shiftObservableRGUniversality :
  RGOI.ObservableRGUniversality
    (EC.Contract.State ShiftC)
    (RGOI.RGObservable ShiftBasin ShiftMotif)
    (RGOI.RGCoarseWitnessPackage.Observable≈ shiftRGWitnessPackage)
shiftObservableRGUniversality =
  RGOI.fromRGCoarseWitnessPackageUniversality
    ShiftC
    shiftRGSurface
    shiftRGWitnessPackage

shiftObservableSchemeUniversalityPhase :
  ∀ x →
  shiftRGAdmissible (EC.Contract.step ShiftC x) →
  RGOI.RGCoarseWitnessPackage.Observable≈
    shiftRGWitnessPackage
    (RGOI.RGObservableSurface.observe shiftRGSurface
      (RGOI.RGCoarseWitnessPackage.coarse shiftRGWitnessPackage
        (RGOI.RGCoarseWitnessPackage.evolve shiftRGWitnessPackage
          (EC.Contract.step ShiftC x))))
    (RGOI.RGObservableSurface.observe shiftRGSurface
      (RGOI.RGCoarseWitnessPackage.coarse shiftRGWitnessPackageAlt
        (RGOI.RGCoarseWitnessPackage.evolve shiftRGWitnessPackageAlt x)))
shiftObservableSchemeUniversalityPhase x ax =
  shiftObservableQuotient
    _
    _
    (cong
      (λ s → RGOI.RGObservable.mdlLevel (RGOI.RGObservableSurface.observe shiftRGSurface s))
      (sym (shiftCoarseAlt≡shiftCoarse (EC.Contract.step ShiftC x))))
    (cong
      (λ s → RGOI.RGObservable.basinLabel (RGOI.RGObservableSurface.observe shiftRGSurface s))
      (sym (shiftCoarseAlt≡shiftCoarse (EC.Contract.step ShiftC x))))
    (cong
      (λ s → RGOI.RGObservable.heckeSignature (RGOI.RGObservableSurface.observe shiftRGSurface s))
      (sym (shiftCoarseAlt≡shiftCoarse (EC.Contract.step ShiftC x))))
    (cong
      (λ s → RGOI.RGObservable.eigenSummary (RGOI.RGObservableSurface.observe shiftRGSurface s))
      (sym (shiftCoarseAlt≡shiftCoarse (EC.Contract.step ShiftC x))))
    (cong
      (λ s → RGOI.RGObservable.motifClass (RGOI.RGObservableSurface.observe shiftRGSurface s))
      (sym (shiftCoarseAlt≡shiftCoarse (EC.Contract.step ShiftC x))))

shiftObservableRGOffsetUniversality :
  RGOI.ObservableRGOffsetUniversality
    (EC.Contract.State ShiftC)
    (RGOI.RGObservable ShiftBasin ShiftMotif)
    (RGOI.RGCoarseWitnessPackage.Observable≈ shiftRGWitnessPackage)
shiftObservableRGOffsetUniversality =
  record
    { admissibleO = λ x → shiftRGAdmissible (EC.Contract.step ShiftC x)
    ; evolveA = RGOI.RGCoarseWitnessPackage.evolve shiftRGWitnessPackage
    ; coarseA = RGOI.RGCoarseWitnessPackage.coarse shiftRGWitnessPackage
    ; evolveB = RGOI.RGCoarseWitnessPackage.evolve shiftRGWitnessPackageAlt
    ; coarseB = RGOI.RGCoarseWitnessPackage.coarse shiftRGWitnessPackageAlt
    ; observeO = RGOI.RGObservableSurface.observe shiftRGSurface
    ; offset = EC.Contract.step ShiftC
    ; universalityOffset = shiftObservableSchemeUniversalityPhase
    }

shiftProjectionDeltaCompatibility :
  RGOI.ProjectionDeltaCompatibility
    (EC.Contract.State ShiftC)
    (RGOI.RGObservable ShiftBasin ShiftMotif)
    (RGOI.RGCoarseWitnessPackage.Observable≈ shiftRGWitnessPackage)
shiftProjectionDeltaCompatibility =
  record
    { admissibleΔ = shiftRGAdmissible
    ; projectA = λ x → shiftCoarse (EC.Contract.step ShiftC x)
    ; projectB = shiftCoarseAlt
    ; observeΔ = RGOI.RGObservableSurface.observe shiftRGSurface
    ; coneΔ = ShiftConeCompatible
    ; cone-projectA = shiftConePreservedLeft
    ; cone-projectB = λ x _ w → shiftConeTransportCoarseAlt x w
    ; universalityΔ =
        λ x _ →
          shiftObservableQuotient
            _
            _
            (cong
              (λ s → RGOI.RGObservable.mdlLevel
                (RGOI.RGObservableSurface.observe shiftRGSurface s))
              (sym (shiftCoarseAlt≡shiftCoarse x)))
            (cong
              (λ s → RGOI.RGObservable.basinLabel
                (RGOI.RGObservableSurface.observe shiftRGSurface s))
              (sym (shiftCoarseAlt≡shiftCoarse x)))
            (cong
              (λ s → RGOI.RGObservable.heckeSignature
                (RGOI.RGObservableSurface.observe shiftRGSurface s))
              (sym (shiftCoarseAlt≡shiftCoarse x)))
            (cong
              (λ s → RGOI.RGObservable.eigenSummary
                (RGOI.RGObservableSurface.observe shiftRGSurface s))
              (sym (shiftCoarseAlt≡shiftCoarse x)))
            (cong
              (λ s → RGOI.RGObservable.motifClass
                (RGOI.RGObservableSurface.observe shiftRGSurface s))
              (sym (shiftCoarseAlt≡shiftCoarse x)))
    }
