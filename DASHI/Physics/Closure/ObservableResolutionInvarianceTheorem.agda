module DASHI.Physics.Closure.ObservableResolutionInvarianceTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.Closure.ClosureObservableWitness as COW
open import DASHI.Physics.Closure.PhysicsClosureCoreWitness as PCCW
open import DASHI.Physics.Closure.PhysicsClosureConstructorTheorem as PCCT
open import DASHI.Physics.Closure.PhysicsClosureFull as PCF
open import DASHI.Physics.Closure.PhysicsClosureFullInstance as PCFI
open import DASHI.Physics.Closure.RootSystemB4ObservableComparison as B4OC
open import DASHI.Physics.Closure.RootSystemB4ObservableResolutionMap as B4ORM
  hiding (_≡ω_; reflω)
open import DASHI.Physics.Closure.RootSystemB4OrbitQuotientTheorem as B4OQT
open import DASHI.Physics.Closure.Validation.RealizationProfileRigidity as RPR
open import DASHI.Physics.Closure.Validation.RootSystemB4PromotionBridge as B4PB
open import DASHI.Physics.Signature31Canonical as S31C

record ObservableAdmissibility
  (obs : COW.ClosureObservableWitness) : Setω where
  field
    admissibleRealization : RPR.AdmissibleComparisonRealization
    orientationTagMatchesObservable :
      RPR.AdmissibleComparisonRealization.orientationTag admissibleRealization
      ≡ COW.ClosureObservableWitness.observedOrientationTag obs
    shell1MatchesObservable :
      RPR.AdmissibleComparisonRealization.shell1Profile admissibleRealization
      ≡ COW.ClosureObservableWitness.observedShell1 obs
    shell2MatchesObservable :
      RPR.AdmissibleComparisonRealization.shell2Profile admissibleRealization
      ≡ COW.ClosureObservableWitness.observedShell2 obs
    signatureMatchesObservable :
      RPR.AdmissibleComparisonRealization.signature admissibleRealization
      ≡ COW.ClosureObservableWitness.provedSignature obs

admissibilityFromObservable :
  (obs : COW.ClosureObservableWitness) →
  ObservableAdmissibility obs
admissibilityFromObservable obs =
  record
    { admissibleRealization = B4ORM.admissibleFromObservable obs
    ; orientationTagMatchesObservable = refl
    ; shell1MatchesObservable = refl
    ; shell2MatchesObservable = refl
    ; signatureMatchesObservable = refl
    }

record ShiftClosureEvidence : Setω where
  field
    coreWitness : PCCW.PhysicsClosureCoreWitness
    usesShiftProvider :
      PCCW.PhysicsClosureCoreWitness.signatureCoreProvider coreWitness
      ≡ω
      S31C.shiftCoreProvider
    constructorTheorem : PCCT.PhysicsClosureConstructorTheorem
    constructorTargetsWitness :
      PCCT.PhysicsClosureConstructorTheorem.closureCoreWitness constructorTheorem
      ≡ω
      coreWitness
    observables : COW.ClosureObservableWitness
    witnessObservables :
      PCCW.PhysicsClosureCoreWitness.observables coreWitness ≡ω observables
    admissibility : ObservableAdmissibility observables
    signatureAgreement :
      S31C.signature31FromProvider
        (PCCW.PhysicsClosureCoreWitness.signatureCoreProvider coreWitness)
      ≡
      COW.ClosureObservableWitness.provedSignature observables

  fullClosure : PCF.PhysicsClosureFull
  fullClosure =
    PCF.physicsClosureFullFromCoreWitness coreWitness

record B4ClosureEvidence : Setω where
  field
    coreWitness : PCCW.PhysicsClosureCoreWitness
    usesB4Provider :
      PCCW.PhysicsClosureCoreWitness.signatureCoreProvider coreWitness
      ≡ω
      S31C.b4CoreProvider
    constructorTheorem : PCCT.PhysicsClosureConstructorTheorem
    constructorTargetsWitness :
      PCCT.PhysicsClosureConstructorTheorem.closureCoreWitness constructorTheorem
      ≡ω
      coreWitness
    observables : COW.ClosureObservableWitness
    witnessObservables :
      PCCW.PhysicsClosureCoreWitness.observables coreWitness ≡ω observables
    admissibility : ObservableAdmissibility observables
    observableComparison : B4OC.B4ObservableComparison
    promotionReady :
      B4PB.B4PromotionBridge.promotionStatus B4PB.bridge
      ≡ B4PB.admissiblePromotionReady
    signatureAgreement :
      S31C.signature31FromProvider
        (PCCW.PhysicsClosureCoreWitness.signatureCoreProvider coreWitness)
      ≡
      COW.ClosureObservableWitness.provedSignature observables

  fullClosure : PCF.PhysicsClosureFull
  fullClosure =
    PCF.physicsClosureFullFromCoreWitness coreWitness

record B4PromotionEvidence : Setω where
  field
    promotionReady :
      B4PB.B4PromotionBridge.promotionStatus B4PB.bridge
      ≡ B4PB.admissiblePromotionReady

canonicalB4PromotionEvidence : B4PromotionEvidence
canonicalB4PromotionEvidence =
  record
    { promotionReady = refl
    }

mkShiftClosureEvidence :
  (obs : COW.ClosureObservableWitness) →
  S31C.signature31FromProvider S31C.shiftCoreProvider
    ≡ COW.ClosureObservableWitness.provedSignature obs →
  ObservableAdmissibility obs →
  ShiftClosureEvidence
mkShiftClosureEvidence obs signatureAgreement admissibility =
  let witness = PCFI.coreWitnessWithShiftObservables obs signatureAgreement
  in
  record
    { coreWitness = witness
    ; usesShiftProvider = reflω
    ; constructorTheorem = PCCT.physicsClosureConstructorTheorem witness
    ; constructorTargetsWitness = reflω
    ; observables = obs
    ; witnessObservables = reflω
    ; admissibility = admissibility
    ; signatureAgreement = signatureAgreement
    }

mkB4ClosureEvidence :
  (obs : COW.ClosureObservableWitness) →
  S31C.signature31FromProvider S31C.b4CoreProvider
    ≡ COW.ClosureObservableWitness.provedSignature obs →
  ObservableAdmissibility obs →
  B4OC.B4ObservableComparison →
  B4PromotionEvidence →
  B4ClosureEvidence
mkB4ClosureEvidence obs signatureAgreement admissibility comparison promotion =
  let witness = PCFI.coreWitnessWithB4Observables obs signatureAgreement
  in
  record
    { coreWitness = witness
    ; usesB4Provider = reflω
    ; constructorTheorem = PCCT.physicsClosureConstructorTheorem witness
    ; constructorTargetsWitness = reflω
    ; observables = obs
    ; witnessObservables = reflω
    ; admissibility = admissibility
    ; observableComparison = comparison
    ; promotionReady = B4PromotionEvidence.promotionReady promotion
    ; signatureAgreement = signatureAgreement
    }

canonicalShiftClosureEvidence : ShiftClosureEvidence
canonicalShiftClosureEvidence =
  let
    obs =
      PCCW.PhysicsClosureCoreWitness.observables PCFI.physicsClosureCoreWitness
    signatureAgreement =
      PCCW.PhysicsClosureCoreWitness.observableSignatureAgreement
        PCFI.physicsClosureCoreWitness
  in
  mkShiftClosureEvidence
    obs
    signatureAgreement
    (admissibilityFromObservable obs)

canonicalB4ClosureEvidence : B4ClosureEvidence
canonicalB4ClosureEvidence =
  let
    obs =
      PCCW.PhysicsClosureCoreWitness.observables PCFI.b4PhysicsClosureCoreWitness
    signatureAgreement =
      PCCW.PhysicsClosureCoreWitness.observableSignatureAgreement
        PCFI.b4PhysicsClosureCoreWitness
  in
  mkB4ClosureEvidence
    obs
    signatureAgreement
    (admissibilityFromObservable obs)
    B4OC.canonicalB4ObservableComparison
    canonicalB4PromotionEvidence

descendClosureEvidenceWith :
  (quotientTheorem : B4OQT.RootSystemB4OrbitQuotientTheorem) →
  B4PromotionEvidence →
  ((shiftEvidence : ShiftClosureEvidence) →
    S31C.signature31FromProvider S31C.b4CoreProvider
      ≡
      COW.ClosureObservableWitness.provedSignature
        (B4ORM.ObservableResolutionMap.onObservables
          (B4OQT.RootSystemB4OrbitQuotientTheorem.resolutionMap
            quotientTheorem)
          (ShiftClosureEvidence.observables shiftEvidence))) →
  ShiftClosureEvidence →
  B4ClosureEvidence
descendClosureEvidenceWith
  quotientTheorem
  promotionEvidence
  signatureAgreement
  shiftEvidence =
  let
    projectedObs =
      B4ORM.ObservableResolutionMap.onObservables
        (B4OQT.RootSystemB4OrbitQuotientTheorem.resolutionMap quotientTheorem)
        (ShiftClosureEvidence.observables shiftEvidence)
    comparison =
      B4OQT.RootSystemB4OrbitQuotientTheorem.observableComparison
        quotientTheorem
  in
  mkB4ClosureEvidence
    projectedObs
    (signatureAgreement shiftEvidence)
    (admissibilityFromObservable projectedObs)
    comparison
    promotionEvidence

descendClosureEvidence :
  ShiftClosureEvidence → B4ClosureEvidence
descendClosureEvidence =
  descendClosureEvidenceWith
    B4OQT.canonicalRootSystemB4OrbitQuotientTheorem
    canonicalB4PromotionEvidence
    (λ _ → refl)

reflectClosureEvidence :
  (b4 : B4ClosureEvidence) →
  (shiftObs : COW.ClosureObservableWitness) →
  S31C.signature31FromProvider S31C.shiftCoreProvider
    ≡ COW.ClosureObservableWitness.provedSignature shiftObs →
  B4ORM.B4ObservableRefinement
    shiftObs
    (B4ClosureEvidence.observables b4)
  →
  ShiftClosureEvidence
reflectClosureEvidence b4 shiftObs signatureAgreement refinement =
  mkShiftClosureEvidence
    shiftObs
    signatureAgreement
    (record
      { admissibleRealization =
          B4ORM.B4ObservableRefinement.sourceAdmissible refinement
      ; orientationTagMatchesObservable =
          B4ORM.B4ObservableRefinement.sourceOrientationMatches refinement
      ; shell1MatchesObservable =
          B4ORM.B4ObservableRefinement.sourceShell1Matches refinement
      ; shell2MatchesObservable =
          B4ORM.B4ObservableRefinement.sourceShell2Matches refinement
      ; signatureMatchesObservable =
          B4ORM.B4ObservableRefinement.sourceSignatureMatches refinement
      })

record ClosureInvariantUnderObservableResolution : Setω where
  field
    descent :
      ShiftClosureEvidence → B4ClosureEvidence
    reflection :
      (b4 : B4ClosureEvidence) →
      (shiftObs : COW.ClosureObservableWitness) →
      S31C.signature31FromProvider S31C.shiftCoreProvider
        ≡ COW.ClosureObservableWitness.provedSignature shiftObs →
      B4ORM.B4ObservableRefinement
        shiftObs
        (B4ClosureEvidence.observables b4)
      →
      ShiftClosureEvidence
    descentOfCanonicalShift :
      descent canonicalShiftClosureEvidence ≡ω canonicalB4ClosureEvidence
    reflectionOfCanonicalB4 :
      reflection canonicalB4ClosureEvidence
        B4ORM.canonicalLiftedShiftObservable
        refl
        B4ORM.canonicalB4LiftRefinement
      ≡ω
      mkShiftClosureEvidence
        B4ORM.canonicalLiftedShiftObservable
        refl
        (record
          { admissibleRealization =
              B4ORM.B4ObservableRefinement.sourceAdmissible
                B4ORM.canonicalB4LiftRefinement
          ; orientationTagMatchesObservable =
              B4ORM.B4ObservableRefinement.sourceOrientationMatches
                B4ORM.canonicalB4LiftRefinement
          ; shell1MatchesObservable =
              B4ORM.B4ObservableRefinement.sourceShell1Matches
                B4ORM.canonicalB4LiftRefinement
          ; shell2MatchesObservable =
              B4ORM.B4ObservableRefinement.sourceShell2Matches
                B4ORM.canonicalB4LiftRefinement
          ; signatureMatchesObservable =
              B4ORM.B4ObservableRefinement.sourceSignatureMatches
                B4ORM.canonicalB4LiftRefinement
          })

canonicalClosureInvariantUnderObservableResolution :
  ClosureInvariantUnderObservableResolution
canonicalClosureInvariantUnderObservableResolution =
  record
    { descent = descendClosureEvidence
    ; reflection = reflectClosureEvidence
    ; descentOfCanonicalShift = reflω
    ; reflectionOfCanonicalB4 = reflω
    }

record ObservableResolutionInvarianceTheorem : Setω where
  field
    resolutionMap : B4ORM.ObservableResolutionMap
    orbitQuotientTheorem : B4OQT.RootSystemB4OrbitQuotientTheorem
    promotionEvidence : B4PromotionEvidence
    canonicalShiftEvidence : ShiftClosureEvidence
    canonicalB4Evidence : B4ClosureEvidence
    canonicalRefinement :
      B4ORM.B4ObservableRefinement
        (ShiftClosureEvidence.observables canonicalShiftEvidence)
        (B4ClosureEvidence.observables canonicalB4Evidence)
    closureDescends :
      ShiftClosureEvidence → B4ClosureEvidence
    closureReflects :
      (b4 : B4ClosureEvidence) →
      (shiftObs : COW.ClosureObservableWitness) →
      S31C.signature31FromProvider S31C.shiftCoreProvider
        ≡ COW.ClosureObservableWitness.provedSignature shiftObs →
      B4ORM.B4ObservableRefinement
        shiftObs
        (B4ClosureEvidence.observables b4)
      →
      ShiftClosureEvidence
    closureInvariant :
      ClosureInvariantUnderObservableResolution

canonicalObservableResolutionInvarianceTheorem :
  ObservableResolutionInvarianceTheorem
canonicalObservableResolutionInvarianceTheorem =
  record
    { resolutionMap = B4ORM.canonicalObservableResolutionMap
    ; orbitQuotientTheorem = B4OQT.canonicalRootSystemB4OrbitQuotientTheorem
    ; promotionEvidence = canonicalB4PromotionEvidence
    ; canonicalShiftEvidence = canonicalShiftClosureEvidence
    ; canonicalB4Evidence = canonicalB4ClosureEvidence
    ; canonicalRefinement = B4ORM.canonicalB4ObservableRefinement
    ; closureDescends =
        descendClosureEvidenceWith
          B4OQT.canonicalRootSystemB4OrbitQuotientTheorem
          canonicalB4PromotionEvidence
          (λ _ → refl)
    ; closureReflects = reflectClosureEvidence
    ; closureInvariant =
        canonicalClosureInvariantUnderObservableResolution
    }

physicsClosureInvariantUnderObservableResolution :
  ObservableResolutionInvarianceTheorem
physicsClosureInvariantUnderObservableResolution =
  canonicalObservableResolutionInvarianceTheorem
