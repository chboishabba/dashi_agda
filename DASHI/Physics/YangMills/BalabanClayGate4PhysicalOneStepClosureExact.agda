module DASHI.Physics.YangMills.BalabanClayGate4PhysicalOneStepClosureExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCriticalMapRGCutsetCompletion as ExistingRG
import DASHI.Physics.YangMills.BalabanClayGate4CombinedSmallLargeNormAssemblyExact as Combined
import DASHI.Physics.YangMills.BalabanClayGate4CombinedRGUVIterationExact as UV

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
------------------------------------------------------------------------

record PhysicalRGState (Coupling Polymer BoundaryTerm : Set) : Set where
  constructor physicalState
  field
    runningCoupling : Coupling
    smallFieldPolymer : Polymer
    rPolymer : Polymer
    combinedPolymer : Polymer
    boundaryDensity : List BoundaryTerm

open PhysicalRGState public

record PhysicalOneStepIdentification
    {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density BoundaryTerm : Set}
    (rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density) : Set₁ where
  field
    current next : PhysicalRGState Coupling Polymer BoundaryTerm
    combinedBridge : Combined.ExistingRGCombinedLargeFieldBridge rg

    currentSmallFieldMeaning :
      smallFieldPolymer current ≡ ExistingRG.E rg
    nextSmallFieldMeaning :
      smallFieldPolymer next ≡ ExistingRG.E-next rg
    nextCombinedMeaning :
      combinedPolymer next ≡ Combined.combinedPolymer combinedBridge

    nextCouplingMeaning : runningCoupling next ≡ ExistingRG.gNext rg
    currentCouplingMeaning : runningCoupling current ≡ ExistingRG.g rg

open PhysicalOneStepIdentification public

physicalCombinedPolymerNormBound :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density BoundaryTerm}
    {rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density}
    (identification : PhysicalOneStepIdentification
      {BoundaryTerm = BoundaryTerm} rg) →
  ExistingRG.LessEqual rg
    (ExistingRG.polymerNorm rg (combinedPolymer (next identification)))
    (ExistingRG.addBound rg
      (ExistingRG.multiplyBound rg
        (ExistingRG.lambdaPolymer rg)
        (ExistingRG.polymerNorm rg (smallFieldPolymer (current identification))))
      (ExistingRG.addBound rg
        (ExistingRG.perturbativeError rg)
        (Combined.totalLargeFieldError (combinedBridge identification))))
physicalCombinedPolymerNormBound {rg = rg} identification =
  subst
    (λ oldPolymer → ExistingRG.LessEqual rg
      (ExistingRG.polymerNorm rg (combinedPolymer (next identification)))
      (ExistingRG.addBound rg
        (ExistingRG.multiplyBound rg
          (ExistingRG.lambdaPolymer rg)
          (ExistingRG.polymerNorm rg oldPolymer))
        (ExistingRG.addBound rg
          (ExistingRG.perturbativeError rg)
          (Combined.totalLargeFieldError (combinedBridge identification)))))
    (sym (currentSmallFieldMeaning identification))
    (subst
      (λ nextPolymer → ExistingRG.LessEqual rg
        (ExistingRG.polymerNorm rg nextPolymer)
        (ExistingRG.addBound rg
          (ExistingRG.multiplyBound rg
            (ExistingRG.lambdaPolymer rg)
            (ExistingRG.polymerNorm rg (ExistingRG.E rg)))
          (ExistingRG.addBound rg
            (ExistingRG.perturbativeError rg)
            (Combined.totalLargeFieldError (combinedBridge identification)))))
      (sym (nextCombinedMeaning identification))
      (Combined.combinedOneStepFromExistingSmallFieldRG
        (combinedBridge identification)))

record PhysicalOneStepClosure
    (State Bound : Set) : Set₁ where
  field
    normData : UV.CombinedOneStepPolymerNormData State Bound

    AdmissibleCoupling : State → Set
    BoundaryAdmissible : State → Set
    PolymerNormAdmissible : State → Set

    couplingDomainPreserved : ∀ state →
      AdmissibleCoupling state →
      AdmissibleCoupling (UV.next normData state)
    boundaryReinjectionAdmissible : ∀ state →
      BoundaryAdmissible state →
      BoundaryAdmissible (UV.next normData state)
    strictPolymerNormClosure : ∀ state →
      PolymerNormAdmissible state →
      PolymerNormAdmissible (UV.next normData state)

open PhysicalOneStepClosure public

physicalAdmissibility :
  ∀ {State Bound} (closure : PhysicalOneStepClosure State Bound) →
  UV.CombinedRGAdmissibility (normData closure)
physicalAdmissibility closure = record
  { UV.CombinedRGAdmissibility.AdmissibleCoupling =
      AdmissibleCoupling closure
  ; UV.CombinedRGAdmissibility.BoundaryAdmissible =
      BoundaryAdmissible closure
  ; UV.CombinedRGAdmissibility.PolymerNormAdmissible =
      PolymerNormAdmissible closure
  ; UV.CombinedRGAdmissibility.admissibleCouplingDomainPreserved =
      couplingDomainPreserved closure
  ; UV.CombinedRGAdmissibility.boundaryTermsRemainAdmissible =
      boundaryReinjectionAdmissible closure
  ; UV.CombinedRGAdmissibility.combinedPolymerNormCloses =
      strictPolymerNormClosure closure
  }

record PhysicalUVInitialData
    {State Bound : Set} (closure : PhysicalOneStepClosure State Bound) : Set₁ where
  field
    consequences : UV.UniformUVConsequences (normData closure)
    initial : State
    initialAdmissible :
      UV.AdmissibleRGState (physicalAdmissibility closure) initial
    initialStable : UV.InitialUVStability consequences initial

open PhysicalUVInitialData public

physicalGate4UVPackage :
  ∀ {State Bound} {closure : PhysicalOneStepClosure State Bound} →
  PhysicalUVInitialData closure → UV.Gate4UVCompletionPackage State Bound
physicalGate4UVPackage {closure = closure} initialData = record
  { UV.Gate4UVCompletionPackage.normData = normData closure
  ; UV.Gate4UVCompletionPackage.admissibility = physicalAdmissibility closure
  ; UV.Gate4UVCompletionPackage.consequences = consequences initialData
  ; UV.Gate4UVCompletionPackage.initial = initial initialData
  ; UV.Gate4UVCompletionPackage.initialAdmissible = initialAdmissible initialData
  ; UV.Gate4UVCompletionPackage.initialStable = initialStable initialData
  }

physicalStateCarrierLevel : ProofLevel
physicalStateCarrierLevel = machineChecked

physicalCombinedPolymerNormTransportLevel : ProofLevel
physicalCombinedPolymerNormTransportLevel = machineChecked

physicalOneStepAdmissibilityAssemblyLevel : ProofLevel
physicalOneStepAdmissibilityAssemblyLevel = machineChecked

physicalUVPackageAssemblyLevel : ProofLevel
physicalUVPackageAssemblyLevel = machineChecked

actualCombinedPolymerRepresentationInputsLevel : ProofLevel
actualCombinedPolymerRepresentationInputsLevel = conditional

physicalCouplingDomainPreservationInputsLevel : ProofLevel
physicalCouplingDomainPreservationInputsLevel = conditional

physicalBoundaryAdmissibilityInputsLevel : ProofLevel
physicalBoundaryAdmissibilityInputsLevel = conditional

physicalStrictPolymerNormClosureInputsLevel : ProofLevel
physicalStrictPolymerNormClosureInputsLevel = conditional
