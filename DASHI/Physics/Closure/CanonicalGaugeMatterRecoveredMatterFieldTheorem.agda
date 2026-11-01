module DASHI.Physics.Closure.CanonicalGaugeMatterRecoveredMatterFieldTheorem where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans; refl)

open import DASHI.Algebra.GaugeGroupContract as GGC
open import DASHI.Physics.Closure.AbstractGaugeMatterBundle as AGMB
open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CAGMI
open import DASHI.Physics.Closure.CanonicalGaugeMatterInterpretableObservableTheorem as CGMIOT
open import DASHI.Physics.Closure.CanonicalGaugeMatterStrengtheningTheorem as CGMST
import DASHI.Physics.Closure.RGObservableInvariance as RGOI
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
open import Ontology.Hecke.PrimeHeckeEigenMotifPipeline as PHEM

private
  canonicalStrengthening : CGMST.CanonicalGaugeMatterStrengtheningTheorem
  canonicalStrengthening = CGMST.canonicalGaugeMatterStrengtheningTheorem

  canonicalBundle : AGMB.AbstractGaugeMatterBundle
  canonicalBundle =
    CGMST.CanonicalGaugeMatterStrengtheningTheorem.canonicalBundle
      canonicalStrengthening

  canonicalRecovery : AGMB.GaugeMatterRecoveryTheorem canonicalBundle
  canonicalRecovery =
    CGMST.CanonicalGaugeMatterStrengtheningTheorem.gaugeMatterRecovery
      canonicalStrengthening

  canonicalTransport : AGMB.ObservableTransportWitness canonicalBundle
  canonicalTransport =
    AGMB.GaugeMatterRecoveryTheorem.transport canonicalRecovery

RecoveredMatterField : Set
RecoveredMatterField =
  SRGOI.ShiftBasin ×
  Nat ×
  SRGOI.ShiftMotif ×
  (Nat × Nat)

recoverInterpretableCharge :
  RecoveredMatterField → CGMIOT.InterpretableCharge
recoverInterpretableCharge (basin , mdl , motif , eigenShadow) =
  ( g
  , basin
  , mdl
  , motif
  , eigenShadow
  )
  where
    g = GGC.SU3×SU2×U1

projectRecoveredMatterField :
  CAGMI.CanonicalConservedCharge → RecoveredMatterField
projectRecoveredMatterField (_ , basin , mdl , motif , eigenShadow) =
  ( basin , mdl , motif , eigenShadow )

observableProjectionRecoveredMatter :
  AGMB.Observable canonicalBundle → RecoveredMatterField
observableProjectionRecoveredMatter (_ , o) =
  projectRecoveredMatterField
    ( GGC.SU3×SU2×U1
    , RGOI.RGObservable.basinLabel o
    , RGOI.RGObservable.mdlLevel o
    , RGOI.RGObservable.motifClass o
    , ( PHEM.EigenProfile.earth (RGOI.RGObservable.eigenSummary o)
      , PHEM.EigenProfile.hub (RGOI.RGObservable.eigenSummary o)
      )
    )

recoveredMatterFieldFromCarrier :
  AGMB.Carrier canonicalBundle → RecoveredMatterField
recoveredMatterFieldFromCarrier x =
  projectRecoveredMatterField (CAGMI.canonicalConservedChargeOf x)

transportedObservableRecoveredMatter :
  AGMB.ObservableTransportWitness.TargetCarrier canonicalTransport →
  RecoveredMatterField
transportedObservableRecoveredMatter x =
  observableProjectionRecoveredMatter
    (AGMB.ObservableTransportWitness.observeTarget canonicalTransport x)

recoveredMatterCarrierObservableCompatible :
  ∀ x →
  recoveredMatterFieldFromCarrier x
    ≡
  observableProjectionRecoveredMatter
    (AGMB.observableOf canonicalBundle x)
recoveredMatterCarrierObservableCompatible _ = refl

recoveredMatterTransportObservableCompatible :
  ∀ x →
  AGMB.admissible canonicalBundle x ≡ true →
  recoveredMatterFieldFromCarrier x
    ≡
  transportedObservableRecoveredMatter
    (AGMB.ObservableTransportWitness.transport canonicalTransport x)
recoveredMatterTransportObservableCompatible _ _ = refl

recoveredFieldToInterpretable :
  ∀ x →
  AGMB.admissible canonicalBundle x ≡ true →
  CGMIOT.interpretableChargeFromCarrier x
    ≡
  recoverInterpretableCharge (recoveredMatterFieldFromCarrier x)
recoveredFieldToInterpretable x ax =
  trans
    (CGMIOT.transportObservableCompatible x ax)
    (cong
      CGMIOT.observableProjectionInterpretable
      (AGMB.ObservableTransportWitness.transport-sound
        canonicalTransport
        x
        ax))

record CanonicalGaugeMatterRecoveredMatterFieldTheorem : Setω where
  field
    strengthening : CGMST.CanonicalGaugeMatterStrengtheningTheorem
    interpretableObservable :
      CGMIOT.CanonicalGaugeMatterInterpretableObservableTheorem

    RecoveredMatterFieldCarrier : Set

    carrier-observable-compatible :
      ∀ x →
      recoveredMatterFieldFromCarrier x
        ≡
      observableProjectionRecoveredMatter
        (AGMB.observableOf canonicalBundle x)

    transport-observable-compatible :
      ∀ x →
      AGMB.admissible canonicalBundle x ≡ true →
      recoveredMatterFieldFromCarrier x
        ≡
      transportedObservableRecoveredMatter
        (AGMB.ObservableTransportWitness.transport canonicalTransport x)

    admissible-gauge-collapse :
      ∀ x →
      AGMB.admissible canonicalBundle x ≡ true →
      CGMIOT.interpretableChargeFromCarrier x
        ≡
      recoverInterpretableCharge (recoveredMatterFieldFromCarrier x)

    recovered-matter-evolve :
      ∀ x →
      recoveredMatterFieldFromCarrier x
        ≡
      recoveredMatterFieldFromCarrier
        (AGMB.evolve canonicalBundle x)

    recovered-matter-coarse :
      ∀ x →
      recoveredMatterFieldFromCarrier x
        ≡
      recoveredMatterFieldFromCarrier
        (AGMB.coarse canonicalBundle x)

    recovered-matter-offset :
      ∀ x →
      recoveredMatterFieldFromCarrier x
        ≡
      recoveredMatterFieldFromCarrier
        (AGMB.offset canonicalBundle x)

canonicalGaugeMatterRecoveredMatterFieldTheorem :
  CanonicalGaugeMatterRecoveredMatterFieldTheorem
canonicalGaugeMatterRecoveredMatterFieldTheorem =
  record
    { strengthening = canonicalStrengthening
    ; interpretableObservable =
        CGMIOT.canonicalGaugeMatterInterpretableObservableTheorem
    ; RecoveredMatterFieldCarrier = RecoveredMatterField
    ; carrier-observable-compatible =
        recoveredMatterCarrierObservableCompatible
    ; transport-observable-compatible =
        recoveredMatterTransportObservableCompatible
    ; admissible-gauge-collapse = recoveredFieldToInterpretable
    ; recovered-matter-evolve =
        λ x →
          cong
            projectRecoveredMatterField
            (CAGMI.canonicalConservedChargePreserved x)
    ; recovered-matter-coarse =
        λ x →
          cong
            projectRecoveredMatterField
            (CAGMI.canonicalConservedChargePreserved x)
    ; recovered-matter-offset =
        λ x →
          cong
            projectRecoveredMatterField
            (CAGMI.canonicalConservedChargePreserved x)
    }
