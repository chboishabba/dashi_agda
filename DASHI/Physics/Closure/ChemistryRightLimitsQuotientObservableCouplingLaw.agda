module DASHI.Physics.Closure.ChemistryRightLimitsQuotientObservableCouplingLaw where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

open import DASHI.Physics.Closure.AtomicChemistryRecoveryTheorem as ACRT
open import DASHI.Physics.Closure.AtomicChemistryRightLimitsAdapter as ACRLA
open import DASHI.Physics.Closure.ChemistryRightLimitsPromotedObservableCouplingLaw as CRPOCL
open import DASHI.Physics.Closure.ChemistryRightLimitsQuotientObservable as CRQO
open import Ontology.DNA.ChemistryQuotient as CDQ

------------------------------------------------------------------------
-- Smallest stable triple coupling law on the atomic lane:
-- the current adapted defect/promoted pair plus one genuinely new
-- quotient-visible pre-spectral observable.
--
-- This law remains purely compatibility-facing. It does not introduce
-- spectra, scale-setting, bonding, or a finished chemistry theorem.

record ChemistryRightLimitsQuotientObservableCouplingLaw : Setω where
  field
    promotedCouplingLaw :
      CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw

    quotientObservable :
      CRQO.ChemistryRightLimitsQuotientObservable

    defectObservableName : String
    promotedObservableName : String
    quotientObservableName : String

    adaptedSupportObservable :
      ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
        (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
          (CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw.atomicRightLimitsAdapter
            promotedCouplingLaw))
      →
      CDQ.ChemistryFeature

    adaptedQuotientObservable :
      ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
        (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
          (CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw.atomicRightLimitsAdapter
            promotedCouplingLaw))
      →
      Nat

    quotientObservableVisible :
      (support :
        ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
          (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
            (CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw.atomicRightLimitsAdapter
              promotedCouplingLaw)))
      →
      adaptedQuotientObservable support
      ≡
      CRQO.ChemistryRightLimitsQuotientObservable.quotientObservable
        quotientObservable
        (adaptedSupportObservable support)

    tripleCoupledObservableClass :
      ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
        (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
          (CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw.atomicRightLimitsAdapter
            promotedCouplingLaw))
      →
      Set

    tripleCouplingStable :
      (support :
        ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
          (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
            (CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw.atomicRightLimitsAdapter
              promotedCouplingLaw)))
      →
      tripleCoupledObservableClass support

    preSpectralBoundary : Set
    preScaleSettingBoundary : Set

    nonClaimBoundary : List String

canonicalChemistryRightLimitsQuotientObservableCouplingLaw :
  ChemistryRightLimitsQuotientObservableCouplingLaw
canonicalChemistryRightLimitsQuotientObservableCouplingLaw =
  let
    pairLaw =
      CRPOCL.canonicalChemistryRightLimitsPromotedObservableCouplingLaw
    quotient =
      CRQO.canonicalChemistryRightLimitsQuotientObservable
    adapter =
      CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw.atomicRightLimitsAdapter
        pairLaw
    supportToFeature =
      ACRLA.AtomicChemistryRightLimitsAdapter.chemistrySupportToFeature
        adapter
    qObs =
      CRQO.ChemistryRightLimitsQuotientObservable.quotientObservable
        quotient
  in
  record
    { promotedCouplingLaw = pairLaw
    ; quotientObservable = quotient
    ; defectObservableName =
        CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw.defectObservableName
          pairLaw
    ; promotedObservableName =
        CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw.promotedObservableName
          pairLaw
    ; quotientObservableName =
        CRQO.ChemistryRightLimitsQuotientObservable.observableName
          quotient
    ; adaptedSupportObservable = supportToFeature
    ; adaptedQuotientObservable =
        λ support → qObs (supportToFeature support)
    ; quotientObservableVisible =
        λ _ → refl
    ; tripleCoupledObservableClass =
        λ support →
        CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw.coupledObservableClass
          pairLaw
          support
        ×
        (qObs (supportToFeature support)
         ≡
         qObs (supportToFeature support))
    ; tripleCouplingStable =
        λ support →
        CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw.couplingStable
          pairLaw
          support
        ,
        refl
    ; preSpectralBoundary =
        CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw.preSpectralBoundary
          pairLaw
    ; preScaleSettingBoundary =
        CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw.preScaleSettingBoundary
          pairLaw
    ; nonClaimBoundary =
        "ChemistryRightLimitsQuotientObservableCouplingLaw only couples the quotient-visible strong-count observable to the current defect/promoted pair on the adapted carrier"
        ∷ "It remains pre-spectral and non-scale-setting, and does not introduce spectra, scale-setting, ionization energies, bonding, periodic-table structure, nuclear dynamics, or finished chemistry"
        ∷ "Any stronger chemistry-facing relation beyond stable triple compatibility remains a later step"
        ∷ []
    }
