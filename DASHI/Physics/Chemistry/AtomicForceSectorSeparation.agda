module DASHI.Physics.Chemistry.AtomicForceSectorSeparation where

infix 4 _≡_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- The chemistry quotient does not identify the strong, weak, and
-- electromagnetic sectors.  Instead it records the different jobs they do:
--
--   * the strong sector supplies an admissible compact nuclear state;
--   * electromagnetism supplies the electronic orbit problem conditioned on
--     the quotient-visible nuclear charge;
--   * the weak sector supplies admissible transitions between nuclear states.
--
-- No spectral, scale-setting, or empirical periodic-table claim is made by
-- this interface alone.

record AtomicForceSectorSeparation : Set₁ where
  field
    NuclearState         : Set
    ElectronState        : Set
    ChargeIndex          : Set
    WeakTransition       : NuclearState → NuclearState → Set

    nuclearCharge        : NuclearState → ChargeIndex
    nuclearAdmissible    : NuclearState → Set
    compactNucleus       : NuclearState → Set

    electronicStateAt    : ChargeIndex → ElectronState → Set
    electromagneticBound : ChargeIndex → ElectronState → Set

    weakEnergyAllowed    : ∀ {x y} → WeakTransition x y → Set
    weakSelectionAllowed : ∀ {x y} → WeakTransition x y → Set

-- Retained strong/weak information is pre-spectral.  A separate
-- orbit-selection bridge is required before shell structure can be recovered.
record PreSpectralForceVisibility
  (F : AtomicForceSectorSeparation) : Set₁ where
  open AtomicForceSectorSeparation F
  field
    StrongWeakVisible : Set
    visibleFromNucleus : NuclearState → StrongWeakVisible

    visibilityRespectsCharge :
      ∀ {x y} → nuclearCharge x ≡ nuclearCharge y →
      visibleFromNucleus x ≡ visibleFromNucleus y
