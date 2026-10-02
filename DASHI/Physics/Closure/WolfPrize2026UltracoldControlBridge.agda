module DASHI.Physics.Closure.WolfPrize2026UltracoldControlBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.BothwellYe2022MillimetreRedshiftReceipt as YeRedshift

------------------------------------------------------------------------
-- 2026 Wolf Prize ultracold-control bridge.
--
-- The Wolf Foundation lists Immanuel Bloch and Jun Ye as the 2026 Physics
-- laureates, sharing the citation
--
--   "For transformative, widely applicable advances in the control of
--    ultracold atomic systems."
--
-- This module records the useful formal common denominator -- controlled
-- ultracold atomic systems -- while preserving the different experimental
-- observables:
--
--   Bloch lane: optical lattices as controllable quantum many-body simulators.
--   Ye lane: optical atomic clocks as precision time/frequency observables.
--
-- The lanes meet at control architecture, not by identifying a Mott
-- transition with a clock-redshift measurement.

data UltracoldControlLane : Set where
  opticalLatticeQuantumSimulation :
    UltracoldControlLane

  opticalAtomicClockMetrology :
    UltracoldControlLane

record WolfPrize2026SourceRow : Set where
  field
    laureate :
      String

    prize :
      String

    year :
      String

    citation :
      String

    sourceUri :
      String

    lane :
      UltracoldControlLane

    highlightedContribution :
      String

open WolfPrize2026SourceRow public

blochWolfPrize2026Row : WolfPrize2026SourceRow
blochWolfPrize2026Row =
  record
    { laureate =
        "Immanuel F. Bloch"
    ; prize =
        "Wolf Prize in Physics"
    ; year =
        "2026"
    ; citation =
        "For transformative, widely applicable advances in the control of ultracold atomic systems"
    ; sourceUri =
        "https://wolffund.org.il/immanuel-f-bloch/"
    ; lane =
        opticalLatticeQuantumSimulation
    ; highlightedContribution =
        "ultracold atoms in optical lattices as a controllable platform for quantum phases and strongly interacting many-body systems"
    }

yeWolfPrize2026Row : WolfPrize2026SourceRow
yeWolfPrize2026Row =
  record
    { laureate =
        "Jun Ye"
    ; prize =
        "Wolf Prize in Physics"
    ; year =
        "2026"
    ; citation =
        "For transformative, widely applicable advances in the control of ultracold atomic systems"
    ; sourceUri =
        "https://wolffund.org.il/jun-ye/"
    ; lane =
        opticalAtomicClockMetrology
    ; highlightedContribution =
        "ultra-stable optical atomic clocks and precision control of laser-trapped atoms for fundamental-physics tests and relativistic geodesy"
    }

canonicalWolfPrize2026Rows : List WolfPrize2026SourceRow
canonicalWolfPrize2026Rows =
  blochWolfPrize2026Row
  ∷ yeWolfPrize2026Row
  ∷ []

record UltracoldControlCommonDenominator : Set where
  field
    commonPlatform :
      String

    blochControlSurface :
      String

    yeControlSurface :
      String

    sharedControlPrinciple :
      String

    distinctObservableLanes :
      Bool

    distinctObservableLanesIsTrue :
      distinctObservableLanes ≡ true

open UltracoldControlCommonDenominator public

canonicalUltracoldControlCommonDenominator :
  UltracoldControlCommonDenominator
canonicalUltracoldControlCommonDenominator =
  record
    { commonPlatform =
        "laser-controlled ultracold atomic ensembles"
    ; blochControlSurface =
        "lattice geometry + tunnelling + interaction + site-resolved many-body observables"
    ; yeControlSurface =
        "clock-transition coherence + laser stability + trapped-atom interactions + spatial frequency comparison"
    ; sharedControlPrinciple =
        "engineer and interrogate quantum degrees of freedom strongly enough that a theoretical observable becomes an experimentally resolvable quantity"
    ; distinctObservableLanes =
        true
    ; distinctObservableLanesIsTrue =
        refl
    }

record EquationPageToMeasuredCloudBridge : Set where
  field
    equation :
      String

    equationOwner :
      String

    controlledCarrier :
      String

    spatialResolution :
      String

    measuredObservable :
      String

    empiricalSource :
      YeRedshift.BothwellYe2022Source

    empiricalSourceIsCanonical :
      empiricalSource ≡ YeRedshift.canonicalBothwellYe2022Source

    interpretation :
      String

    mathematicsIdentifiedWithMeasurement :
      Bool

    mathematicsIdentifiedWithMeasurementIsFalse :
      mathematicsIdentifiedWithMeasurement ≡ false

    measurementProvidesEmpiricalContact :
      Bool

    measurementProvidesEmpiricalContactIsTrue :
      measurementProvidesEmpiricalContact ≡ true

open EquationPageToMeasuredCloudBridge public

canonicalEquationPageToMeasuredCloudBridge :
  EquationPageToMeasuredCloudBridge
canonicalEquationPageToMeasuredCloudBridge =
  record
    { equation =
        "Delta f / f = Delta U / c^2; in the local uniform-field model Delta U = g h"
    ; equationOwner =
        "DASHI.Physics.Closure.QuantumClockProperTimeRedshiftBridge"
    ; controlledCarrier =
        "ultracold strontium atoms confined in a vertical optical lattice"
    ; spatialResolution =
        "clock frequency resolved across one millimetre-scale atomic sample"
    ; measuredObservable =
        "linear frequency gradient across the sample"
    ; empiricalSource =
        YeRedshift.canonicalBothwellYe2022Source
    ; empiricalSourceIsCanonical =
        refl
    ; interpretation =
        "the formal relation specifies the observable dependence; ultracold control and precision spectroscopy make that dependence measurable within one atomic ensemble"
    ; mathematicsIdentifiedWithMeasurement =
        false
    ; mathematicsIdentifiedWithMeasurementIsFalse =
        refl
    ; measurementProvidesEmpiricalContact =
        true
    ; measurementProvidesEmpiricalContactIsTrue =
        refl
    }

record WolfPrize2026UltracoldControlBridge : Set where
  field
    prizeRows :
      List WolfPrize2026SourceRow

    prizeRowsAreCanonical :
      prizeRows ≡ canonicalWolfPrize2026Rows

    commonDenominator :
      UltracoldControlCommonDenominator

    commonDenominatorIsCanonical :
      commonDenominator ≡ canonicalUltracoldControlCommonDenominator

    equationToMeasurement :
      EquationPageToMeasuredCloudBridge

    equationToMeasurementIsCanonical :
      equationToMeasurement ≡ canonicalEquationPageToMeasuredCloudBridge

    yeRedshiftReceipt :
      YeRedshift.BothwellYe2022ReceiptBoundary

    yeRedshiftReceiptIsCanonical :
      yeRedshiftReceipt ≡ YeRedshift.canonicalBothwellYe2022ReceiptBoundary

    prizeCitationUsedAsPhysicsProof :
      Bool

    prizeCitationUsedAsPhysicsProofIsFalse :
      prizeCitationUsedAsPhysicsProof ≡ false

    blochAndYeObservablesConflated :
      Bool

    blochAndYeObservablesConflatedIsFalse :
      blochAndYeObservablesConflated ≡ false

    reading :
      List String

open WolfPrize2026UltracoldControlBridge public

canonicalWolfPrize2026UltracoldControlBridge :
  WolfPrize2026UltracoldControlBridge
canonicalWolfPrize2026UltracoldControlBridge =
  record
    { prizeRows =
        canonicalWolfPrize2026Rows
    ; prizeRowsAreCanonical =
        refl
    ; commonDenominator =
        canonicalUltracoldControlCommonDenominator
    ; commonDenominatorIsCanonical =
        refl
    ; equationToMeasurement =
        canonicalEquationPageToMeasuredCloudBridge
    ; equationToMeasurementIsCanonical =
        refl
    ; yeRedshiftReceipt =
        YeRedshift.canonicalBothwellYe2022ReceiptBoundary
    ; yeRedshiftReceiptIsCanonical =
        refl
    ; prizeCitationUsedAsPhysicsProof =
        false
    ; prizeCitationUsedAsPhysicsProofIsFalse =
        refl
    ; blochAndYeObservablesConflated =
        false
    ; blochAndYeObservablesConflatedIsFalse =
        refl
    ; reading =
        "Bloch and Ye share an experimental-control paradigm, not one identical observable."
        ∷ "Bloch's optical-lattice lane turns model Hamiltonians and many-body phases into controllable laboratory systems."
        ∷ "Ye's optical-clock lane turns relativistic frequency-shift equations into spatially resolved clock observables."
        ∷ "The 2022 millimetre-scale strontium result is the repository's concrete equation-to-measurement witness for the Ye lane."
        ∷ "The 2026 Wolf Prize citation is provenance for the shared control theme; it is not itself evidence for any physical law."
        ∷ []
    }

canonicalWolfPrize2026KeepsLanesDistinct :
  blochAndYeObservablesConflated
    canonicalWolfPrize2026UltracoldControlBridge
  ≡
  false
canonicalWolfPrize2026KeepsLanesDistinct =
  refl

canonicalWolfPrize2026DoesNotUsePrizeAsProof :
  prizeCitationUsedAsPhysicsProof
    canonicalWolfPrize2026UltracoldControlBridge
  ≡
  false
canonicalWolfPrize2026DoesNotUsePrizeAsProof =
  refl
