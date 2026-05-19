module DASHI.Physics.Closure.ChemistryRightLimitsBlockageBroken where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ChemistryRightLimitsInterpretationContract as Contract
import DASHI.Physics.Closure.AtomicChemistryRightLimitsAdapter as Adapter
import DASHI.Physics.Closure.ChemistryRightLimitsObservableLaw as FirstLaw
import DASHI.Physics.Closure.ChemistryRightLimitsPromotedObservableCouplingLaw as Promoted
import DASHI.Physics.Closure.ChemistryRightLimitsQuotientObservable as Quotient
import DASHI.Physics.Closure.ChemistryRightLimitsQuotientObservableCouplingLaw as Coupling

------------------------------------------------------------------------
-- Chemistry blockage discharge.
--
-- Current old blocker shape:
--   interpretation contract + adapter seam + first law + promoted pair landed;
--   remaining request was a genuinely new quotient-visible pre-spectral
--   observable, then a coupling law to the current defect/promoted pair.
--
-- The plain logical move is to bundle exactly those objects.  No spectral,
-- scale-setting, bonding, periodic-table, or nuclear-dynamics claim is added.

record ChemistryRightLimitsBlockageBroken : Setω where
  field
    interpretationContract :
      Contract.ChemistryRightLimitsInterpretationContract

    adapterSeam :
      Adapter.AtomicChemistryRightLimitsAdapter

    firstObservableLaw :
      FirstLaw.ChemistryRightLimitsObservableLaw

    promotedObservableCoupling :
      Promoted.ChemistryRightLimitsPromotedObservableCouplingLaw

    quotientVisibleObservable :
      Quotient.ChemistryRightLimitsQuotientObservable

    quotientVisibleCoupling :
      Coupling.ChemistryRightLimitsQuotientObservableCouplingLaw

    blockageBroken : ⊤

    remainingBoundary : List String

canonicalChemistryRightLimitsBlockageBroken :
  ChemistryRightLimitsBlockageBroken
canonicalChemistryRightLimitsBlockageBroken = record
  { interpretationContract =
      Contract.canonicalChemistryRightLimitsInterpretationContract
  ; adapterSeam =
      Adapter.canonicalAtomicChemistryRightLimitsAdapter
  ; firstObservableLaw =
      FirstLaw.canonicalChemistryRightLimitsObservableLaw
  ; promotedObservableCoupling =
      Promoted.canonicalChemistryRightLimitsPromotedObservableCouplingLaw
  ; quotientVisibleObservable =
      Quotient.canonicalChemistryRightLimitsQuotientObservable
  ; quotientVisibleCoupling =
      Coupling.canonicalChemistryRightLimitsQuotientObservableCouplingLaw
  ; blockageBroken = tt
  ; remainingBoundary =
      "Chemistry blocker is discharged only at pre-spectral observable/coupling level"
      ∷ "No spectra, scale setting, ionization energy, bonding, periodic-table completion, nuclear dynamics, or finished chemistry theorem is claimed"
      ∷ "The next honest chemistry target is a scale-setting/spectral semantics layer, not another blocker spec"
      ∷ []
  }
