module DASHI.Planning.AuthorityRelativeReparativeClosureExact where

open import DASHI.Core.Prelude
import DASHI.Planning.NonSubstitutionalReparationExact as Repair

------------------------------------------------------------------------
-- AUTHORITY-RELATIVE REPARATIVE CLOSURE
--
-- A repair axis can be materially marked repaired while the authority capable
-- of certifying closure remains distinct.  This blocks unilateral closure by
-- the wrongdoer/state merely because one remedial act occurred.
------------------------------------------------------------------------

data ClosureAuthority : Set where
  affectedAuthority externalAdministrator wrongdoer : ClosureAuthority

data ClosureReceipt : ClosureAuthority → Repair.RepairAxis → Set where
  affectedAuthorityClosesLand :
    ClosureReceipt affectedAuthority Repair.landReturnAxis
  affectedAuthorityClosesDecisionRights :
    ClosureReceipt affectedAuthority Repair.decisionRightsAxis
  affectedAuthorityClosesAuthority :
    ClosureReceipt affectedAuthority Repair.authorityRestorationAxis
  administratorClosesCompensation :
    ClosureReceipt externalAdministrator Repair.compensationAxis

record LegitimatelyClosed
    (bundle : Repair.ReparativeBundle)
    (axis : Repair.RepairAxis) : Set where
  constructor legitimatelyClosed
  field
    materialRepair : Repair.ReparativeBundle.status bundle axis ≡ Repair.repaired
    certifyingAuthority : ClosureAuthority
    authorityReceipt : ClosureReceipt certifyingAuthority axis

open LegitimatelyClosed public

wrongdoerCannotCertifyLandReturn :
  ClosureReceipt wrongdoer Repair.landReturnAxis → ⊥
wrongdoerCannotCertifyLandReturn ()

administratorCannotCertifyAuthorityRestoration :
  ClosureReceipt externalAdministrator Repair.authorityRestorationAxis → ⊥
administratorCannotCertifyAuthorityRestoration ()

compensationStatusDoesNotCloseAuthorityAxis :
  LegitimatelyClosed Repair.compensationOnly Repair.authorityRestorationAxis → ⊥
compensationStatusDoesNotCloseAuthorityAxis closed =
  Repair.compensationDoesNotRestoreAuthority (materialRepair closed)

record ReparativeClosureBoundary : Set where
  constructor reparativeClosureBoundary
  field
    wrongdoerMayUnilaterallyCloseEveryAxis : Bool
    wrongdoerMayUnilaterallyCloseEveryAxisIsFalse :
      wrongdoerMayUnilaterallyCloseEveryAxis ≡ false
    oneRepairedAxisClosesWholeBundle : Bool
    oneRepairedAxisClosesWholeBundleIsFalse :
      oneRepairedAxisClosesWholeBundle ≡ false
    stateRecognitionCreatesClosureAuthority : Bool
    stateRecognitionCreatesClosureAuthorityIsFalse :
      stateRecognitionCreatesClosureAuthority ≡ false

canonicalReparativeClosureBoundary : ReparativeClosureBoundary
canonicalReparativeClosureBoundary =
  reparativeClosureBoundary false refl false refl false refl
