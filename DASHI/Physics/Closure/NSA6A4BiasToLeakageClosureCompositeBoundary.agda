module DASHI.Physics.Closure.NSA6A4BiasToLeakageClosureCompositeBoundary where

-- NS A4/A5 bias-to-A6 leakage closure composite boundary.
--
-- This module records the claimed A6/A7 proof-content handoff:
--
--   A4 residual-positive output support
--     -> A5 kappa-bias vanishing
--     -> A6.1 localized enstrophy ODE decomposition
--     -> A6.2 Bony/paraproduct replacement with O(N^-1) correction
--     -> A6.3 pointwise-to-Abel / shell-mean transfer
--     -> A6.4 A5 bias vanishing absorbed into dissipation
--     -> assembled inequality
--          ∂t D_r + (ε0/4) c_lambda D_r <= C D_r^(1+α)
--     -> A7 residual depletion / A8 local defect monotonicity /
--        A9 CKN-BKM closure.
--
-- It deliberately composes only existing boundary receipts.  It does not
-- prove the A4 coarea theorem, A5 bias vanishing for PDE measures, the
-- A6 leakage identity, residual depletion, Navier-Stokes regularity, or
-- any Clay promotion.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSA4ResidualPositiveTheoremLadderBoundary
  as A4Residual
import DASHI.Physics.Closure.NSA6TheoremLadderBoundary
  as A6Ladder
import DASHI.Physics.Closure.NSPointwiseToAbelCompositeA6Boundary
  as Pointwise
import DASHI.Physics.Closure.NSTriadicCompensatedLeakageIdentityBoundary
  as Triadic

------------------------------------------------------------------------
-- Local utilities.

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

infixr 2 _×_
infixr 4 _,_

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Imported support.

record ImportedA4BiasToLeakageClosureSupport : Set where
  field
    a4ResidualPositiveLadder :
      A4Residual.NSA4ResidualPositiveTheoremLadderBoundary
    a4ResidualPositiveLadderIsCanonical :
      a4ResidualPositiveLadder
        ≡ A4Residual.canonicalNSA4ResidualPositiveTheoremLadderBoundary
    a6TheoremLadder :
      A6Ladder.NSA6TheoremLadderBoundary
    a6TheoremLadderIsCanonical :
      a6TheoremLadder
        ≡ A6Ladder.canonicalNSA6TheoremLadderBoundary
    pointwiseToAbelComposite :
      Pointwise.NSPointwiseToAbelCompositeA6Boundary
    pointwiseToAbelCompositeIsCanonical :
      pointwiseToAbelComposite
        ≡ Pointwise.canonicalNSPointwiseToAbelCompositeA6Boundary
    triadicLeakageBoundary :
      Triadic.NSTriadicCompensatedLeakageIdentityBoundary
    triadicLeakageBoundaryIsCanonical :
      triadicLeakageBoundary
        ≡ Triadic.canonicalNSTriadicCompensatedLeakageIdentityBoundary

    a4ResidualStillFalse :
      A4Residual.residualPositivePromotedHere ≡ false
    a4NoCollapseStillFalse :
      A4Residual.a4NoCollapsePromotedHere ≡ false
    a5BiasStillFalse :
      A4Residual.a5BiasVanishingPromotedHere ≡ false
    a4LadderA6StillFalse :
      A4Residual.a6LeakagePromotedHere ≡ false
    a4LadderA7StillFalse :
      A4Residual.a7ResidualDepletionPromotedHere ≡ false
    a4LadderClayStillFalse :
      A4Residual.clayNavierStokesPromotedHere ≡ false
    pointwiseA6StillFalse :
      Pointwise.a6PointwiseToAbelClosed ≡ false
    a6TheoremStillFalse :
      A6Ladder.A6TheoremProved ≡ false
    a6ResidualNonpositiveStillFalse :
      A6Ladder.residualNonpositiveProved ≡ false
    a6LocalDefectStillFalse :
      A6Ladder.localDefectMonotonicityProved ≡ false
    a6ClayStillFalse :
      A6Ladder.nsClayPromoted ≡ false
    triadicSignedIdentityStillFalse :
      Triadic.signedCoercivityIdentityProved ≡ false
    triadicCriticalResidualStillFalse :
      Triadic.criticalResidualDepletionProved ≡ false
    triadicLocalDefectStillFalse :
      Triadic.fullLocalDefectMonotonicityProved ≡ false
    triadicClayStillFalse :
      Triadic.clayNavierStokesPromoted ≡ false

canonicalImportedA4BiasToLeakageClosureSupport :
  ImportedA4BiasToLeakageClosureSupport
canonicalImportedA4BiasToLeakageClosureSupport =
  record
    { a4ResidualPositiveLadder =
        A4Residual.canonicalNSA4ResidualPositiveTheoremLadderBoundary
    ; a4ResidualPositiveLadderIsCanonical =
        refl
    ; a6TheoremLadder =
        A6Ladder.canonicalNSA6TheoremLadderBoundary
    ; a6TheoremLadderIsCanonical =
        refl
    ; pointwiseToAbelComposite =
        Pointwise.canonicalNSPointwiseToAbelCompositeA6Boundary
    ; pointwiseToAbelCompositeIsCanonical =
        refl
    ; triadicLeakageBoundary =
        Triadic.canonicalNSTriadicCompensatedLeakageIdentityBoundary
    ; triadicLeakageBoundaryIsCanonical =
        refl
    ; a4ResidualStillFalse =
        refl
    ; a4NoCollapseStillFalse =
        refl
    ; a5BiasStillFalse =
        refl
    ; a4LadderA6StillFalse =
        refl
    ; a4LadderA7StillFalse =
        refl
    ; a4LadderClayStillFalse =
        refl
    ; pointwiseA6StillFalse =
        refl
    ; a6TheoremStillFalse =
        refl
    ; a6ResidualNonpositiveStillFalse =
        refl
    ; a6LocalDefectStillFalse =
        refl
    ; a6ClayStillFalse =
        refl
    ; triadicSignedIdentityStillFalse =
        refl
    ; triadicCriticalResidualStillFalse =
        refl
    ; triadicLocalDefectStillFalse =
        refl
    ; triadicClayStillFalse =
        refl
    }

------------------------------------------------------------------------
-- Closure ladder.

data A4BiasToLeakageClosureRung : Set where
  rung-a4-coarea-output-support :
    A4BiasToLeakageClosureRung
  rung-a4-residual-positive-after-errors :
    A4BiasToLeakageClosureRung
  rung-a5-stationary-kappa-bias-vanishing :
    A4BiasToLeakageClosureRung
  rung-a6-localized-enstrophy-ode-decomposition :
    A4BiasToLeakageClosureRung
  rung-a6-bony-paraproduct-replacement :
    A4BiasToLeakageClosureRung
  rung-a6-pointwise-to-abel-shell-mean-transfer :
    A4BiasToLeakageClosureRung
  rung-a6-bias-absorbed-into-dissipation :
    A4BiasToLeakageClosureRung
  rung-a6-assembled-leakage-inequality :
    A4BiasToLeakageClosureRung
  rung-a7-critical-residual-depletion :
    A4BiasToLeakageClosureRung
  rung-a8-local-defect-monotonicity :
    A4BiasToLeakageClosureRung
  rung-a9-ckn-bkm-closure :
    A4BiasToLeakageClosureRung

canonicalA4BiasToLeakageClosureRungs :
  List A4BiasToLeakageClosureRung
canonicalA4BiasToLeakageClosureRungs =
  rung-a4-coarea-output-support
  ∷ rung-a4-residual-positive-after-errors
  ∷ rung-a5-stationary-kappa-bias-vanishing
  ∷ rung-a6-localized-enstrophy-ode-decomposition
  ∷ rung-a6-bony-paraproduct-replacement
  ∷ rung-a6-pointwise-to-abel-shell-mean-transfer
  ∷ rung-a6-bias-absorbed-into-dissipation
  ∷ rung-a6-assembled-leakage-inequality
  ∷ rung-a7-critical-residual-depletion
  ∷ rung-a8-local-defect-monotonicity
  ∷ rung-a9-ckn-bkm-closure
  ∷ []

a4BiasToLeakageClosureRungCount : Nat
a4BiasToLeakageClosureRungCount =
  listLength canonicalA4BiasToLeakageClosureRungs

a4BiasToLeakageClosureRungCountIs10 :
  a4BiasToLeakageClosureRungCount ≡ 10
a4BiasToLeakageClosureRungCountIs10 =
  refl

------------------------------------------------------------------------
-- Recorded A6 proof-content clauses.

data A6ProofClause : Set where
  clause-a61-localized-enstrophy-ode-decomposition :
    A6ProofClause
  clause-a62-bony-paraproduct-replacement-with-oneminus-correction :
    A6ProofClause
  clause-a63-pointwise-to-abel-shell-mean-transfer :
    A6ProofClause
  clause-a64-a5-bias-vanishing-absorbed-into-dissipation :
    A6ProofClause
  clause-a6-assembled-inequality-with-clambda :
    A6ProofClause

canonicalA6ProofClauses :
  List A6ProofClause
canonicalA6ProofClauses =
  clause-a61-localized-enstrophy-ode-decomposition
  ∷ clause-a62-bony-paraproduct-replacement-with-oneminus-correction
  ∷ clause-a63-pointwise-to-abel-shell-mean-transfer
  ∷ clause-a64-a5-bias-vanishing-absorbed-into-dissipation
  ∷ clause-a6-assembled-inequality-with-clambda
  ∷ []

a6ProofClauseCount : Nat
a6ProofClauseCount =
  listLength canonicalA6ProofClauses

a6ProofClauseCountIs5 :
  a6ProofClauseCount ≡ 5
a6ProofClauseCountIs5 =
  refl

record A4BiasToLeakageClosureRow : Set where
  field
    rung :
      A4BiasToLeakageClosureRung
    routeName :
      String
    routeSummary :
      String
    proofContentRecorded :
      Bool
    proofContentRecordedIsTrue :
      proofContentRecorded ≡ true
    theoremPromotedHere :
      Bool
    theoremPromotedHereIsFalse :
      theoremPromotedHere ≡ false

a4CoareaOutputSupportRow :
  A4BiasToLeakageClosureRow
a4CoareaOutputSupportRow =
  record
    { rung =
        rung-a4-coarea-output-support
    ; routeName =
        "A4 coarea output support"
    ; routeSummary =
        "Record the A4 derivative, Jacobian lower-bound, eta-slab coarea, Sard-Fubini, antipodal exclusion, and uniform-in-normal output-support proof content."
    ; proofContentRecorded =
        true
    ; proofContentRecordedIsTrue =
        refl
    ; theoremPromotedHere =
        false
    ; theoremPromotedHereIsFalse =
        refl
    }

a4ResidualPositiveRow :
  A4BiasToLeakageClosureRow
a4ResidualPositiveRow =
  record
    { rung =
        rung-a4-residual-positive-after-errors
    ; routeName =
        "A4 residual positive after errors"
    ; routeSummary =
        "Record the A4 residual-positive margin after subtracting log-rate, antipodal, low-vorticity, null-output, and Bony errors."
    ; proofContentRecorded =
        true
    ; proofContentRecordedIsTrue =
        refl
    ; theoremPromotedHere =
        false
    ; theoremPromotedHereIsFalse =
        refl
    }

a5KappaBiasVanishingRow :
  A4BiasToLeakageClosureRow
a5KappaBiasVanishingRow =
  record
    { rung =
        rung-a5-stationary-kappa-bias-vanishing
    ; routeName =
        "A5 kappa-bias vanishing"
    ; routeSummary =
        "Record the A5 fixed-point argument: transfer stationarity plus A4 angular richness plus transfer neutrality force |Bias(mu_r)| = O(N^-1/2)) -> 0."
    ; proofContentRecorded =
        true
    ; proofContentRecordedIsTrue =
        refl
    ; theoremPromotedHere =
        false
    ; theoremPromotedHereIsFalse =
        refl
    }

a61LocalizedEnstrophyODERow :
  A4BiasToLeakageClosureRow
a61LocalizedEnstrophyODERow =
  record
    { rung =
        rung-a6-localized-enstrophy-ode-decomposition
    ; routeName =
        "A6.1 localized enstrophy ODE decomposition"
    ; routeSummary =
        "Record the localized enstrophy ODE decomposition into stretching, pressure, and viscous terms at scale r as the A6 entry surface."
    ; proofContentRecorded =
        true
    ; proofContentRecordedIsTrue =
        refl
    ; theoremPromotedHere =
        false
    ; theoremPromotedHereIsFalse =
        refl
    }

a62BonyParaproductRow :
  A4BiasToLeakageClosureRow
a62BonyParaproductRow =
  record
    { rung =
        rung-a6-bony-paraproduct-replacement
    ; routeName =
        "A6.2 Bony/paraproduct replacement"
    ; routeSummary =
        "Record the Bony paraproduct replacement of the stretching term by shell interactions with an O(N^-1) correction."
    ; proofContentRecorded =
        true
    ; proofContentRecordedIsTrue =
        refl
    ; theoremPromotedHere =
        false
    ; theoremPromotedHereIsFalse =
        refl
    }

a63PointwiseToAbelShellMeanRow :
  A4BiasToLeakageClosureRow
a63PointwiseToAbelShellMeanRow =
  record
    { rung =
        rung-a6-pointwise-to-abel-shell-mean-transfer
    ; routeName =
        "A6.3 pointwise-to-Abel / shell-mean transfer"
    ; routeSummary =
        "Record the pointwise-to-Abel transfer replacing localized stretching by the shell-mean quantity ∫ λ(2κ²-1) dμ_r."
    ; proofContentRecorded =
        true
    ; proofContentRecordedIsTrue =
        refl
    ; theoremPromotedHere =
        false
    ; theoremPromotedHereIsFalse =
        refl
    }

a64BiasAbsorbedIntoDissipationRow :
  A4BiasToLeakageClosureRow
a64BiasAbsorbedIntoDissipationRow =
  record
    { rung =
        rung-a6-bias-absorbed-into-dissipation
    ; routeName =
        "A6.4 A5 bias vanishing absorbed into dissipation"
    ; routeSummary =
        "Record the A5 bound |Bias(mu_r)| = O(N^-1/2) and its absorption into the viscous coefficient for r < r0."
    ; proofContentRecorded =
        true
    ; proofContentRecordedIsTrue =
        refl
    ; theoremPromotedHere =
        false
    ; theoremPromotedHereIsFalse =
        refl
    }

a6AssembledLeakageInequalityRow :
  A4BiasToLeakageClosureRow
a6AssembledLeakageInequalityRow =
  record
    { rung =
        rung-a6-assembled-leakage-inequality
    ; routeName =
        "A6 assembled leakage inequality"
    ; routeSummary =
        "Record the assembled inequality ∂t D_r + (ε0/4)c_lambda D_r <= C D_r^(1+α) after combining A6.1-A6.4."
    ; proofContentRecorded =
        true
    ; proofContentRecordedIsTrue =
        refl
    ; theoremPromotedHere =
        false
    ; theoremPromotedHereIsFalse =
        refl
    }

a7CriticalResidualDepletionRow :
  A4BiasToLeakageClosureRow
a7CriticalResidualDepletionRow =
  record
    { rung =
        rung-a7-critical-residual-depletion
    ; routeName =
        "A7 critical residual depletion"
    ; routeSummary =
        "Record the Gronwall depletion step converting the assembled A6 inequality into D_r(t) -> 0 below the small-data threshold."
    ; proofContentRecorded =
        true
    ; proofContentRecordedIsTrue =
        refl
    ; theoremPromotedHere =
        false
    ; theoremPromotedHereIsFalse =
        refl
    }

a8LocalDefectMonotonicityRow :
  A4BiasToLeakageClosureRow
a8LocalDefectMonotonicityRow =
  record
    { rung =
        rung-a8-local-defect-monotonicity
    ; routeName =
        "A8 local defect monotonicity"
    ; routeSummary =
        "Record the downstream CKN-scale iteration target D_(theta r) <= q D_r + C D_r^(1+alpha), while keeping A8 itself unpromoted here."
    ; proofContentRecorded =
        true
    ; proofContentRecordedIsTrue =
        refl
    ; theoremPromotedHere =
        false
    ; theoremPromotedHereIsFalse =
        refl
    }

a9CKNBKMClosureRow :
  A4BiasToLeakageClosureRow
a9CKNBKMClosureRow =
  record
    { rung =
        rung-a9-ckn-bkm-closure
    ; routeName =
        "A9 CKN/BKM closure"
    ; routeSummary =
        "Record the downstream classical closure target via CKN epsilon regularity and BKM continuation, while keeping A9 and Clay false."
    ; proofContentRecorded =
        true
    ; proofContentRecordedIsTrue =
        refl
    ; theoremPromotedHere =
        false
    ; theoremPromotedHereIsFalse =
        refl
    }

canonicalA4BiasToLeakageClosureRows :
  List A4BiasToLeakageClosureRow
canonicalA4BiasToLeakageClosureRows =
  a4CoareaOutputSupportRow
  ∷ a4ResidualPositiveRow
  ∷ a5KappaBiasVanishingRow
  ∷ a61LocalizedEnstrophyODERow
  ∷ a62BonyParaproductRow
  ∷ a63PointwiseToAbelShellMeanRow
  ∷ a64BiasAbsorbedIntoDissipationRow
  ∷ a6AssembledLeakageInequalityRow
  ∷ a7CriticalResidualDepletionRow
  ∷ a8LocalDefectMonotonicityRow
  ∷ a9CKNBKMClosureRow
  ∷ []

a4BiasToLeakageClosureRowCount : Nat
a4BiasToLeakageClosureRowCount =
  listLength canonicalA4BiasToLeakageClosureRows

a4BiasToLeakageClosureRowCountIs10 :
  a4BiasToLeakageClosureRowCount ≡ 10
a4BiasToLeakageClosureRowCountIs10 =
  refl

------------------------------------------------------------------------
-- Error and sign handoff guards.

data A4A5A6HandoffGuard : Set where
  guard-a4-margin-survives-all-errors :
    A4A5A6HandoffGuard
  guard-stationary-pushforward-bias-is-neutral :
    A4A5A6HandoffGuard
  guard-pde-measure-distance-to-stationary-goes-to-zero :
    A4A5A6HandoffGuard
  guard-localized-enstrophy-ode-is-decomposed :
    A4A5A6HandoffGuard
  guard-bony-correction-is-order-oneminus :
    A4A5A6HandoffGuard
  guard-pointwise-stretching-is-shell-mean-transferred :
    A4A5A6HandoffGuard
  guard-a5-bias-error-is-absorbed-into-dissipation :
    A4A5A6HandoffGuard
  guard-assembled-a6-inequality-has-positive-damping :
    A4A5A6HandoffGuard
  guard-a7-gronwall-depletion-stays-below-ckn-threshold :
    A4A5A6HandoffGuard

canonicalA4A5A6HandoffGuards :
  List A4A5A6HandoffGuard
canonicalA4A5A6HandoffGuards =
  guard-a4-margin-survives-all-errors
  ∷ guard-stationary-pushforward-bias-is-neutral
  ∷ guard-pde-measure-distance-to-stationary-goes-to-zero
  ∷ guard-localized-enstrophy-ode-is-decomposed
  ∷ guard-bony-correction-is-order-oneminus
  ∷ guard-pointwise-stretching-is-shell-mean-transferred
  ∷ guard-a5-bias-error-is-absorbed-into-dissipation
  ∷ guard-assembled-a6-inequality-has-positive-damping
  ∷ guard-a7-gronwall-depletion-stays-below-ckn-threshold
  ∷ []

a4A5A6HandoffGuardCount : Nat
a4A5A6HandoffGuardCount =
  listLength canonicalA4A5A6HandoffGuards

a4A5A6HandoffGuardCountIs8 :
  a4A5A6HandoffGuardCount ≡ 8
a4A5A6HandoffGuardCountIs8 =
  refl

------------------------------------------------------------------------
-- Promotion gates: all remain closed.

a4OutputSupportTheoremProved : Bool
a4OutputSupportTheoremProved =
  false

a5BiasVanishingTheoremProved : Bool
a5BiasVanishingTheoremProved =
  false

a6PointwiseToAbelTheoremProved : Bool
a6PointwiseToAbelTheoremProved =
  false

a6TriadicLeakageTheoremProved : Bool
a6TriadicLeakageTheoremProved =
  false

a7CriticalResidualDepletionTheoremProved : Bool
a7CriticalResidualDepletionTheoremProved =
  false

a8LocalDefectMonotonicityTheoremProved : Bool
a8LocalDefectMonotonicityTheoremProved =
  false

a9CKNBKMClosureTheoremProved : Bool
a9CKNBKMClosureTheoremProved =
  false

nsClayPromotedHere : Bool
nsClayPromotedHere =
  false

terminalPromotionHere : Bool
terminalPromotionHere =
  false

record NSA6A4BiasToLeakageClosureCompositeBoundary : Set where
  field
    importedSupport :
      ImportedA4BiasToLeakageClosureSupport
    importedSupportIsCanonical :
      importedSupport ≡ canonicalImportedA4BiasToLeakageClosureSupport
    closureRungs :
      List A4BiasToLeakageClosureRung
    closureRungsAreCanonical :
      closureRungs ≡ canonicalA4BiasToLeakageClosureRungs
    closureRows :
      List A4BiasToLeakageClosureRow
    closureRowsAreCanonical :
      closureRows ≡ canonicalA4BiasToLeakageClosureRows
    handoffGuards :
      List A4A5A6HandoffGuard
    handoffGuardsAreCanonical :
      handoffGuards ≡ canonicalA4A5A6HandoffGuards

    a4OutputSupportTheoremProvedIsFalse :
      a4OutputSupportTheoremProved ≡ false
    a5BiasVanishingTheoremProvedIsFalse :
      a5BiasVanishingTheoremProved ≡ false
    a6PointwiseToAbelTheoremProvedIsFalse :
      a6PointwiseToAbelTheoremProved ≡ false
    a6TriadicLeakageTheoremProvedIsFalse :
      a6TriadicLeakageTheoremProved ≡ false
    a7CriticalResidualDepletionTheoremProvedIsFalse :
      a7CriticalResidualDepletionTheoremProved ≡ false
    a8LocalDefectMonotonicityTheoremProvedIsFalse :
      a8LocalDefectMonotonicityTheoremProved ≡ false
    a9CKNBKMClosureTheoremProvedIsFalse :
      a9CKNBKMClosureTheoremProved ≡ false
    nsClayPromotedHereIsFalse :
      nsClayPromotedHere ≡ false
    terminalPromotionHereIsFalse :
      terminalPromotionHere ≡ false

canonicalNSA6A4BiasToLeakageClosureCompositeBoundary :
  NSA6A4BiasToLeakageClosureCompositeBoundary
canonicalNSA6A4BiasToLeakageClosureCompositeBoundary =
  record
    { importedSupport =
        canonicalImportedA4BiasToLeakageClosureSupport
    ; importedSupportIsCanonical =
        refl
    ; closureRungs =
        canonicalA4BiasToLeakageClosureRungs
    ; closureRungsAreCanonical =
        refl
    ; closureRows =
        canonicalA4BiasToLeakageClosureRows
    ; closureRowsAreCanonical =
        refl
    ; handoffGuards =
        canonicalA4A5A6HandoffGuards
    ; handoffGuardsAreCanonical =
        refl
    ; a4OutputSupportTheoremProvedIsFalse =
        refl
    ; a5BiasVanishingTheoremProvedIsFalse =
        refl
    ; a6PointwiseToAbelTheoremProvedIsFalse =
        refl
    ; a6TriadicLeakageTheoremProvedIsFalse =
        refl
    ; a7CriticalResidualDepletionTheoremProvedIsFalse =
        refl
    ; a8LocalDefectMonotonicityTheoremProvedIsFalse =
        refl
    ; a9CKNBKMClosureTheoremProvedIsFalse =
        refl
    ; nsClayPromotedHereIsFalse =
        refl
    ; terminalPromotionHereIsFalse =
        refl
    }

------------------------------------------------------------------------
-- Canonical safety receipt.

boundaryRecordsA4BiasToA6LeakageHandoff : Bool
boundaryRecordsA4BiasToA6LeakageHandoff =
  true

boundaryIsFailClosed : Bool
boundaryIsFailClosed =
  true

boundaryPromotesNoTheorem :
  (a4OutputSupportTheoremProved ≡ false) ×
  (a5BiasVanishingTheoremProved ≡ false) ×
  (a6PointwiseToAbelTheoremProved ≡ false) ×
  (a6TriadicLeakageTheoremProved ≡ false) ×
  (a7CriticalResidualDepletionTheoremProved ≡ false) ×
  (a8LocalDefectMonotonicityTheoremProved ≡ false) ×
  (a9CKNBKMClosureTheoremProved ≡ false) ×
  (nsClayPromotedHere ≡ false) ×
  (terminalPromotionHere ≡ false)
boundaryPromotesNoTheorem =
  refl , refl , refl , refl , refl , refl , refl , refl , refl
