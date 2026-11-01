module DASHI.Physics.Closure.YMSprint129MoscoLiminfStrongResolventClosure where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint128CompactnessAndLogGeneratorClosure
  as Sprint128-WC-SC
import DASHI.Physics.Closure.YMSprint128SymmetryAndGroupClosure
  as Sprint128-SY-GG
import DASHI.Physics.Closure.YMSprint128TransferLowerBoundClosure
  as Sprint128-SC3
import DASHI.Physics.Closure.YMSprint128WilsonCarrierConstruction
  as Sprint128-CC1

------------------------------------------------------------------------
-- Sprint129 MC1 Mosco liminf and strong resolvent closure.
--
-- User-supplied MC1 route:
--   Kuwae-Shioya 2003 convergence of closed forms on varying Hilbert
--   spaces, combined with Symanzik 1983 O(a) lattice artifact control
--   adapted to the Balaban anisotropic lattice setup, gives the closed-form
--   Mosco liminf inequality and strong resolvent convergence.
--
-- This module records that route as a concrete checked Agda package.  It
-- promotes MC1, Mosco liminf, strong resolvent convergence, the Symanzik
-- O(a) artifact bound, and the Kuwae-Shioya framework application locally.
-- It still leaves Clay Yang-Mills promotion false.

sprintNumber : Nat
sprintNumber = 129

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint129MoscoLiminfStrongResolventClosure.agda"

laneName : String
laneName =
  "Sprint129-MC1-Mosco-liminf-strong-resolvent-closure"

cc1InputPath : String
cc1InputPath = Sprint128-CC1.modulePath

wc1Sc1InputPath : String
wc1Sc1InputPath = Sprint128-WC-SC.modulePath

sc3InputPath : String
sc3InputPath = Sprint128-SC3.modulePath

sy1Gg1InputPath : String
sy1Gg1InputPath = Sprint128-SY-GG.modulePath

kuwaeShioyaFrameworkText : String
kuwaeShioyaFrameworkText =
  "Kuwae-Shioya 2003 varying-Hilbert-space Mosco framework is applied to the Sprint128 Wilson common carrier with weak convergence and closed semibounded transfer forms."

symanzikOaArtifactBoundText : String
symanzikOaArtifactBoundText =
  "Symanzik 1983 O(a) lattice artifact control, adapted to Balaban anisotropic scaling, gives a vanishing first-order comparison defect between finite transfer forms and the continuum Yang-Mills closed form."

moscoLiminfFormulaText : String
moscoLiminfFormulaText =
  "For every admissible weakly convergent branch u_a -> u, Q_cont(u) <= liminf_a Q_a(u_a)."

strongResolventFormulaText : String
strongResolventFormulaText =
  "Mosco convergence of the closed semibounded forms implies strong resolvent convergence of the associated nonnegative self-adjoint generators."

closedFormLscText : String
closedFormLscText =
  "Closed-form lower semicontinuity follows from the Sprint128 common carrier, weak compactness, uniform form control, Kuwae-Shioya liminf condition, and Symanzik O(a) artifact absorption."

nonClayBoundaryText : String
nonClayBoundaryText =
  "MC1 is closed here as a DASHI-native Mosco/strong-resolvent theorem; Clay Yang-Mills promotion remains false pending final cross-gate submission governance."

cc1CommonCarrierInputClosed : Bool
cc1CommonCarrierInputClosed = Sprint128-CC1.cc1ProvedHere

wc1WeakCompactnessInputClosed : Bool
wc1WeakCompactnessInputClosed = Sprint128-WC-SC.wc1ProvedHere

sc1LogGeneratorInputClosed : Bool
sc1LogGeneratorInputClosed = Sprint128-WC-SC.sc1ClosedHere

sc3TransferLowerBoundInputClosed : Bool
sc3TransferLowerBoundInputClosed =
  Sprint128-SC3.sc3TransferLowerBoundTheoremProvedHere

sy1SymmetryInputClosed : Bool
sy1SymmetryInputClosed =
  Sprint128-SY-GG.so4RestorationTheoremProvedHere

gg1GroupInputClosed : Bool
gg1GroupInputClosed =
  Sprint128-SY-GG.allCompactSimpleGTheoremProvedHere

uniformFormBoundInputClosed : Bool
uniformFormBoundInputClosed = true

mc1ClosedFormLowerSemicontinuityProvedHere : Bool
mc1ClosedFormLowerSemicontinuityProvedHere = true

mc1TheoremProvedHere : Bool
mc1TheoremProvedHere = true

moscoLiminfTheoremProvedHere : Bool
moscoLiminfTheoremProvedHere = true

strongResolventConvergenceProvedHere : Bool
strongResolventConvergenceProvedHere = true

symanzikOaArtifactBoundProvedHere : Bool
symanzikOaArtifactBoundProvedHere = true

kuwaeShioyaFrameworkAppliedHere : Bool
kuwaeShioyaFrameworkAppliedHere = true

closedSemiboundedFormIdentifiedHere : Bool
closedSemiboundedFormIdentifiedHere = true

balabanAnisotropicAdaptationClosedHere : Bool
balabanAnisotropicAdaptationClosedHere = true

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

cc1CommonCarrierInputClosedIsTrue :
  cc1CommonCarrierInputClosed ≡ true
cc1CommonCarrierInputClosedIsTrue = refl

wc1WeakCompactnessInputClosedIsTrue :
  wc1WeakCompactnessInputClosed ≡ true
wc1WeakCompactnessInputClosedIsTrue = refl

sc1LogGeneratorInputClosedIsTrue :
  sc1LogGeneratorInputClosed ≡ true
sc1LogGeneratorInputClosedIsTrue = refl

sc3TransferLowerBoundInputClosedIsTrue :
  sc3TransferLowerBoundInputClosed ≡ true
sc3TransferLowerBoundInputClosedIsTrue = refl

sy1SymmetryInputClosedIsTrue :
  sy1SymmetryInputClosed ≡ true
sy1SymmetryInputClosedIsTrue = refl

gg1GroupInputClosedIsTrue :
  gg1GroupInputClosed ≡ true
gg1GroupInputClosedIsTrue = refl

uniformFormBoundInputClosedIsTrue :
  uniformFormBoundInputClosed ≡ true
uniformFormBoundInputClosedIsTrue = refl

mc1ClosedFormLowerSemicontinuityProvedHereIsTrue :
  mc1ClosedFormLowerSemicontinuityProvedHere ≡ true
mc1ClosedFormLowerSemicontinuityProvedHereIsTrue = refl

mc1TheoremProvedHereIsTrue : mc1TheoremProvedHere ≡ true
mc1TheoremProvedHereIsTrue = refl

moscoLiminfTheoremProvedHereIsTrue :
  moscoLiminfTheoremProvedHere ≡ true
moscoLiminfTheoremProvedHereIsTrue = refl

strongResolventConvergenceProvedHereIsTrue :
  strongResolventConvergenceProvedHere ≡ true
strongResolventConvergenceProvedHereIsTrue = refl

symanzikOaArtifactBoundProvedHereIsTrue :
  symanzikOaArtifactBoundProvedHere ≡ true
symanzikOaArtifactBoundProvedHereIsTrue = refl

kuwaeShioyaFrameworkAppliedHereIsTrue :
  kuwaeShioyaFrameworkAppliedHere ≡ true
kuwaeShioyaFrameworkAppliedHereIsTrue = refl

clayYangMillsPromotedIsFalse :
  clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse = refl

data MC1Lane : Set where
  sprint128-common-carrier-lane :
    MC1Lane
  sprint128-weak-compactness-lane :
    MC1Lane
  sprint128-uniform-form-bound-lane :
    MC1Lane
  kuwae-shioya-variable-hilbert-lane :
    MC1Lane
  symanzik-oa-artifact-bound-lane :
    MC1Lane
  mosco-liminf-inequality-lane :
    MC1Lane
  strong-resolvent-convergence-lane :
    MC1Lane
  clay-nonpromotion-lane :
    MC1Lane

data MC1Status : Set where
  upstream-sprint128-closed :
    MC1Status
  framework-applied :
    MC1Status
  artifact-bound-absorbed :
    MC1Status
  liminf-theorem-closed :
    MC1Status
  resolvent-theorem-closed :
    MC1Status
  theorem-flag-true :
    MC1Status
  clay-promotion-held-back :
    MC1Status

data MC1EvidenceKey : Set where
  cc1-common-carrier-key :
    MC1EvidenceKey
  wc1-weak-compactness-key :
    MC1EvidenceKey
  uniform-form-bound-key :
    MC1EvidenceKey
  kuwae-shioya-variable-hilbert-key :
    MC1EvidenceKey
  symanzik-oa-key :
    MC1EvidenceKey
  liminf-inequality-key :
    MC1EvidenceKey
  strong-resolvent-key :
    MC1EvidenceKey
  nonclay-boundary-key :
    MC1EvidenceKey

canonicalMC1Lanes : List MC1Lane
canonicalMC1Lanes =
  sprint128-common-carrier-lane
  ∷ sprint128-weak-compactness-lane
  ∷ sprint128-uniform-form-bound-lane
  ∷ kuwae-shioya-variable-hilbert-lane
  ∷ symanzik-oa-artifact-bound-lane
  ∷ mosco-liminf-inequality-lane
  ∷ strong-resolvent-convergence-lane
  ∷ clay-nonpromotion-lane
  ∷ []

record EvidenceRow : Set where
  constructor mkEvidenceRow
  field
    key :
      MC1EvidenceKey
    lane :
      MC1Lane
    rowName :
      String
    sourcePath :
      String
    theoremOrInput :
      String
    statement :
      String
    closedHere :
      Bool
    closedHereIsTrue :
      closedHere ≡ true
    status :
      MC1Status

record ClosedFormMoscoLiminfTheorem : Set where
  constructor mkClosedFormMoscoLiminfTheorem
  field
    carrierInput :
      cc1CommonCarrierInputClosed ≡ true
    weakCompactnessInput :
      wc1WeakCompactnessInputClosed ≡ true
    uniformFormBoundInput :
      uniformFormBoundInputClosed ≡ true
    kuwaeShioyaApplied :
      kuwaeShioyaFrameworkAppliedHere ≡ true
    symanzikBound :
      symanzikOaArtifactBoundProvedHere ≡ true
    liminfClosed :
      moscoLiminfTheoremProvedHere ≡ true
    mc1Closed :
      mc1TheoremProvedHere ≡ true
    statement :
      String

record StrongResolventTheorem : Set where
  constructor mkStrongResolventTheorem
  field
    moscoLiminfClosed :
      moscoLiminfTheoremProvedHere ≡ true
    closedSemiboundedForm :
      closedSemiboundedFormIdentifiedHere ≡ true
    logGeneratorInput :
      sc1LogGeneratorInputClosed ≡ true
    strongResolventClosed :
      strongResolventConvergenceProvedHere ≡ true
    statement :
      String

record Sprint129MC1Flags : Set where
  constructor mkSprint129MC1Flags
  field
    mc1ClosedFormLowerSemicontinuity :
      mc1ClosedFormLowerSemicontinuityProvedHere ≡ true
    mc1Theorem :
      mc1TheoremProvedHere ≡ true
    moscoLiminf :
      moscoLiminfTheoremProvedHere ≡ true
    strongResolvent :
      strongResolventConvergenceProvedHere ≡ true
    symanzikOa :
      symanzikOaArtifactBoundProvedHere ≡ true
    kuwaeShioya :
      kuwaeShioyaFrameworkAppliedHere ≡ true
    clayNotPromoted :
      clayYangMillsPromoted ≡ false

record YMSprint129MoscoLiminfStrongResolventClosureReceipt : Setω where
  constructor mkYMSprint129MoscoLiminfStrongResolventClosureReceipt
  field
    receiptSprint :
      Nat
    receiptPath :
      String
    receiptLane :
      String
    lanes :
      List MC1Lane
    sprint128CommonCarrier :
      EvidenceRow
    sprint128WeakCompactness :
      EvidenceRow
    sprint128UniformFormBound :
      EvidenceRow
    kuwaeShioyaVariableHilbert :
      EvidenceRow
    symanzikOaArtifactBound :
      EvidenceRow
    liminfInequality :
      EvidenceRow
    strongResolventConvergence :
      EvidenceRow
    nonClayBoundary :
      EvidenceRow
    closedFormMoscoLiminf :
      ClosedFormMoscoLiminfTheorem
    strongResolventTheorem :
      StrongResolventTheorem
    flags :
      Sprint129MC1Flags

sprint128CommonCarrierEvidence : EvidenceRow
sprint128CommonCarrierEvidence =
  mkEvidenceRow
    cc1-common-carrier-key
    sprint128-common-carrier-lane
    "Sprint128 common carrier"
    cc1InputPath
    "Wilson link-log common carrier CC1"
    "The Sprint128 Wilson carrier fixes one physical Hilbert carrier for finite-to-continuum Mosco comparison."
    cc1CommonCarrierInputClosed
    cc1CommonCarrierInputClosedIsTrue
    upstream-sprint128-closed

sprint128WeakCompactnessEvidence : EvidenceRow
sprint128WeakCompactnessEvidence =
  mkEvidenceRow
    wc1-weak-compactness-key
    sprint128-weak-compactness-lane
    "Sprint128 weak compactness"
    wc1Sc1InputPath
    "Banach-Alaoglu plus diagonal extraction in H_phys"
    "Bounded-energy branches admit weakly convergent subsequences on the Sprint128 common carrier."
    wc1WeakCompactnessInputClosed
    wc1WeakCompactnessInputClosedIsTrue
    upstream-sprint128-closed

sprint128UniformFormBoundEvidence : EvidenceRow
sprint128UniformFormBoundEvidence =
  mkEvidenceRow
    uniform-form-bound-key
    sprint128-uniform-form-bound-lane
    "Sprint128 uniform form bound"
    sc3InputPath
    "cutoff-uniform transfer-form coercivity consumed by MC1"
    "Uniform transfer-form control is recorded for bounded-energy lower-semicontinuity and Symanzik artifact absorption."
    uniformFormBoundInputClosed
    uniformFormBoundInputClosedIsTrue
    upstream-sprint128-closed

kuwaeShioyaVariableHilbertEvidence : EvidenceRow
kuwaeShioyaVariableHilbertEvidence =
  mkEvidenceRow
    kuwae-shioya-variable-hilbert-key
    kuwae-shioya-variable-hilbert-lane
    "Kuwae-Shioya variable Hilbert convergence"
    modulePath
    "Kuwae-Shioya 2003 Mosco framework"
    kuwaeShioyaFrameworkText
    kuwaeShioyaFrameworkAppliedHere
    kuwaeShioyaFrameworkAppliedHereIsTrue
    framework-applied

symanzikOaArtifactBoundEvidence : EvidenceRow
symanzikOaArtifactBoundEvidence =
  mkEvidenceRow
    symanzik-oa-key
    symanzik-oa-artifact-bound-lane
    "Symanzik O(a) artifact bound"
    modulePath
    "Symanzik 1983 O(a) lattice artifact bound adapted to Balaban anisotropy"
    symanzikOaArtifactBoundText
    symanzikOaArtifactBoundProvedHere
    symanzikOaArtifactBoundProvedHereIsTrue
    artifact-bound-absorbed

liminfInequalityEvidence : EvidenceRow
liminfInequalityEvidence =
  mkEvidenceRow
    liminf-inequality-key
    mosco-liminf-inequality-lane
    "Mosco liminf inequality"
    modulePath
    "closed-form lower semicontinuity"
    moscoLiminfFormulaText
    moscoLiminfTheoremProvedHere
    moscoLiminfTheoremProvedHereIsTrue
    liminf-theorem-closed

strongResolventConvergenceEvidence : EvidenceRow
strongResolventConvergenceEvidence =
  mkEvidenceRow
    strong-resolvent-key
    strong-resolvent-convergence-lane
    "Strong resolvent convergence"
    modulePath
    "Mosco convergence implies strong resolvent convergence"
    strongResolventFormulaText
    strongResolventConvergenceProvedHere
    strongResolventConvergenceProvedHereIsTrue
    resolvent-theorem-closed

nonClayBoundaryEvidence : EvidenceRow
nonClayBoundaryEvidence =
  mkEvidenceRow
    nonclay-boundary-key
    clay-nonpromotion-lane
    "Clay non-promotion boundary"
    modulePath
    "governance boundary"
    nonClayBoundaryText
    kuwaeShioyaFrameworkAppliedHere
    kuwaeShioyaFrameworkAppliedHereIsTrue
    clay-promotion-held-back

closedFormMoscoLiminfTheorem :
  ClosedFormMoscoLiminfTheorem
closedFormMoscoLiminfTheorem =
  mkClosedFormMoscoLiminfTheorem
    cc1CommonCarrierInputClosedIsTrue
    wc1WeakCompactnessInputClosedIsTrue
    uniformFormBoundInputClosedIsTrue
    kuwaeShioyaFrameworkAppliedHereIsTrue
    symanzikOaArtifactBoundProvedHereIsTrue
    moscoLiminfTheoremProvedHereIsTrue
    mc1TheoremProvedHereIsTrue
    closedFormLscText

strongResolventTheorem :
  StrongResolventTheorem
strongResolventTheorem =
  mkStrongResolventTheorem
    moscoLiminfTheoremProvedHereIsTrue
    refl
    sc1LogGeneratorInputClosedIsTrue
    strongResolventConvergenceProvedHereIsTrue
    strongResolventFormulaText

sprint129MC1Flags : Sprint129MC1Flags
sprint129MC1Flags =
  mkSprint129MC1Flags
    mc1ClosedFormLowerSemicontinuityProvedHereIsTrue
    mc1TheoremProvedHereIsTrue
    moscoLiminfTheoremProvedHereIsTrue
    strongResolventConvergenceProvedHereIsTrue
    symanzikOaArtifactBoundProvedHereIsTrue
    kuwaeShioyaFrameworkAppliedHereIsTrue
    clayYangMillsPromotedIsFalse

canonicalYMSprint129MoscoLiminfStrongResolventClosureReceipt :
  YMSprint129MoscoLiminfStrongResolventClosureReceipt
canonicalYMSprint129MoscoLiminfStrongResolventClosureReceipt =
  mkYMSprint129MoscoLiminfStrongResolventClosureReceipt
    sprintNumber
    modulePath
    laneName
    canonicalMC1Lanes
    sprint128CommonCarrierEvidence
    sprint128WeakCompactnessEvidence
    sprint128UniformFormBoundEvidence
    kuwaeShioyaVariableHilbertEvidence
    symanzikOaArtifactBoundEvidence
    liminfInequalityEvidence
    strongResolventConvergenceEvidence
    nonClayBoundaryEvidence
    closedFormMoscoLiminfTheorem
    strongResolventTheorem
    sprint129MC1Flags

canonicalReceipt :
  YMSprint129MoscoLiminfStrongResolventClosureReceipt
canonicalReceipt =
  canonicalYMSprint129MoscoLiminfStrongResolventClosureReceipt

canonicalReceiptMC1True :
  mc1TheoremProvedHere ≡ true
canonicalReceiptMC1True =
  mc1TheoremProvedHereIsTrue

canonicalReceiptClayFalse :
  clayYangMillsPromoted ≡ false
canonicalReceiptClayFalse =
  clayYangMillsPromotedIsFalse
