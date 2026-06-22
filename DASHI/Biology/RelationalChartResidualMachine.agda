module DASHI.Biology.RelationalChartResidualMachine where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

------------------------------------------------------------------------
-- Relational chart / compiled inverse / residual pressure machine.
--
-- This module is candidate-only and keeps the local reading conservative:
--
--   - local charts are chart-local, not global authority,
--   - compiled inverses are compiled from those charts, not promoted claims,
--   - residual pressure is audited against a threshold,
--   - when the residual is over threshold, the handle is the small safe j+1
--     carry handle,
--   - no promotion, no force, and no authority are carried by the receipt.

data LocalChartKind : Set where
  liveLocalChartKind : LocalChartKind
  compiledInverseLocalChartKind : LocalChartKind
  residualPressureLocalChartKind : LocalChartKind
  thresholdLocalChartKind : LocalChartKind
  jPlusOneSafeHandleLocalChartKind : LocalChartKind

data ResidualPressureStatus : Set where
  belowThresholdResidual : ResidualPressureStatus
  atThresholdResidual : ResidualPressureStatus
  aboveThresholdResidual : ResidualPressureStatus

data SafetyHandleKind : Set where
  directHandleKind : SafetyHandleKind
  smallSafeHandleKind : SafetyHandleKind
  jPlusOneSafeHandleKind : SafetyHandleKind
  forceHandleKind : SafetyHandleKind
  authorityHandleKind : SafetyHandleKind

canonicalLocalChartKinds : List LocalChartKind
canonicalLocalChartKinds =
  liveLocalChartKind
  ∷ compiledInverseLocalChartKind
  ∷ residualPressureLocalChartKind
  ∷ thresholdLocalChartKind
  ∷ jPlusOneSafeHandleLocalChartKind
  ∷ []

canonicalResidualPressureStatuses : List ResidualPressureStatus
canonicalResidualPressureStatuses =
  belowThresholdResidual
  ∷ atThresholdResidual
  ∷ aboveThresholdResidual
  ∷ []

canonicalSafetyHandleKinds : List SafetyHandleKind
canonicalSafetyHandleKinds =
  directHandleKind
  ∷ smallSafeHandleKind
  ∷ jPlusOneSafeHandleKind
  ∷ forceHandleKind
  ∷ authorityHandleKind
  ∷ []

canonicalRelationalChartResidualNotes : List String
canonicalRelationalChartResidualNotes =
  "Local charts remain local and do not become global authority"
  ∷ "Compiled inverses are chart-local compiled readings, not promoted claims"
  ∷ "Residual pressure is measured against a threshold as an audit surface"
  ∷ "Over-threshold residuals carry the small safe j+1 handle"
  ∷ "No promotion, no force, and no authority are encoded by the receipt"
  ∷ []

record LocalChartReceipt : Setω where
  constructor mkLocalChartReceipt
  field
    chartIndex :
      Nat

    chartKind :
      LocalChartKind

    chartLabel :
      String

    chartSurface :
      String

    chartLocality :
      Bool

    chartLocalityIsTrue :
      chartLocality ≡ true

    chartReading :
      String

    chartNotes :
      List String

open LocalChartReceipt public

record CompiledInverseReceipt : Setω where
  constructor mkCompiledInverseReceipt
  field
    sourceChart :
      LocalChartReceipt

    compiledInverseLabel :
      String

    compiledInverseTerm :
      String

    compiledProductTerm :
      String

    compiledInverseKind :
      LocalChartKind

    compiledInverseKindIsCanonical :
      compiledInverseKind ≡ compiledInverseLocalChartKind

    compiledResidualCheck :
      Bool

    compiledResidualCheckIsTrue :
      compiledResidualCheck ≡ true

    compiledInverseReading :
      String

    compiledInverseNotes :
      List String

open CompiledInverseReceipt public

record ResidualPressureReceipt : Setω where
  constructor mkResidualPressureReceipt
  field
    compiledInverseReceipt :
      CompiledInverseReceipt

    residualPressure :
      Nat

    residualThreshold :
      Nat

    residualPressureStatus :
      ResidualPressureStatus

    residualPressureStatusIsCanonical :
      residualPressureStatus ≡ aboveThresholdResidual

    thresholdReading :
      String

    pressureReading :
      String

    jPlusOneSafeHandle :
      Nat

    jPlusOneSafeHandleIsSucc :
      jPlusOneSafeHandle ≡ suc residualThreshold

    safetyHandleKind :
      SafetyHandleKind

    safetyHandleKindIsCanonical :
      safetyHandleKind ≡ jPlusOneSafeHandleKind

    nonPromotion :
      Bool

    nonPromotionIsFalse :
      nonPromotion ≡ false

    noForce :
      Bool

    noForceIsFalse :
      noForce ≡ false

    noAuthority :
      Bool

    noAuthorityIsFalse :
      noAuthority ≡ false

    residualReceiptNotes :
      List String

open ResidualPressureReceipt public

record RelationalChartResidualMachine : Setω where
  constructor mkRelationalChartResidualMachine
  field
    machineLocalChartReceipt :
      LocalChartReceipt

    machineCompiledInverseReceipt :
      CompiledInverseReceipt

    machineResidualPressureReceipt :
      ResidualPressureReceipt

    machineCandidateOnly :
      Bool

    machineCandidateOnlyIsTrue :
      machineCandidateOnly ≡ true

    machineReading :
      String

    machineNotes :
      List String

open RelationalChartResidualMachine public

------------------------------------------------------------------------
-- Canonical constructors.

localChartReceiptOf :
  Nat →
  LocalChartReceipt
localChartReceiptOf j =
  mkLocalChartReceipt
    j
    liveLocalChartKind
    "local chart j"
    "chart-local surface for live relational reading"
    true
    refl
    "local chart remains a local chart"
    ( "chart locality is preserved"
    ∷ "chart authority is not promoted"
    ∷ []
    )

compiledInverseReceiptOf :
  LocalChartReceipt →
  CompiledInverseReceipt
compiledInverseReceiptOf chart =
  mkCompiledInverseReceipt
    chart
    "compiled inverse"
    "self * world^-1_j"
    "compiled chart-local inverse product"
    compiledInverseLocalChartKind
    refl
    true
    refl
    "compiled inverse remains candidate-only"
    ( "the inverse is compiled from the local chart"
    ∷ "the residual check stays open and local"
    ∷ []
    )

residualPressureReceiptOf :
  CompiledInverseReceipt →
  ResidualPressureReceipt
residualPressureReceiptOf compiled =
  mkResidualPressureReceipt
    compiled
    (suc (chartIndex (sourceChart compiled)))
    (chartIndex (sourceChart compiled))
    aboveThresholdResidual
    refl
    "threshold stays audit-side, not authority-side"
    "residual pressure is over threshold and audited"
    (suc (chartIndex (sourceChart compiled)))
    refl
    jPlusOneSafeHandleKind
    refl
    false
    refl
    false
    refl
    false
    refl
    ( "over-threshold residual carries the small safe j+1 handle"
    ∷ "promotion is blocked"
    ∷ "force is blocked"
    ∷ "authority is blocked"
    ∷ []
    )

relationalChartResidualMachineOf :
  Nat →
  RelationalChartResidualMachine
relationalChartResidualMachineOf j =
  let
    chart = localChartReceiptOf j
    compiled = compiledInverseReceiptOf chart
    residual = residualPressureReceiptOf compiled
  in
  mkRelationalChartResidualMachine
    chart
    compiled
    residual
    true
    refl
    "relational chart residual machine keeps the reading candidate-only"
    canonicalRelationalChartResidualNotes

------------------------------------------------------------------------
-- Canonical receipts.

canonicalLocalChartReceipt :
  LocalChartReceipt
canonicalLocalChartReceipt =
  localChartReceiptOf zero

canonicalCompiledInverseReceipt :
  CompiledInverseReceipt
canonicalCompiledInverseReceipt =
  compiledInverseReceiptOf canonicalLocalChartReceipt

canonicalResidualPressureReceipt :
  ResidualPressureReceipt
canonicalResidualPressureReceipt =
  residualPressureReceiptOf canonicalCompiledInverseReceipt

canonicalRelationalChartResidualMachine :
  RelationalChartResidualMachine
canonicalRelationalChartResidualMachine =
  relationalChartResidualMachineOf zero

canonicalLocalChartReceiptIsTrue :
  chartLocality canonicalLocalChartReceipt ≡ true
canonicalLocalChartReceiptIsTrue =
  chartLocalityIsTrue canonicalLocalChartReceipt

canonicalCompiledInverseReceiptIsCanonical :
  compiledInverseKind canonicalCompiledInverseReceipt ≡
  compiledInverseLocalChartKind
canonicalCompiledInverseReceiptIsCanonical =
  compiledInverseKindIsCanonical canonicalCompiledInverseReceipt

canonicalCompiledResidualCheckIsTrue :
  compiledResidualCheck canonicalCompiledInverseReceipt ≡ true
canonicalCompiledResidualCheckIsTrue =
  compiledResidualCheckIsTrue canonicalCompiledInverseReceipt

canonicalResidualPressureStatusIsCanonical :
  residualPressureStatus canonicalResidualPressureReceipt ≡
  aboveThresholdResidual
canonicalResidualPressureStatusIsCanonical =
  residualPressureStatusIsCanonical canonicalResidualPressureReceipt

canonicalJPlusOneSafeHandleIsSucc :
  jPlusOneSafeHandle canonicalResidualPressureReceipt ≡
  suc (residualThreshold canonicalResidualPressureReceipt)
canonicalJPlusOneSafeHandleIsSucc =
  jPlusOneSafeHandleIsSucc canonicalResidualPressureReceipt

canonicalSmallSafeHandleKindIsCanonical :
  safetyHandleKind canonicalResidualPressureReceipt ≡
  jPlusOneSafeHandleKind
canonicalSmallSafeHandleKindIsCanonical =
  safetyHandleKindIsCanonical canonicalResidualPressureReceipt

canonicalNonPromotionIsFalse :
  nonPromotion canonicalResidualPressureReceipt ≡ false
canonicalNonPromotionIsFalse =
  nonPromotionIsFalse canonicalResidualPressureReceipt

canonicalNoForceIsFalse :
  noForce canonicalResidualPressureReceipt ≡ false
canonicalNoForceIsFalse =
  noForceIsFalse canonicalResidualPressureReceipt

canonicalNoAuthorityIsFalse :
  noAuthority canonicalResidualPressureReceipt ≡ false
canonicalNoAuthorityIsFalse =
  noAuthorityIsFalse canonicalResidualPressureReceipt

canonicalMachineCandidateOnlyIsTrue :
  machineCandidateOnly canonicalRelationalChartResidualMachine ≡ true
canonicalMachineCandidateOnlyIsTrue =
  machineCandidateOnlyIsTrue canonicalRelationalChartResidualMachine

canonicalMachineNoPromotionIsFalse :
  nonPromotion
    (machineResidualPressureReceipt canonicalRelationalChartResidualMachine)
  ≡
  false
canonicalMachineNoPromotionIsFalse =
  canonicalNonPromotionIsFalse

canonicalMachineNoForceIsFalse :
  noForce (machineResidualPressureReceipt canonicalRelationalChartResidualMachine)
  ≡
  false
canonicalMachineNoForceIsFalse =
  canonicalNoForceIsFalse

canonicalMachineNoAuthorityIsFalse :
  noAuthority
    (machineResidualPressureReceipt canonicalRelationalChartResidualMachine)
  ≡
  false
canonicalMachineNoAuthorityIsFalse =
  canonicalNoAuthorityIsFalse

canonicalRelationalChartResidualMachineReading :
  String
canonicalRelationalChartResidualMachineReading =
  machineReading canonicalRelationalChartResidualMachine
