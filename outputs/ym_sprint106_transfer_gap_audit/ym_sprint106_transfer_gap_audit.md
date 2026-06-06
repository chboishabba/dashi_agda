# YM Sprint 106 Transfer-Gap Audit

Route decision: `theorem still open`

## Scanned module surfaces

- sprint105: `DASHI/Physics/Closure/YMSprint105CompactSimpleGroupParameterTable.agda`
- sprint105: `DASHI/Physics/Closure/YMSprint105NonCircularMassGapBridge.agda`
- sprint105: `DASHI/Physics/Closure/YMSprint105OSToWightmanBridge.agda`
- sprint105: `DASHI/Physics/Closure/YMSprint105SymmetryRestorationContinuumLimit.agda`
- sprint106: `DASHI/Physics/Closure/YMSprint106EffectiveMassLowerBound.agda`
- sprint106: `DASHI/Physics/Closure/YMSprint106SymmetryAndGroupAuditAdvance.agda`
- sprint106: `DASHI/Physics/Closure/YMSprint106TransferGapLowerBoundAssembly.agda`
- sprint106: `DASHI/Physics/Closure/YMSprint106TransferMatrixGapComparison.agda`

## Transfer-gap target

- `gapTransferObligationFormula` in `DASHI/Physics/Closure/YMSprint105NonCircularMassGapBridge.agda`: `gap(T(a)) >= c * m_eff(a) * a`
- `gapTransferObligationStatus` in `DASHI/Physics/Closure/YMSprint105NonCircularMassGapBridge.agda`: `open-required-dashi-native-theorem`
- `transferGapOpenText` in `DASHI/Physics/Closure/YMSprint106EffectiveMassLowerBound.agda`: `Downstream/open: prove a DASHI-native transfer-gap comparison from WC3 effective mass to a physical Hamiltonian spectral gap.`
- `transferMatrixGapComparisonText` in `DASHI/Physics/Closure/YMSprint106TransferGapLowerBoundAssembly.agda`: `Transfer-matrix gap comparison: required DASHI-native comparison from WC3 effective mass to gap(T(a)); not proved in this assembly.`

## Effective-mass evidence

### `DASHI/Physics/Closure/YMSprint105NonCircularMassGapBridge.agda`
- `polymerWeightBoundFormula`: `|rho_k(gamma)| <= exp(-m_k * |gamma|)`
- `effectiveMassFormula`: `m_k = -log(18*C_local(a_k))`
- `effectiveMassPositivityCondition`: `18*C_local(a_k) < 1 implies m_k > 0`
- `wc3OnlyIndependenceStatement`: `The positivity m_k > 0 is read from WC3/Balaban polymer weights and does not use the desired continuum mass gap.`
- `wc3EffectiveMassPositivityRouteRecorded`: `true`
- `asymptoticFreedomScaleExternalInputRecorded`: `true`
- `nonCircularContinuumMassGapRouteComplete`: `false`
- `circularUseOfDesiredMassGap`: `false`

### `DASHI/Physics/Closure/YMSprint106EffectiveMassLowerBound.agda`
- `effectiveMassText`: `m_k = -log(18*C_local(a_k))`
- `effectiveMassPositivityText`: `18*C_local(a_k) < 1 implies m_k > 0`
- `effectiveMassLowerBoundText`: `The WC3 lower bound is m_eff(a_k) >= m_k, where m_k = -log(18*C_local(a_k)) > 0.`
- `wc3LowerBoundSurfaceRecorded`: `true`
- `effectiveMassUsesDesiredMassGap`: `false`
- `continuumMassGapClaimed`: `false`

### `DASHI/Physics/Closure/YMSprint106TransferGapLowerBoundAssembly.agda`
- `wc3EffectiveMassComponentText`: `WC3 effective mass positivity: Sprint105 records m_eff(a)>0 from Balaban/WC3 polymer weights without using the desired mass gap.`
- `effectiveMassDependencyPath`: `DASHI/Physics/Closure/YMSprint106EffectiveMassLowerBound.agda`
- `sprint106EffectiveMassModulePresent`: `true`

## Transfer-matrix comparison status

- Status: `theorem still open`
- Note: Explicit transfer-matrix comparison wording was detected in scanned surfaces.

## Theorem-proved flags

- `dashiNativeGapTransferTheoremProved` in `DASHI/Physics/Closure/YMSprint105NonCircularMassGapBridge.agda`: `false`
- `nonCircularContinuumMassGapRouteComplete` in `DASHI/Physics/Closure/YMSprint105NonCircularMassGapBridge.agda`: `false`
- `os1975Theorem1ProvedInRepo` in `DASHI/Physics/Closure/YMSprint105OSToWightmanBridge.agda`: `false`
- `wightmanConsequencesLocallyProvedInRepo` in `DASHI/Physics/Closure/YMSprint105OSToWightmanBridge.agda`: `false`
- `fullOSToWightmanRouteCompleteForClay` in `DASHI/Physics/Closure/YMSprint105OSToWightmanBridge.agda`: `false`
- `transferGapComparisonTheoremProved` in `DASHI/Physics/Closure/YMSprint106EffectiveMassLowerBound.agda`: `false`
- `continuumMassGapClaimed` in `DASHI/Physics/Closure/YMSprint106EffectiveMassLowerBound.agda`: `false`
- `theoremProved` in `DASHI/Physics/Closure/YMSprint106TransferGapLowerBoundAssembly.agda`: `false`
- `uniformContinuumLowerBoundProved` in `DASHI/Physics/Closure/YMSprint106TransferMatrixGapComparison.agda`: `false`
- `comparisonTargetLocallyProved` in `DASHI/Physics/Closure/YMSprint106TransferMatrixGapComparison.agda`: `false`

## Clay promotion flags

- `clayYangMillsPromoted` in `DASHI/Physics/Closure/YMSprint105CompactSimpleGroupParameterTable.agda`: `false`
- `clayYangMillsPromoted` in `DASHI/Physics/Closure/YMSprint105NonCircularMassGapBridge.agda`: `false`
- `clayYangMillsPromoted` in `DASHI/Physics/Closure/YMSprint105OSToWightmanBridge.agda`: `false`
- `fullOSToWightmanRouteCompleteForClay` in `DASHI/Physics/Closure/YMSprint105OSToWightmanBridge.agda`: `false`
- `clayYangMillsPromoted` in `DASHI/Physics/Closure/YMSprint105SymmetryRestorationContinuumLimit.agda`: `false`
- `clayYangMillsPromoted` in `DASHI/Physics/Closure/YMSprint106EffectiveMassLowerBound.agda`: `false`
- `clayYangMillsPromoted` in `DASHI/Physics/Closure/YMSprint106SymmetryAndGroupAuditAdvance.agda`: `false`
- `clayYangMillsPromoted` in `DASHI/Physics/Closure/YMSprint106TransferGapLowerBoundAssembly.agda`: `false`
- `transferGapLowerBoundPromoted` in `DASHI/Physics/Closure/YMSprint106TransferGapLowerBoundAssembly.agda`: `false`
- `clayYangMillsPromoted` in `DASHI/Physics/Closure/YMSprint106TransferMatrixGapComparison.agda`: `false`

## Fail-closed scan

- No Sprint 106 fail-closed condition was detected.
