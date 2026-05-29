# Paper 8 Receipt Index

Date: `2026-05-29`
Status: Paper 8 submission support; non-promoting; fail-closed

This index is the source map for Paper 8.  It records which formal receipts can be cited, what each receipt contributes, and which promotion bit must remain false.  The paper claim is a governance and tower-composition claim, not a solved Millennium, GR, QFT, or Standard Model theorem.

## Draft Body Receipt Anchors

Every receipt cited in the Paper 8 draft body is anchored here by Agda module path and identifier.

| Module path | Agda identifier | Paper role |
| --- | --- | --- |
| `DASHI.Physics.Closure.MillenniumTowerSchemaReceipt` | `MillenniumTowerSchemaReceipt`, `canonicalMillenniumTowerSchemaReceipt` | Shared `T0..T4` tower schema; keeps Clay, full-unification, and terminal promotion bits false. |
| `DASHI.Physics.Closure.MillenniumTowerSchemaReceipt` | `canonicalMillenniumTowerSchemaReceiptStagesAreCanonical`, `canonicalMillenniumTowerContinuumObligationStillOpen`, `canonicalMillenniumTowerAuthorityBoundaryStillClosed`, `canonicalMillenniumTowerPromotionToClayStillFalse`, `canonicalMillenniumTowerFullUnificationStillFalse`, `canonicalMillenniumTowerTerminalPromotionStillFalse` | Schema-level theorem witnesses cited by the draft. |
| `DASHI.Physics.Closure.MillenniumTowerInstancesReceipt` | `MillenniumTowerInstancesReceipt`, `canonicalMillenniumTowerInstancesReceipt` | Aggregate YM, NS, GR/cosmology, and DHR/SM lane mappings into the shared tower schema. |
| `DASHI.Physics.Closure.MillenniumTowerInstancesReceipt` | `MillenniumTowerInstancesReceipt.dhrStandardModelLaneReceipt` | Aggregate DHR/SM lane field named in the theorem statement. |
| `DASHI.Physics.Closure.MillenniumTowerInstancesReceipt` | `millenniumTowerKeepsYangMillsClayFalse`, `millenniumTowerKeepsNavierStokesRegularityFalse`, `millenniumTowerKeepsGRCosmologyPromotionFalse`, `millenniumTowerKeepsFullGDHREqualsGSMFalse` | Fully qualified fail-closed lemmas cited by the draft's receipt-audit paragraph. |
| `DASHI.Physics.Closure.MillenniumTowerYangMillsInstanceReceipt` | `MillenniumTowerYangMillsInstanceReceipt`, `canonicalMillenniumTowerYangMillsInstanceReceipt`, `millenniumTowerYangMillsNoClayPromotion`, `millenniumTowerYangMillsFieldEquationNoPromotion`, `millenniumTowerYangMillsMassGapNoPromotion` | Split Yang-Mills tower instance; no Clay, field-equation, or continuum mass-gap promotion. |
| `DASHI.Physics.Closure.MillenniumTowerYangMillsInstanceReceipt` | `MillenniumTowerYangMillsInstanceReceipt.finiteFieldEquationReceipt`, `MillenniumTowerYangMillsInstanceReceipt.yangMillsFieldEquationReceipt`, `MillenniumTowerYangMillsInstanceReceipt.yangMillsMassGapBoundaryReceipt` | Positive split Yang-Mills receipt-backed fields named in the theorem statement. |
| `DASHI.Physics.Closure.MillenniumTowerNavierStokesInstanceReceipt` | `MillenniumTowerNavierStokesInstanceReceipt`, `canonicalMillenniumTowerNavierStokesInstanceReceipt` | Split Navier-Stokes tower instance; `millenniumTowerNavierStokesNoClayPromotion` records no Clay regularity promotion. |
| `DASHI.Physics.Closure.ClayMillenniumClosureTargetReceipt` | `CarrierOSPositivityAndWightmanTargetReceipt`, `canonicalCarrierOSPositivityAndWightmanTargetReceipt`, `clayMillenniumClosureTargetKeepsYangMillsFalse` | Exact Yang-Mills closing-target receipt; OS positivity, uniform mass gap, interacting continuum limit, Wightman reconstruction, and Clay closure remain false. |
| `DASHI.Physics.Closure.CarrierFactorVecInjectivityOSPositivity` | `CarrierFactorVecInjectivityOSPositivityReceipt`, `canonicalCarrierFactorVecInjectivityOSPositivityReceipt`, `carrierOSPositivityInhabited`, `carrierOSPositivityDoesNotPromoteYangMillsMassGap`, `carrierOSPositivityDoesNotPromoteClayYangMills` | Finite FactorVec injectivity-to-OS receipt; OS reconstruction is citation authority and Wightman, mass-gap, and Clay promotion remain false. |
| `DASHI.Physics.Closure.ClayMillenniumClosureTargetReceipt` | `CarrierBKMControlTargetReceipt`, `canonicalCarrierBKMControlTargetReceipt`, `clayMillenniumClosureTargetKeepsNavierStokesFalse` | Exact Navier-Stokes closing-target receipt; uniform enstrophy/BKM control, continuum BKM passage, and Clay closure remain false. |
| `DASHI.Physics.Closure.UltrametricSobolevUniformBound` | `UltrametricSobolevUniformBoundReceipt`, `canonicalUltrametricSobolevUniformBoundReceipt`, `canonicalUltrametricSobolevUniformBoundedTrue`, `ultrametricSobolevDoesNotPromoteContinuumBKM`, `ultrametricSobolevDoesNotPromoteClayNavierStokes` | Taibleson/BKM citation-authority surface for a depth-independent ultrametric Sobolev bound; continuum BKM and Clay NS promotion remain false. |
| `DASHI.Physics.Closure.MillenniumTowerGRInstanceReceipt` | `MillenniumTowerGRInstanceReceipt`, `canonicalMillenniumTowerGRInstanceReceipt` | Split GR/cosmology tower instance; `millenniumTowerGRNoPromotion` records no GR/cosmology promotion. |
| `DASHI.Physics.Closure.MillenniumTowerGRInstanceReceipt` | `MillenniumTowerGRInstanceReceipt.friedmannInstabilitySaddle` | GR/cosmology split-instance field named in the theorem statement. |
| `DASHI.Physics.Closure.MillenniumTowerDHRSMInstanceReceipt` | `MillenniumTowerDHRSMInstanceReceipt`, `canonicalMillenniumTowerDHRSMInstanceReceipt` | Split DHR/SM tower instance; `millenniumTowerDHRSMNoFullPromotion` records no full `G_DHR = G_SM` promotion. |
| `DASHI.Physics.Closure.BalabanRGMassGapReceiptSurface` | `BalabanRGMassGapReceiptSurface`, `canonicalBalabanRGMassGapReceiptSurface` | Finite-depth and local finite-carrier Yang-Mills mass-gap evidence surface. |
| `DASHI.Physics.Closure.BalabanRGMassGapReceiptSurface` | `BalabanRGMassGapReceiptSurface.finiteDepthProObjectReceipt`, `BalabanRGMassGapReceiptSurface.depthIndexedVsContinuumStatus`, `BalabanRGMassGapReceiptSurface.quantifierExchangeReceipt` | Balaban surface fields cited in the Yang-Mills finite-depth discussion. |
| `DASHI.Physics.Closure.ColimitGapLiftOnHamiltonian` | `ColimitGapLiftOnHamiltonianReceipt`, `canonicalColimitGapLiftOnHamiltonianReceipt`, `ColimitHamiltonianGapThreadReceipt`, `canonicalColimitHamiltonianGapThreadReceipt` | Yang-Mills finite-to-colimit/Hamiltonian lift thread; `colimitHamiltonianGapThreadKeepsClayFalse` keeps Clay promotion false. |
| `DASHI.Physics.Closure.ContinuumClayMassGapReceiptObligation` | `ContinuumClayMassGapReceiptObligation`, `canonicalContinuumClayMassGapReceiptObligation` | Clay-facing Yang-Mills required components and open obligations. |
| `DASHI.Physics.Closure.ContinuumClayMassGapReceiptObligation` | `ContinuumClayMassGapReceiptObligation.continuumClayMassGapPromoted`, `ContinuumClayMassGapReceiptObligation.continuumClayMassGapPromotedIsFalse`, `continuumClayMassGapReceiptObligationClayFalse` | Fields and lemma cited by the draft to show the Yang-Mills Clay promotion bit remains false. |
| `DASHI.Physics.Closure.YangMillsMassGapBoundary` | `YangMillsMassGapBoundaryReceipt`, `canonicalYangMillsMassGapBoundaryReceipt` | Finite-depth versus continuum mass-gap authority boundary. |
| `DASHI.Physics.Closure.NavierStokesWeakSolutionInterface` | `NavierStokesWeakSolutionInterfaceReceipt`, `canonicalNavierStokesWeakSolutionInterfaceReceipt` | Finite carrier weak formulation, divergence-free interface, Leray projection, and Leray-Hopf weak-solution interface. |
| `DASHI.Physics.Closure.NavierStokesRegularityTowerReceipt` | `NavierStokesRegularityTowerReceipt`, `canonicalNavierStokesRegularityTowerReceipt` | Finite-depth NS energy, enstrophy, vorticity, BKM rungs, and regularity blockers. |
| `DASHI.Physics.Closure.NavierStokesRegularityTowerReceipt` | `ContinuumRegularityObligation`, `canonicalContinuumRegularityObligation` | Explicit continuum smoothness obligation cited in the NS tower discussion. |
| `DASHI.Physics.Closure.NavierStokesRegularityTowerReceipt` | `NavierStokesRegularityTowerReceipt.continuumClayNavierStokesPromoted`, `NavierStokesRegularityTowerReceipt.continuumClayNavierStokesPromotedIsFalse` | Fields cited by the draft to show Clay regularity promotion remains false. |
| `DASHI.Physics.Closure.ContractedBianchiMatterClosure` | `ContractedBianchiMatterClosureReceipt`, `canonicalContractedBianchiMatterClosureReceipt` | Gate 4 finite sourced-Einstein and Wald/GR precondition wiring. |
| `DASHI.Physics.Closure.WaldGRAuthorityReceipt` | `WaldGRAuthorityReceipt`, `canonicalWaldGRAuthorityReceipt` | Wald continuum GR authority boundary; sourced-Einstein promotion remains false. |
| `DASHI.Physics.Closure.FriedmannInstabilitySaddleReceipt` | `FriedmannInstabilitySaddleReceipt`, `canonicalFriedmannInstabilitySaddleReceipt` | Temple-Alexander-Vogler Friedmann instability authority contact; cosmology promotion remains false. |
| `DASHI.Physics.Closure.FriedmannInstabilitySaddleReceipt` | `friedmannInstabilityDoesNotRemoveDarkEnergyHere`, `friedmannInstabilityDoesNotFalsifyLCDMHere` | Fully qualified Friedmann fail-closed lemmas cited by the draft. |
| `DASHI.Physics.QFT.DHRGaugeReceiptSurface` | `DHRFormalismPrimitiveReceipt`, `canonicalDHRFormalismPrimitiveReceipt` | DHR/DR primitive and authority surfaces. |
| `DASHI.Physics.QFT.DHRTensorDualGroupReconstruction` | `DHRTensorDualGroupReconstructionReceipt`, `canonicalDHRTensorDualGroupReconstructionReceipt` | DHR tensor/dual/Tannaka reconstruction target and blockers. |
| `DASHI.Physics.QFT.FinitePrimeLaneDHRSMCompatibilityLedger` | `FinitePrimeLaneDHRSMCompatibilityLedger`, `canonicalFinitePrimeLaneDHRSMCompatibilityLedger` | Finite `p2`/`p3`/`p5` DHR-SM compatibility ledger. |
| `DASHI.Physics.QFT.ConditionalGDHRSMPromotionReceipt` | `ConditionalGDHRSMPromotionReceipt`, `canonicalConditionalGDHRSMPromotionReceipt` | Conditional DHR/SM promotion status; unconditional reconstruction remains false. |
| `DASHI.Physics.QFT.ConditionalGDHRSMPromotionReceipt` | `canonicalConditionalGDHRSMPromotionNoFullTheorem`, `fullGDHRSMPromotionTheoremImpossibleHere` | Fully qualified no-full-theorem witnesses cited by the draft. |
| `DASHI.Physics.Closure.CrossGateConsistency` | `Gate8CrossGateConsistencyReceipt.gate8PromotableIsFalse`, `canonicalGate8CrossGateConsistencyReceipt` | Gate 8 cross-gate consistency receipt cited to show terminal promotion remains blocked. |
| `DASHI.Physics.Closure.HEPDataResidualBridgeAuthorityGate` | `HEPDataResidualBridgeAuthorityGate`, `canonicalHEPDataResidualBridgeAuthorityGate` | Residual empirical bridge as receipt filter, blocking W3/W4/W5/W8 promotion. |
| `DASHI.Physics.Closure.PenguinDecayC9C10P5PrimePredictionTargetReceipt` | `C9C10P5PrimePredictionTargetReceipt`, `canonicalC9C10P5PrimePredictionTargetReceipt` | P5' prediction target frontier. |
| `DASHI.Physics.Closure.PenguinDecayCarrierDerivedC9ConstraintTargetReceipt` | `PenguinDecayCarrierDerivedC9ConstraintTargetReceipt`, `canonicalPenguinDecayCarrierDerivedC9ConstraintTargetReceipt` | Carrier-derived C9 constraint target; empirical promotion remains false. |
| `DASHI.Physics.Closure.CKMPredictionFrontierReceipt` | `CKMPredictionFrontierReceipt`, `canonicalCKMPredictionFrontierReceipt` | CKM/Yukawa prediction frontier, comparison targets only. |
| `DASHI.Physics.Closure.CarrierYukawaRatioTargetReceipt` | `CarrierYukawaRatioTargetReceipt`, `canonicalCarrierYukawaRatioTargetReceipt` | Yukawa ratio target bookkeeping; physical ratio promotion remains false. |
| `DASHI.Physics.Closure.CabibboAngleCarrierReceipt` | `CabibboAngleCarrierReceipt`, `canonicalCabibboAngleCarrierReceipt` | Cabibbo-angle target form and alpha diagnostics; physical CKM and accepted common-alpha promotion remain false. |
| `DASHI.Physics.Moonshine.ModularJInvariantAlphaReceipt` | `ModularJInvariantAlphaReceipt`, `canonicalModularJInvariantAlphaReceipt`, `modularJInvariantAlphaReceiptKeepsDerivationClosed` | Modular-j/Eisenstein alpha target; records `j(i)=1728` and `j(rho)=0`, while alpha-from-j and accepted alpha promotion remain false. |
| `DASHI.Physics.Moonshine.MonsterOrderDepthBoundReceipt` | `MonsterOrderDepthBoundReceipt`, `canonicalMonsterOrderDepthBoundReceipt`, `monsterOrderDepthBoundProvedIsFalse`, `monsterOrderPrimeSetForcedFromFirstPrinciplesIsFalse` | Monster-order exponent depth-bound target; conjectural only, with no first-principles prime forcing or terminal promotion. |

## Shared Tower Schema

| Lane | Primary receipts | Paper role | Closed boundary |
| --- | --- | --- | --- |
| Tower schema | `DASHI.Physics.Closure.MillenniumTowerSchemaReceipt`, `DASHI.Physics.Closure.MillenniumTowerInstancesReceipt`, `DASHI.Physics.Closure.MillenniumTowerYangMillsInstanceReceipt`, `DASHI.Physics.Closure.MillenniumTowerNavierStokesInstanceReceipt`, `DASHI.Physics.Closure.MillenniumTowerGRInstanceReceipt`, `DASHI.Physics.Closure.MillenniumTowerDHRSMInstanceReceipt` | Common `T0..T4` schema plus current YM, NS, GR, and DHR/SM instance mappings. | `promotionToClay = false`, `fullUnification = false`, `terminalPromotion = false`. |
| Gate 8 composition | `DASHI.Physics.Closure.CrossGateCompositionTheorems`, `DASHI.Physics.Closure.CrossGateHamiltonianCompatibilityReceipt` | Shows how Stone/GNS, YM Hamiltonian, DHR sector, and carrier-functor lanes are wired as compatibility receipts. | No single physical Hamiltonian is identified across Stone, YM, and DHR representations. |

## YM And NS Millennium Lanes

| Lane | Primary receipts | Paper role | Closed boundary |
| --- | --- | --- | --- |
| Yang-Mills mass gap | `DASHI.Physics.Closure.BalabanRGMassGapReceiptSurface`, `DASHI.Physics.Closure.YangMillsMassGapBoundary`, `DASHI.Physics.Closure.ColimitGapLiftOnHamiltonian`, `DASHI.Physics.Closure.ContinuumClayMassGapReceiptObligation`, `DASHI.Physics.Closure.ClayMillenniumClosureTargetReceipt`, `DASHI.Physics.Closure.CarrierFactorVecInjectivityOSPositivity`, `DASHI.Physics.Boundaries.YMConstructive5DProofReceipt`, `DASHI.Physics.Boundaries.TopologicalMassGapInterpretation`, `DASHI.Physics.Boundaries.GribovResolutionAuthorityReceipt` | Finite-depth and authority-bound YM tower with a finite FactorVec-injectivity-to-OS receipt plus explicit uniform-gap, Wightman, and Clay-facing blockers. | No uniform depth-independent mass gap, no continuum constructive YM theory, no Wightman reconstruction, no Clay mass-gap promotion. |
| Navier-Stokes regularity | `DASHI.Physics.Closure.NavierStokesWeakSolutionInterface`, `DASHI.Physics.Closure.NavierStokesRegularityTowerReceipt`, `DASHI.Physics.Closure.ClayMillenniumClosureTargetReceipt`, `DASHI.Physics.Closure.UltrametricSobolevUniformBound` | Finite weak-solution, energy, enstrophy, vorticity, BKM-style rungs, and an ultrametric Sobolev citation-authority target. | No carrier-specialized full p-adic Sobolev proof, no continuum BKM passage, no continuum regularity lift, no blowup exclusion, no Clay regularity promotion. |

## GR, Hilbert/Stone, And DHR

| Lane | Primary receipts | Paper role | Closed boundary |
| --- | --- | --- | --- |
| GR / Gate 4 | `DASHI.Physics.Closure.WaldGRAuthorityReceipt`, `DASHI.Physics.Closure.FriedmannInstabilitySaddleReceipt`, `DASHI.Physics.Closure.ContractedBianchiMatterClosure`, `DASHI.Physics.Closure.GRDiscreteBianchiFiniteR` | Finite GR staging plus external Wald/Friedmann authority boundary. | No continuum sourced Einstein theorem, no cosmology promotion, no dark-energy or LCDM claim. |
| Hilbert / Stone / GNS | `DASHI.Physics.Closure.PhysicalHilbertColimitObligation`, `DASHI.Physics.Closure.StoneTheoremCarrierReceipt`, `DASHI.Physics.Closure.GNSCarrierQuotientReceipt`, `DASHI.Physics.Closure.TraversalGroupStrongContinuity` | Finite quotient Hilbert and one-point Stone data; GNS local-algebra quotient target. | No accepted infinite-depth physical Hilbert completion, no self-adjoint physical colimit generator, no GNS Hilbert space promotion. |
| DHR / Gate 6 | `DASHI.Physics.QFT.DHRGaugeReceiptSurface`, `DASHI.Physics.QFT.DHRTensorDualGroupReconstruction`, `DASHI.Physics.QFT.DHROriginalPaperAuthorityReceipt`, `DASHI.Physics.QFT.FinitePrimeLaneDHRSMCompatibilityLedger`, `DASHI.Physics.QFT.FinitePrimeLaneConjugateDualReceipts`, `DASHI.Physics.QFT.TannakaKreinFibreFunctorReceipt`, `DASHI.Physics.QFT.ConditionalGDHRSMPromotionReceipt` | Conditional DHR/DR and Tannaka-Krein reconstruction surface for the finite `p2/p3/p5` lane package. | No arbitrary-sector DHR theorem, no internal compact group construction, no `G_DHR = G_SM`, no full SM reconstruction. |

## Empirical And Matter Lanes

| Lane | Primary receipts | Paper role | Closed boundary |
| --- | --- | --- | --- |
| P5 prime / Gate 5 empirical contact | `DASHI.Physics.Closure.HEPDataResidualBridgeAuthorityGate`, `DASHI.Physics.Closure.PenguinDecayLHCbChecksumAcceptedResidualReceipt`, `DASHI.Physics.Closure.PenguinDecayC9C10P5PrimePredictionTargetReceipt`, `DASHI.Physics.Closure.PenguinDecayCarrierDerivedC9ConstraintTargetReceipt`, `DASHI.Physics.Closure.PenguinDecayResidualComparisonLaw`, `DASHI.Physics.Closure.PenguinDecaySMBaselineAuthority`, `DASHI.Physics.Closure.PenguinDecayWilsonCoefficientAuthority` | Digest-bound P5 prime residual target and C9/C10 comparison lane. | No full covariance authority, no accepted residual theorem, no new-physics promotion. |
| Yukawa / CKM / Gate 7 | `DASHI.Physics.Closure.YukawaFromCarrier`, `DASHI.Physics.Closure.CKMCarrierDerived`, `DASHI.Physics.Closure.CKMPredictionFrontierReceipt`, `DASHI.Physics.Closure.CKMVusCarrierPredictionTargetReceipt`, `DASHI.Physics.Closure.CarrierYukawaRatioTargetReceipt`, `DASHI.Physics.Closure.CabibboAngleCarrierReceipt`, `DASHI.Physics.Closure.YukawaDHRIntertwinerCompatibility`, `DASHI.Physics.Moonshine.ModularJInvariantAlphaReceipt`, `DASHI.Physics.Moonshine.MonsterOrderDepthBoundReceipt` | Carrier-side Yukawa, CKM, ratio, Cabibbo, DHR-intertwiner, and modular-j/Monster-depth diagnostics. | No accepted common alpha, no alpha-from-j derivation, no Monster-depth proof, no physical CKM matrix, no exact PDG match; carrier-natural `g12 = 1` gives `|V_us| = 0.041` versus PDG-sized `0.225`, so deriving `g12` from DHR sector data remains open. |

## Citation Rule

Paper 8 should cite each receipt as one of these statuses only:

- `inhabited finite receipt`: usable as current formal evidence inside the finite carrier scope.
- `authority boundary`: usable as literature or external theorem context without internal theorem import.
- `target receipt`: usable as a named comparison or promotion target.
- `obligation`: usable as a blocker list that prevents promotion.

No receipt in this index authorizes a solved Millennium problem, complete continuum GR/QFT construction, or full Standard Model reconstruction.
