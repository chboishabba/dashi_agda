module DASHI.Interop.SweetgrassCarrierSpine where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.PNFRoleVectorAlgebra as Role
import DASHI.Interop.SensibLawResidualLattice as Residual

------------------------------------------------------------------------
-- Sweetgrass / dialectical carrier spine.
--
-- This is a non-promoting crosswalk for the local braid, fabric, weave,
-- 3-6-9, BT-tree, BT-braid, p-adic, supervoxel, wave, Hecke/eigen,
-- j-invariant, monster/moonshine, fascistic, antifascistic, 15SSP, Tlurey,
-- triadic/nonary, ultrametric/adelic, Clifford/Bott/spinor/gauge, PDE/flow,
-- semantic/PNF/residual, claim/Wikidata, DNA/brain/biology/chemistry, and
-- category/functor/operator/lattice carrier surfaces.  Sweetgrass is recorded
-- as a braid/fabric motif with credit to Robin Wall Kimmerer / Braiding
-- Sweetgrass.
--
-- The spine is for NLP/PNF/ITIR integration: motifs become bounded carrier
-- vocabulary, role-vector projections, and evidence-only PredicatePNF atoms.
-- It does not assert that the domains are definitionally equal, and it does
-- not promote legal, cultural, metaphysical, physics, Wikidata, or Clay
-- authority.

sweetgrassAttribution : String
sweetgrassAttribution =
  "Sweetgrass braid/fabric attribution: Robin Wall Kimmerer / Braiding Sweetgrass"

data CarrierMotif : Set where
  motifSweetgrassBraidFabric : CarrierMotif
  motif369 : CarrierMotif
  motifCarry : CarrierMotif
  motifDialectic : CarrierMotif
  motifBraid : CarrierMotif
  motifBTTree : CarrierMotif
  motifBTBraid : CarrierMotif
  motifPAdic : CarrierMotif
  motifDecimalArchimedean : CarrierMotif
  motifSupervoxel : CarrierMotif
  motifThreadBraid : CarrierMotif
  motifLowOrderRegularFabric : CarrierMotif
  motifHighDimensionalHyperfabric : CarrierMotif
  motifFascisticContraction : CarrierMotif
  motifAntifascistInvertibility : CarrierMotif
  motifWaveTransport : CarrierMotif
  motifWeave : CarrierMotif
  motifKnot : CarrierMotif
  motifFifteenSSP : CarrierMotif
  motifHeckeEigen : CarrierMotif
  motifJInvariant : CarrierMotif
  motifMonsterMoonshine : CarrierMotif
  motifHighNPrimeCarrier : CarrierMotif
  motifTlureyTriadicNonary : CarrierMotif
  motifUltrametricAdelic : CarrierMotif
  motifCliffordBottSpinor : CarrierMotif
  motifGaugeYangMills : CarrierMotif
  motifNavierStokesFlow : CarrierMotif
  motifSemanticPNFResidual : CarrierMotif
  motifClaimWikidataLattice : CarrierMotif
  motifDNAGenomeChemistry : CarrierMotif
  motifBrainConnectomeSemantic : CarrierMotif
  motifBiologySensorimotor : CarrierMotif
  motifCategoryFunctorOperator : CarrierMotif
  motifLatticeQuotient : CarrierMotif

data CarrierAnchor : Set where
  anchorBase369 : CarrierAnchor
  anchorLocalDocs369 : CarrierAnchor
  anchorCarryMemory : CarrierAnchor
  anchorDialecticalDepth : CarrierAnchor
  anchorUnifiedCarryBraid : CarrierAnchor
  anchorBTBraidKP : CarrierAnchor
  anchorCarrierBraid : CarrierAnchor
  anchorPAdicMetric : CarrierAnchor
  anchorDecimalArchimedeanLane : CarrierAnchor
  anchorSupervoxelAdmissibility : CarrierAnchor
  anchorPrimeHeckeEigenMotif : CarrierAnchor
  anchorHeckeScan15 : CarrierAnchor
  anchorModularJInvariant : CarrierAnchor
  anchorMonsterMoonshineJDistribution : CarrierAnchor
  anchorMonsterMoonshineSSPQuotient : CarrierAnchor
  anchorFascisticSystem : CarrierAnchor
  anchorAntifascistSystem : CarrierAnchor
  anchorWaveTransport : CarrierAnchor
  anchorKnotWeaveCulture : CarrierAnchor
  anchorCarrierWeaveDefect : CarrierAnchor
  anchorMonsterSSP15 : CarrierAnchor
  anchorTlureyLogic : CarrierAnchor
  anchorUltrametricAdelicTransport : CarrierAnchor
  anchorCliffordBottSpinor : CarrierAnchor
  anchorGaugeYangMills : CarrierAnchor
  anchorNavierStokesFlow : CarrierAnchor
  anchorSemanticPNFResidual : CarrierAnchor
  anchorClaimWikidataLattice : CarrierAnchor
  anchorDNAGenomeChemistry : CarrierAnchor
  anchorBrainConnectomeSemantic : CarrierAnchor
  anchorBiologySensorimotor : CarrierAnchor
  anchorCategoryFunctorOperator : CarrierAnchor
  anchorLatticeQuotient : CarrierAnchor

data CarrierRole : Set where
  localStateRole : CarrierRole
  orientationRole : CarrierRole
  memoryRole : CarrierRole
  defectRole : CarrierRole
  pressureRole : CarrierRole
  admissibilityRole : CarrierRole
  transportRole : CarrierRole
  bindingRole : CarrierRole
  braidRole : CarrierRole
  threadRole : CarrierRole
  btBraidRole : CarrierRole
  fabricRole : CarrierRole
  hyperfabricRole : CarrierRole
  dialecticalInclusionRole : CarrierRole
  contractionRole : CarrierRole
  invertibilityRole : CarrierRole
  primeLaneRole : CarrierRole
  highNPrimeCarrierRole : CarrierRole
  heckeOperatorRole : CarrierRole
  eigenProfileRole : CarrierRole
  jInvariantRole : CarrierRole
  moonshineGroupRole : CarrierRole
  categorySurfaceRole : CarrierRole
  latticeRole : CarrierRole
  quotientRole : CarrierRole
  functorRole : CarrierRole
  operatorRole : CarrierRole
  semanticTransportRole : CarrierRole
  residualComparisonRole : CarrierRole
  claimReviewRole : CarrierRole
  genomeRole : CarrierRole
  connectomeRole : CarrierRole
  sensorimotorRole : CarrierRole
  chemistryChannelRole : CarrierRole
  gaugeRole : CarrierRole
  spinorRole : CarrierRole
  flowRole : CarrierRole
  sourceAttributionRole : CarrierRole
  nonPromotionBoundaryRole : CarrierRole

data FabricOrder : Set where
  lowOrderRegularFabric : FabricOrder
  highDimensionalBTBraidHyperfabric : FabricOrder

motifKey : CarrierMotif → String
motifKey motifSweetgrassBraidFabric =
  "sweetgrass_braid_fabric"
motifKey motif369 =
  "base_369"
motifKey motifCarry =
  "carry_memory"
motifKey motifDialectic =
  "dialectical_depth"
motifKey motifBraid =
  "braid_tension"
motifKey motifBTTree =
  "bruhat_tits_tree"
motifKey motifBTBraid =
  "bruhat_tits_braid"
motifKey motifPAdic =
  "p_adic_metric"
motifKey motifDecimalArchimedean =
  "decimal_archimedean_lane"
motifKey motifSupervoxel =
  "supervoxel_admissibility"
motifKey motifThreadBraid =
  "thread_braid"
motifKey motifLowOrderRegularFabric =
  "low_order_regular_fabric"
motifKey motifHighDimensionalHyperfabric =
  "high_dimensional_hyperfabric"
motifKey motifFascisticContraction =
  "fascistic_contraction"
motifKey motifAntifascistInvertibility =
  "antifascist_invertibility"
motifKey motifWaveTransport =
  "wave_transport"
motifKey motifWeave =
  "carrier_weave"
motifKey motifKnot =
  "knot_binding"
motifKey motifFifteenSSP =
  "fifteen_ssp"
motifKey motifHeckeEigen =
  "hecke_eigen_motif"
motifKey motifJInvariant =
  "j_invariant_moonshine_anchor"
motifKey motifMonsterMoonshine =
  "monster_moonshine"
motifKey motifHighNPrimeCarrier =
  "high_n_prime_carrier"
motifKey motifTlureyTriadicNonary =
  "tlurey_triadic_nonary"
motifKey motifUltrametricAdelic =
  "ultrametric_adelic_transport"
motifKey motifCliffordBottSpinor =
  "clifford_bott_spinor"
motifKey motifGaugeYangMills =
  "gauge_yang_mills"
motifKey motifNavierStokesFlow =
  "navier_stokes_flow"
motifKey motifSemanticPNFResidual =
  "semantic_pnf_residual"
motifKey motifClaimWikidataLattice =
  "claim_wikidata_lattice"
motifKey motifDNAGenomeChemistry =
  "dna_genome_chemistry"
motifKey motifBrainConnectomeSemantic =
  "brain_connectome_semantic"
motifKey motifBiologySensorimotor =
  "biology_sensorimotor"
motifKey motifCategoryFunctorOperator =
  "category_functor_operator"
motifKey motifLatticeQuotient =
  "lattice_quotient"

motifAnchor : CarrierMotif → CarrierAnchor
motifAnchor motifSweetgrassBraidFabric =
  anchorKnotWeaveCulture
motifAnchor motif369 =
  anchorBase369
motifAnchor motifCarry =
  anchorCarryMemory
motifAnchor motifDialectic =
  anchorDialecticalDepth
motifAnchor motifBraid =
  anchorUnifiedCarryBraid
motifAnchor motifBTTree =
  anchorBTBraidKP
motifAnchor motifBTBraid =
  anchorBTBraidKP
motifAnchor motifPAdic =
  anchorPAdicMetric
motifAnchor motifDecimalArchimedean =
  anchorDecimalArchimedeanLane
motifAnchor motifSupervoxel =
  anchorSupervoxelAdmissibility
motifAnchor motifThreadBraid =
  anchorCarrierBraid
motifAnchor motifLowOrderRegularFabric =
  anchorCarrierWeaveDefect
motifAnchor motifHighDimensionalHyperfabric =
  anchorBTBraidKP
motifAnchor motifFascisticContraction =
  anchorFascisticSystem
motifAnchor motifAntifascistInvertibility =
  anchorAntifascistSystem
motifAnchor motifWaveTransport =
  anchorWaveTransport
motifAnchor motifWeave =
  anchorCarrierWeaveDefect
motifAnchor motifKnot =
  anchorKnotWeaveCulture
motifAnchor motifFifteenSSP =
  anchorMonsterSSP15
motifAnchor motifHeckeEigen =
  anchorPrimeHeckeEigenMotif
motifAnchor motifJInvariant =
  anchorModularJInvariant
motifAnchor motifMonsterMoonshine =
  anchorMonsterMoonshineJDistribution
motifAnchor motifHighNPrimeCarrier =
  anchorHeckeScan15
motifAnchor motifTlureyTriadicNonary =
  anchorTlureyLogic
motifAnchor motifUltrametricAdelic =
  anchorUltrametricAdelicTransport
motifAnchor motifCliffordBottSpinor =
  anchorCliffordBottSpinor
motifAnchor motifGaugeYangMills =
  anchorGaugeYangMills
motifAnchor motifNavierStokesFlow =
  anchorNavierStokesFlow
motifAnchor motifSemanticPNFResidual =
  anchorSemanticPNFResidual
motifAnchor motifClaimWikidataLattice =
  anchorClaimWikidataLattice
motifAnchor motifDNAGenomeChemistry =
  anchorDNAGenomeChemistry
motifAnchor motifBrainConnectomeSemantic =
  anchorBrainConnectomeSemantic
motifAnchor motifBiologySensorimotor =
  anchorBiologySensorimotor
motifAnchor motifCategoryFunctorOperator =
  anchorCategoryFunctorOperator
motifAnchor motifLatticeQuotient =
  anchorLatticeQuotient

motifPrimaryRole : CarrierMotif → CarrierRole
motifPrimaryRole motifSweetgrassBraidFabric =
  fabricRole
motifPrimaryRole motif369 =
  localStateRole
motifPrimaryRole motifCarry =
  memoryRole
motifPrimaryRole motifDialectic =
  dialecticalInclusionRole
motifPrimaryRole motifBraid =
  braidRole
motifPrimaryRole motifBTTree =
  primeLaneRole
motifPrimaryRole motifBTBraid =
  btBraidRole
motifPrimaryRole motifPAdic =
  transportRole
motifPrimaryRole motifDecimalArchimedean =
  transportRole
motifPrimaryRole motifSupervoxel =
  admissibilityRole
motifPrimaryRole motifThreadBraid =
  threadRole
motifPrimaryRole motifLowOrderRegularFabric =
  fabricRole
motifPrimaryRole motifHighDimensionalHyperfabric =
  hyperfabricRole
motifPrimaryRole motifFascisticContraction =
  contractionRole
motifPrimaryRole motifAntifascistInvertibility =
  invertibilityRole
motifPrimaryRole motifWaveTransport =
  transportRole
motifPrimaryRole motifWeave =
  bindingRole
motifPrimaryRole motifKnot =
  bindingRole
motifPrimaryRole motifFifteenSSP =
  primeLaneRole
motifPrimaryRole motifHeckeEigen =
  eigenProfileRole
motifPrimaryRole motifJInvariant =
  jInvariantRole
motifPrimaryRole motifMonsterMoonshine =
  moonshineGroupRole
motifPrimaryRole motifHighNPrimeCarrier =
  highNPrimeCarrierRole
motifPrimaryRole motifTlureyTriadicNonary =
  localStateRole
motifPrimaryRole motifUltrametricAdelic =
  transportRole
motifPrimaryRole motifCliffordBottSpinor =
  spinorRole
motifPrimaryRole motifGaugeYangMills =
  gaugeRole
motifPrimaryRole motifNavierStokesFlow =
  flowRole
motifPrimaryRole motifSemanticPNFResidual =
  residualComparisonRole
motifPrimaryRole motifClaimWikidataLattice =
  claimReviewRole
motifPrimaryRole motifDNAGenomeChemistry =
  genomeRole
motifPrimaryRole motifBrainConnectomeSemantic =
  connectomeRole
motifPrimaryRole motifBiologySensorimotor =
  sensorimotorRole
motifPrimaryRole motifCategoryFunctorOperator =
  categorySurfaceRole
motifPrimaryRole motifLatticeQuotient =
  latticeRole

roleProjectionTarget : CarrierRole → Role.ProjectionTarget
roleProjectionTarget localStateRole =
  Role.objectTarget
roleProjectionTarget orientationRole =
  Role.modifierDiagnosticTarget
roleProjectionTarget memoryRole =
  Role.provenanceTarget
roleProjectionTarget defectRole =
  Role.objectTarget
roleProjectionTarget pressureRole =
  Role.qualifierTarget
roleProjectionTarget admissibilityRole =
  Role.qualifierTarget
roleProjectionTarget transportRole =
  Role.actionTarget
roleProjectionTarget bindingRole =
  Role.objectTarget
roleProjectionTarget braidRole =
  Role.modifierDiagnosticTarget
roleProjectionTarget threadRole =
  Role.provenanceTarget
roleProjectionTarget btBraidRole =
  Role.modifierDiagnosticTarget
roleProjectionTarget fabricRole =
  Role.modifierDiagnosticTarget
roleProjectionTarget hyperfabricRole =
  Role.modifierDiagnosticTarget
roleProjectionTarget dialecticalInclusionRole =
  Role.qualifierTarget
roleProjectionTarget contractionRole =
  Role.actionTarget
roleProjectionTarget invertibilityRole =
  Role.qualifierTarget
roleProjectionTarget primeLaneRole =
  Role.objectTarget
roleProjectionTarget highNPrimeCarrierRole =
  Role.objectTarget
roleProjectionTarget heckeOperatorRole =
  Role.actionTarget
roleProjectionTarget eigenProfileRole =
  Role.qualifierTarget
roleProjectionTarget jInvariantRole =
  Role.objectTarget
roleProjectionTarget moonshineGroupRole =
  Role.objectTarget
roleProjectionTarget categorySurfaceRole =
  Role.modifierDiagnosticTarget
roleProjectionTarget latticeRole =
  Role.modifierDiagnosticTarget
roleProjectionTarget quotientRole =
  Role.actionTarget
roleProjectionTarget functorRole =
  Role.actionTarget
roleProjectionTarget operatorRole =
  Role.actionTarget
roleProjectionTarget semanticTransportRole =
  Role.actionTarget
roleProjectionTarget residualComparisonRole =
  Role.qualifierTarget
roleProjectionTarget claimReviewRole =
  Role.objectTarget
roleProjectionTarget genomeRole =
  Role.objectTarget
roleProjectionTarget connectomeRole =
  Role.objectTarget
roleProjectionTarget sensorimotorRole =
  Role.qualifierTarget
roleProjectionTarget chemistryChannelRole =
  Role.objectTarget
roleProjectionTarget gaugeRole =
  Role.qualifierTarget
roleProjectionTarget spinorRole =
  Role.objectTarget
roleProjectionTarget flowRole =
  Role.actionTarget
roleProjectionTarget sourceAttributionRole =
  Role.provenanceTarget
roleProjectionTarget nonPromotionBoundaryRole =
  Role.provenanceTarget

motifFabricOrder : CarrierMotif → FabricOrder
motifFabricOrder motifHighDimensionalHyperfabric =
  highDimensionalBTBraidHyperfabric
motifFabricOrder motifBTBraid =
  highDimensionalBTBraidHyperfabric
motifFabricOrder motifHighNPrimeCarrier =
  highDimensionalBTBraidHyperfabric
motifFabricOrder motifHeckeEigen =
  highDimensionalBTBraidHyperfabric
motifFabricOrder motifJInvariant =
  highDimensionalBTBraidHyperfabric
motifFabricOrder motifMonsterMoonshine =
  highDimensionalBTBraidHyperfabric
motifFabricOrder motifCliffordBottSpinor =
  highDimensionalBTBraidHyperfabric
motifFabricOrder motifGaugeYangMills =
  highDimensionalBTBraidHyperfabric
motifFabricOrder motifUltrametricAdelic =
  highDimensionalBTBraidHyperfabric
motifFabricOrder motifCategoryFunctorOperator =
  highDimensionalBTBraidHyperfabric
motifFabricOrder motifLatticeQuotient =
  highDimensionalBTBraidHyperfabric
motifFabricOrder motifLowOrderRegularFabric =
  lowOrderRegularFabric
motifFabricOrder motifSweetgrassBraidFabric =
  lowOrderRegularFabric
motifFabricOrder motifWeave =
  lowOrderRegularFabric
motifFabricOrder motifKnot =
  lowOrderRegularFabric
motifFabricOrder motifThreadBraid =
  lowOrderRegularFabric
motifFabricOrder _ =
  lowOrderRegularFabric

motifProjectionTarget : CarrierMotif → Role.ProjectionTarget
motifProjectionTarget motif =
  roleProjectionTarget (motifPrimaryRole motif)

motifRoleVector : CarrierMotif → Role.RoleVector
motifRoleVector motif =
  Role.roleVector
    (Role.observedRole "carrier-spine")
    (Role.observedRole (motifKey motif))
    (Role.observedRole (motifKey motif))
    Role.absentRole
    (Role.observedRole "evidence-only")
    (Role.observedRole "local-anchor")

motifRoleVectorStable :
  ∀ motif →
  Role.StableRoleVector (motifRoleVector motif)
motifRoleVectorStable motif =
  Role.stableRoleVector
    (Role.observedStable "carrier-spine")
    (Role.observedStable (motifKey motif))
    (Role.observedStable (motifKey motif))
    Role.absentStable
    (Role.observedStable "evidence-only")
    (Role.observedStable "local-anchor")

motifRoleVectorSelfExact :
  ∀ motif →
  Role.meetRoleVector (motifRoleVector motif) (motifRoleVector motif)
    ≡
    Residual.exact
motifRoleVectorSelfExact motif =
  Role.roleVectorAllRequestedSlotsExactIsExact
    (motifRoleVector motif)
    (motifRoleVectorStable motif)

motifPNF : CarrierMotif → Residual.PredicatePNF
motifPNF motif =
  Residual.predicatePNF
    "sweetgrass_carrier_spine"
    Residual.sig-agent-theme
    (Residual.opaqueArg (motifKey motif))
    (Residual.opaqueArg "bounded-carrier-vocabulary")
    Residual.absent
    Residual.positive
    Residual.attributedEvidence
    "Sweetgrass carrier spine: evidence-only braid/fabric/dialectical carrier crosswalk"

motifReceipt : CarrierMotif → Residual.PNFEmissionReceipt
motifReceipt motif =
  Residual.pnfEmissionReceipt
    "dashi-sweetgrass-carrier-spine"
    "dashi-agda-pnf-role-vector-algebra"
    (motifKey motif)
    (motifPNF motif)

promotesLegalAuthority : CarrierMotif → Bool
promotesLegalAuthority _ = false

grantsLiveWikidataEditAuthority : CarrierMotif → Bool
grantsLiveWikidataEditAuthority _ = false

promotesSemanticAuthority : CarrierMotif → Bool
promotesSemanticAuthority _ = false

motifDoesNotPromoteLegalAuthority :
  ∀ motif →
  promotesLegalAuthority motif ≡ false
motifDoesNotPromoteLegalAuthority motif = refl

motifDoesNotGrantWikidataAuthority :
  ∀ motif →
  grantsLiveWikidataEditAuthority motif ≡ false
motifDoesNotGrantWikidataAuthority motif = refl

motifDoesNotPromoteSemanticAuthority :
  ∀ motif →
  promotesSemanticAuthority motif ≡ false
motifDoesNotPromoteSemanticAuthority motif = refl

sweetgrassIsBraidFabric :
  motifPrimaryRole motifSweetgrassBraidFabric ≡ fabricRole
sweetgrassIsBraidFabric = refl

sweetgrassProjectionIsDiagnostic :
  motifProjectionTarget motifSweetgrassBraidFabric
    ≡
    Role.modifierDiagnosticTarget
sweetgrassProjectionIsDiagnostic = refl

hyperfabricIsHighDimensionalBTBraid :
  motifFabricOrder motifHighDimensionalHyperfabric
    ≡
    highDimensionalBTBraidHyperfabric
hyperfabricIsHighDimensionalBTBraid = refl

regularFabricIsLowOrderBTBraidLike :
  motifFabricOrder motifLowOrderRegularFabric
    ≡
    lowOrderRegularFabric
regularFabricIsLowOrderBTBraidLike = refl

heckeEigenProjectionIsQualifier :
  motifProjectionTarget motifHeckeEigen
    ≡
    Role.qualifierTarget
heckeEigenProjectionIsQualifier = refl

jInvariantProjectionIsObject :
  motifProjectionTarget motifJInvariant
    ≡
    Role.objectTarget
jInvariantProjectionIsObject = refl

dialecticTiesTo369 :
  List CarrierMotif
dialecticTiesTo369 =
  motif369
  ∷ motifCarry
  ∷ motifDialectic
  ∷ motifTlureyTriadicNonary
  ∷ motifSweetgrassBraidFabric
  ∷ []

heckeEigenJInvariantThread :
  List CarrierMotif
heckeEigenJInvariantThread =
  motifHeckeEigen
  ∷ motifJInvariant
  ∷ motifMonsterMoonshine
  ∷ motifFifteenSSP
  ∷ motifHighNPrimeCarrier
  ∷ []

pAdicDecimalWaveThread :
  List CarrierMotif
pAdicDecimalWaveThread =
  motifPAdic
  ∷ motifDecimalArchimedean
  ∷ motifUltrametricAdelic
  ∷ motifWaveTransport
  ∷ motifSupervoxel
  ∷ []

physicsGeometryThread :
  List CarrierMotif
physicsGeometryThread =
  motifWaveTransport
  ∷ motifCliffordBottSpinor
  ∷ motifGaugeYangMills
  ∷ motifNavierStokesFlow
  ∷ motifBTTree
  ∷ motifBTBraid
  ∷ motifPAdic
  ∷ motifUltrametricAdelic
  ∷ []

semanticReviewThread :
  List CarrierMotif
semanticReviewThread =
  motifSemanticPNFResidual
  ∷ motifClaimWikidataLattice
  ∷ motifCategoryFunctorOperator
  ∷ motifLatticeQuotient
  ∷ motifSweetgrassBraidFabric
  ∷ []

lifeLanguageThread :
  List CarrierMotif
lifeLanguageThread =
  motifDNAGenomeChemistry
  ∷ motifBrainConnectomeSemantic
  ∷ motifBiologySensorimotor
  ∷ motifSemanticPNFResidual
  ∷ motifWeave
  ∷ motifKnot
  ∷ []

btBraidFabricThread :
  List CarrierMotif
btBraidFabricThread =
  motifThreadBraid
  ∷ motifBraid
  ∷ motifBTTree
  ∷ motifBTBraid
  ∷ motifLowOrderRegularFabric
  ∷ motifHighDimensionalHyperfabric
  ∷ motifHighNPrimeCarrier
  ∷ []

canonicalCarrierMotifs : List CarrierMotif
canonicalCarrierMotifs =
  motifSweetgrassBraidFabric
  ∷ motif369
  ∷ motifCarry
  ∷ motifDialectic
  ∷ motifBraid
  ∷ motifBTTree
  ∷ motifBTBraid
  ∷ motifPAdic
  ∷ motifDecimalArchimedean
  ∷ motifSupervoxel
  ∷ motifThreadBraid
  ∷ motifLowOrderRegularFabric
  ∷ motifHighDimensionalHyperfabric
  ∷ motifFascisticContraction
  ∷ motifAntifascistInvertibility
  ∷ motifWaveTransport
  ∷ motifWeave
  ∷ motifKnot
  ∷ motifFifteenSSP
  ∷ motifHeckeEigen
  ∷ motifJInvariant
  ∷ motifMonsterMoonshine
  ∷ motifHighNPrimeCarrier
  ∷ motifTlureyTriadicNonary
  ∷ motifUltrametricAdelic
  ∷ motifCliffordBottSpinor
  ∷ motifGaugeYangMills
  ∷ motifNavierStokesFlow
  ∷ motifSemanticPNFResidual
  ∷ motifClaimWikidataLattice
  ∷ motifDNAGenomeChemistry
  ∷ motifBrainConnectomeSemantic
  ∷ motifBiologySensorimotor
  ∷ motifCategoryFunctorOperator
  ∷ motifLatticeQuotient
  ∷ []

canonicalCarrierAnchors : List CarrierAnchor
canonicalCarrierAnchors =
  anchorBase369
  ∷ anchorLocalDocs369
  ∷ anchorCarryMemory
  ∷ anchorDialecticalDepth
  ∷ anchorUnifiedCarryBraid
  ∷ anchorBTBraidKP
  ∷ anchorCarrierBraid
  ∷ anchorPAdicMetric
  ∷ anchorDecimalArchimedeanLane
  ∷ anchorSupervoxelAdmissibility
  ∷ anchorPrimeHeckeEigenMotif
  ∷ anchorHeckeScan15
  ∷ anchorModularJInvariant
  ∷ anchorMonsterMoonshineJDistribution
  ∷ anchorMonsterMoonshineSSPQuotient
  ∷ anchorFascisticSystem
  ∷ anchorAntifascistSystem
  ∷ anchorWaveTransport
  ∷ anchorKnotWeaveCulture
  ∷ anchorCarrierWeaveDefect
  ∷ anchorMonsterSSP15
  ∷ anchorTlureyLogic
  ∷ anchorUltrametricAdelicTransport
  ∷ anchorCliffordBottSpinor
  ∷ anchorGaugeYangMills
  ∷ anchorNavierStokesFlow
  ∷ anchorSemanticPNFResidual
  ∷ anchorClaimWikidataLattice
  ∷ anchorDNAGenomeChemistry
  ∷ anchorBrainConnectomeSemantic
  ∷ anchorBiologySensorimotor
  ∷ anchorCategoryFunctorOperator
  ∷ anchorLatticeQuotient
  ∷ []

data SweetgrassSpineNonClaim : Set where
  noCrossDomainDefinitionalEquality : SweetgrassSpineNonClaim
  noLegalAuthorityPromotion : SweetgrassSpineNonClaim
  noWikidataEditAuthorityPromotion : SweetgrassSpineNonClaim
  noCulturalUniversalPromotion : SweetgrassSpineNonClaim
  noPhysicsPromotion : SweetgrassSpineNonClaim
  noHeckeEigenTheoremPromotion : SweetgrassSpineNonClaim
  noJInvariantMoonshinePromotion : SweetgrassSpineNonClaim
  noHyperfabricBTBraidDefinitionalEquality : SweetgrassSpineNonClaim
  noGroupCategoryCollapse : SweetgrassSpineNonClaim
  noFascismOrAntifascismTheoremPromotion : SweetgrassSpineNonClaim
  noLifeScienceAuthorityPromotion : SweetgrassSpineNonClaim
  noSemanticTruthAuthorityPromotion : SweetgrassSpineNonClaim
  noCategoryEquivalencePromotion : SweetgrassSpineNonClaim
  noGaugeOrFlowTheoremPromotion : SweetgrassSpineNonClaim
  noCliffordBottEquivalencePromotion : SweetgrassSpineNonClaim
  noClayPromotion : SweetgrassSpineNonClaim

canonicalSweetgrassSpineNonClaims : List SweetgrassSpineNonClaim
canonicalSweetgrassSpineNonClaims =
  noCrossDomainDefinitionalEquality
  ∷ noLegalAuthorityPromotion
  ∷ noWikidataEditAuthorityPromotion
  ∷ noCulturalUniversalPromotion
  ∷ noPhysicsPromotion
  ∷ noHeckeEigenTheoremPromotion
  ∷ noJInvariantMoonshinePromotion
  ∷ noHyperfabricBTBraidDefinitionalEquality
  ∷ noGroupCategoryCollapse
  ∷ noFascismOrAntifascismTheoremPromotion
  ∷ noLifeScienceAuthorityPromotion
  ∷ noSemanticTruthAuthorityPromotion
  ∷ noCategoryEquivalencePromotion
  ∷ noGaugeOrFlowTheoremPromotion
  ∷ noCliffordBottEquivalencePromotion
  ∷ noClayPromotion
  ∷ []

record SweetgrassCarrierSpineSurface : Set where
  field
    motifs :
      List CarrierMotif

    motifsAreCanonical :
      motifs ≡ canonicalCarrierMotifs

    anchors :
      List CarrierAnchor

    anchorsAreCanonical :
      anchors ≡ canonicalCarrierAnchors

    pnfCarrier :
      CarrierMotif → Residual.PredicatePNF

    roleVectorCarrier :
      CarrierMotif → Role.RoleVector

    projectionTarget :
      CarrierMotif → Role.ProjectionTarget

    dialectic369Link :
      List CarrierMotif

    dialectic369LinkIsCanonical :
      dialectic369Link ≡ dialecticTiesTo369

    heckeEigenJInvariantLink :
      List CarrierMotif

    heckeEigenJInvariantLinkIsCanonical :
      heckeEigenJInvariantLink ≡ heckeEigenJInvariantThread

    pAdicDecimalWaveLink :
      List CarrierMotif

    pAdicDecimalWaveLinkIsCanonical :
      pAdicDecimalWaveLink ≡ pAdicDecimalWaveThread

    physicsGeometryLink :
      List CarrierMotif

    physicsGeometryLinkIsCanonical :
      physicsGeometryLink ≡ physicsGeometryThread

    semanticReviewLink :
      List CarrierMotif

    semanticReviewLinkIsCanonical :
      semanticReviewLink ≡ semanticReviewThread

    lifeLanguageLink :
      List CarrierMotif

    lifeLanguageLinkIsCanonical :
      lifeLanguageLink ≡ lifeLanguageThread

    btBraidFabricLink :
      List CarrierMotif

    btBraidFabricLinkIsCanonical :
      btBraidFabricLink ≡ btBraidFabricThread

    fabricOrder :
      CarrierMotif → FabricOrder

    sweetgrassAttributionStatement :
      String

    sweetgrassAttributionIsKimmerer :
      sweetgrassAttributionStatement ≡ sweetgrassAttribution

    legalAuthorityPromotion :
      Bool

    legalAuthorityPromotionIsFalse :
      legalAuthorityPromotion ≡ false

    wikidataEditAuthorityPromotion :
      Bool

    wikidataEditAuthorityPromotionIsFalse :
      wikidataEditAuthorityPromotion ≡ false

    semanticAuthorityPromotion :
      Bool

    semanticAuthorityPromotionIsFalse :
      semanticAuthorityPromotion ≡ false

    nonClaims :
      List SweetgrassSpineNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalSweetgrassSpineNonClaims

    plainReading :
      String

canonicalSweetgrassCarrierSpineSurface :
  SweetgrassCarrierSpineSurface
canonicalSweetgrassCarrierSpineSurface =
  record
    { motifs =
        canonicalCarrierMotifs
    ; motifsAreCanonical =
        refl
    ; anchors =
        canonicalCarrierAnchors
    ; anchorsAreCanonical =
        refl
    ; pnfCarrier =
        motifPNF
    ; roleVectorCarrier =
        motifRoleVector
    ; projectionTarget =
        motifProjectionTarget
    ; dialectic369Link =
        dialecticTiesTo369
    ; dialectic369LinkIsCanonical =
        refl
    ; heckeEigenJInvariantLink =
        heckeEigenJInvariantThread
    ; heckeEigenJInvariantLinkIsCanonical =
        refl
    ; pAdicDecimalWaveLink =
        pAdicDecimalWaveThread
    ; pAdicDecimalWaveLinkIsCanonical =
        refl
    ; physicsGeometryLink =
        physicsGeometryThread
    ; physicsGeometryLinkIsCanonical =
        refl
    ; semanticReviewLink =
        semanticReviewThread
    ; semanticReviewLinkIsCanonical =
        refl
    ; lifeLanguageLink =
        lifeLanguageThread
    ; lifeLanguageLinkIsCanonical =
        refl
    ; btBraidFabricLink =
        btBraidFabricThread
    ; btBraidFabricLinkIsCanonical =
        refl
    ; fabricOrder =
        motifFabricOrder
    ; sweetgrassAttributionStatement =
        sweetgrassAttribution
    ; sweetgrassAttributionIsKimmerer =
        refl
    ; legalAuthorityPromotion =
        false
    ; legalAuthorityPromotionIsFalse =
        refl
    ; wikidataEditAuthorityPromotion =
        false
    ; wikidataEditAuthorityPromotionIsFalse =
        refl
    ; semanticAuthorityPromotion =
        false
    ; semanticAuthorityPromotionIsFalse =
        refl
    ; nonClaims =
        canonicalSweetgrassSpineNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; plainReading =
        "Sweetgrass is carried as Kimmerer-attributed braid/fabric vocabulary; 3-6-9, Tlurey/triadic/nonary, dialectic, BT tree, BT-braid, p-adic, decimal/Archimedean, ultrametric/adelic, supervoxel, wave, Clifford/Bott/spinor, gauge/Yang-Mills, Navier-Stokes/flow, Hecke/eigen, j-invariant, monster/moonshine, high-n prime carrier, fascistic/antifascistic, semantic PNF/residual, claim/Wikidata lattice, DNA/genome/chemistry, brain/connectome/semantic transport, biology/sensorimotor, category/functor/operator/lattice, weave/knot, regular fabric, hyperfabric, and 15SSP lanes enter NLP/PNF/ITIR only as bounded evidence carriers. Hyperfabric is classified as high-dimensional BT-braid-like carrier vocabulary; regular fabric is low-order BT-braid-like carrier vocabulary; neither is a definitional equality theorem."
    }
