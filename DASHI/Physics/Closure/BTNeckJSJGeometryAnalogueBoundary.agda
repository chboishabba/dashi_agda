module DASHI.Physics.Closure.BTNeckJSJGeometryAnalogueBoundary where

-- Boundary module for the Bruhat-Tits epsilon-neck analogy, the JSJ
-- analogy, and the corrected Thurston-geometry placement.
--
-- This file records a vocabulary-level analogue only.  It deliberately keeps
-- smooth surgery, canonical-neighborhood, and geometrization conclusions
-- blocked: the BT product tree is placed in non-Archimedean hyperbolic-tree
-- geometry, hypervoxels are placed in finite flat-cell geometry, and the BT
-- boundary is placed at a p-adic boundary.  None of these placements asserts a
-- smooth S2 cross-section, a Ricci-flow neck, a constructed JSJ torus system,
-- JSJ uniqueness, or Thurston geometrization.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

data ⊥ : Set where

------------------------------------------------------------------------
-- Small local counting utility.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Boolean negation as an explicit fail-closed gate.

NotTrue : Bool → Set
NotTrue b =
  b ≡ true → ⊥

falseNotTrue : NotTrue false
falseNotTrue ()

------------------------------------------------------------------------
-- Bruhat-Tits epsilon-neck analogue.

data ScaleLabel : Set where
  pAdicDepthScale :
    ScaleLabel

  hypervoxelMeshScale :
    ScaleLabel

  archimedeanComparisonScale :
    ScaleLabel

canonicalScaleName : ScaleLabel → String
canonicalScaleName pAdicDepthScale =
  "p-adic depth scale"
canonicalScaleName hypervoxelMeshScale =
  "finite hypervoxel mesh scale"
canonicalScaleName archimedeanComparisonScale =
  "archimedean comparison scale"

q : Nat
q =
  2

q+1 : Nat
q+1 =
  suc q

record BTNeckAnalogue : Set where
  field
    depth :
      Nat

    scale :
      ScaleLabel

    scaleLabel :
      String

    scaleLabelIsCanonical :
      scaleLabel ≡ canonicalScaleName scale

    crossSectionCardinality :
      Nat

    crossSectionCardinalityIsq+1 :
      crossSectionCardinality ≡ q+1

    cylindricalApprox :
      Bool

    cylindricalApproxIsTrue :
      cylindricalApprox ≡ true

    smoothS2CrossSection :
      Bool

    smoothS2CrossSectionIsFalse :
      smoothS2CrossSection ≡ false

    smoothS2CrossSectionBlocked :
      NotTrue smoothS2CrossSection

open BTNeckAnalogue public

canonicalBTNeckAnalogue : BTNeckAnalogue
canonicalBTNeckAnalogue =
  record
    { depth =
        3
    ; scale =
        pAdicDepthScale
    ; scaleLabel =
        canonicalScaleName pAdicDepthScale
    ; scaleLabelIsCanonical =
        refl
    ; crossSectionCardinality =
        q+1
    ; crossSectionCardinalityIsq+1 =
        refl
    ; cylindricalApprox =
        true
    ; cylindricalApproxIsTrue =
        refl
    ; smoothS2CrossSection =
        false
    ; smoothS2CrossSectionIsFalse =
        refl
    ; smoothS2CrossSectionBlocked =
        falseNotTrue
    }

btNeckDepthIs3 :
  depth canonicalBTNeckAnalogue ≡ 3
btNeckDepthIs3 =
  refl

btNeckCardinalityIsq+1 :
  crossSectionCardinality canonicalBTNeckAnalogue ≡ q+1
btNeckCardinalityIsq+1 =
  refl

btNeckCylindricalApproxTrue :
  cylindricalApprox canonicalBTNeckAnalogue ≡ true
btNeckCylindricalApproxTrue =
  refl

btNeckSmoothS2False :
  smoothS2CrossSection canonicalBTNeckAnalogue ≡ false
btNeckSmoothS2False =
  refl

------------------------------------------------------------------------
-- JSJ analogue.

record JSJAnalogue : Set where
  field
    btPiecesAtoroidal :
      Bool

    btPiecesAtoroidalIsTrue :
      btPiecesAtoroidal ≡ true

    hypervoxelSeifertAnalogue :
      Bool

    hypervoxelSeifertAnalogueIsTrue :
      hypervoxelSeifertAnalogue ≡ true

    incompressibleGluingToriConstructed :
      Bool

    incompressibleGluingToriConstructedIsFalse :
      incompressibleGluingToriConstructed ≡ false

    incompressibleGluingToriConstructionBlocked :
      NotTrue incompressibleGluingToriConstructed

    jsjUniquenessProvedHere :
      Bool

    jsjUniquenessProvedHereIsFalse :
      jsjUniquenessProvedHere ≡ false

    jsjUniquenessPromotionBlocked :
      NotTrue jsjUniquenessProvedHere

open JSJAnalogue public

canonicalJSJAnalogue : JSJAnalogue
canonicalJSJAnalogue =
  record
    { btPiecesAtoroidal =
        true
    ; btPiecesAtoroidalIsTrue =
        refl
    ; hypervoxelSeifertAnalogue =
        true
    ; hypervoxelSeifertAnalogueIsTrue =
        refl
    ; incompressibleGluingToriConstructed =
        false
    ; incompressibleGluingToriConstructedIsFalse =
        refl
    ; incompressibleGluingToriConstructionBlocked =
        falseNotTrue
    ; jsjUniquenessProvedHere =
        false
    ; jsjUniquenessProvedHereIsFalse =
        refl
    ; jsjUniquenessPromotionBlocked =
        falseNotTrue
    }

jsjAtoroidalTrue :
  btPiecesAtoroidal canonicalJSJAnalogue ≡ true
jsjAtoroidalTrue =
  refl

jsjHypervoxelSeifertTrue :
  hypervoxelSeifertAnalogue canonicalJSJAnalogue ≡ true
jsjHypervoxelSeifertTrue =
  refl

jsjGluingToriConstructedFalse :
  incompressibleGluingToriConstructed canonicalJSJAnalogue ≡ false
jsjGluingToriConstructedFalse =
  refl

jsjUniquenessFalse :
  jsjUniquenessProvedHere canonicalJSJAnalogue ≡ false
jsjUniquenessFalse =
  refl

------------------------------------------------------------------------
-- Corrected Thurston-geometry analogue placement.

data GeometryAnalogue : Set where
  archimedeanSocket :
    GeometryAnalogue

  nonArchHypTree :
    GeometryAnalogue

  finiteFlatCell :
    GeometryAnalogue

  pAdicBoundary :
    GeometryAnalogue

geometryAnalogueLabel : GeometryAnalogue → String
geometryAnalogueLabel archimedeanSocket =
  "archimedean socket"
geometryAnalogueLabel nonArchHypTree =
  "non-Archimedean hyperbolic tree"
geometryAnalogueLabel finiteFlatCell =
  "finite flat cell"
geometryAnalogueLabel pAdicBoundary =
  "p-adic boundary"

BTProductTreeGeometry : GeometryAnalogue
BTProductTreeGeometry =
  nonArchHypTree

HypervoxelGeometry : GeometryAnalogue
HypervoxelGeometry =
  finiteFlatCell

BTBoundaryGeometry : GeometryAnalogue
BTBoundaryGeometry =
  pAdicBoundary

bTProductTreeGeometryCorrected :
  BTProductTreeGeometry ≡ nonArchHypTree
bTProductTreeGeometryCorrected =
  refl

hypervoxelGeometryCorrected :
  HypervoxelGeometry ≡ finiteFlatCell
hypervoxelGeometryCorrected =
  refl

bTBoundaryGeometryCorrected :
  BTBoundaryGeometry ≡ pAdicBoundary
bTBoundaryGeometryCorrected =
  refl

data AnalogueCarrier : Set where
  btProductTreeCarrier :
    AnalogueCarrier

  hypervoxelCarrier :
    AnalogueCarrier

  btBoundaryCarrier :
    AnalogueCarrier

  archimedeanComparisonCarrier :
    AnalogueCarrier

canonicalGeometryForCarrier : AnalogueCarrier → GeometryAnalogue
canonicalGeometryForCarrier btProductTreeCarrier =
  BTProductTreeGeometry
canonicalGeometryForCarrier hypervoxelCarrier =
  HypervoxelGeometry
canonicalGeometryForCarrier btBoundaryCarrier =
  BTBoundaryGeometry
canonicalGeometryForCarrier archimedeanComparisonCarrier =
  archimedeanSocket

record GeometryPlacementRow : Set where
  field
    carrier :
      AnalogueCarrier

    geometry :
      GeometryAnalogue

    geometryIsCanonical :
      geometry ≡ canonicalGeometryForCarrier carrier

    thurstonGeometryClaim :
      Bool

    thurstonGeometryClaimIsFalse :
      thurstonGeometryClaim ≡ false

    thurstonGeometryClaimBlocked :
      NotTrue thurstonGeometryClaim

open GeometryPlacementRow public

mkGeometryPlacementRow : AnalogueCarrier → GeometryPlacementRow
mkGeometryPlacementRow carrier =
  record
    { carrier =
        carrier
    ; geometry =
        canonicalGeometryForCarrier carrier
    ; geometryIsCanonical =
        refl
    ; thurstonGeometryClaim =
        false
    ; thurstonGeometryClaimIsFalse =
        refl
    ; thurstonGeometryClaimBlocked =
        falseNotTrue
    }

canonicalGeometryPlacementRows : List GeometryPlacementRow
canonicalGeometryPlacementRows =
  mkGeometryPlacementRow btProductTreeCarrier
  ∷ mkGeometryPlacementRow hypervoxelCarrier
  ∷ mkGeometryPlacementRow btBoundaryCarrier
  ∷ mkGeometryPlacementRow archimedeanComparisonCarrier
  ∷ []

geometryPlacementRowCount : Nat
geometryPlacementRowCount =
  listLength canonicalGeometryPlacementRows

geometryPlacementRowCountIs4 :
  geometryPlacementRowCount ≡ 4
geometryPlacementRowCountIs4 =
  refl

------------------------------------------------------------------------
-- Claims explicitly blocked by this boundary.

data BlockedPromotionClaim : Set where
  smoothSurgeryClaim :
    BlockedPromotionClaim

  canonicalNeighborhoodClaim :
    BlockedPromotionClaim

  geometrizationClaim :
    BlockedPromotionClaim

  smoothRicciFlowNeckClaim :
    BlockedPromotionClaim

  smoothS2CrossSectionClaim :
    BlockedPromotionClaim

  constructedJSJGluingToriClaim :
    BlockedPromotionClaim

  jsjUniquenessClaim :
    BlockedPromotionClaim

claimName : BlockedPromotionClaim → String
claimName smoothSurgeryClaim =
  "smooth surgery"
claimName canonicalNeighborhoodClaim =
  "canonical neighborhood"
claimName geometrizationClaim =
  "geometrization"
claimName smoothRicciFlowNeckClaim =
  "smooth Ricci-flow neck"
claimName smoothS2CrossSectionClaim =
  "smooth S2 cross-section"
claimName constructedJSJGluingToriClaim =
  "constructed incompressible JSJ gluing tori"
claimName jsjUniquenessClaim =
  "JSJ uniqueness"

record BlockedClaimRow : Set where
  field
    claim :
      BlockedPromotionClaim

    claimLabel :
      String

    claimLabelIsCanonical :
      claimLabel ≡ claimName claim

    provedHere :
      Bool

    provedHereIsFalse :
      provedHere ≡ false

    promotionBlocked :
      NotTrue provedHere

open BlockedClaimRow public

mkBlockedClaimRow : BlockedPromotionClaim → BlockedClaimRow
mkBlockedClaimRow claim =
  record
    { claim =
        claim
    ; claimLabel =
        claimName claim
    ; claimLabelIsCanonical =
        refl
    ; provedHere =
        false
    ; provedHereIsFalse =
        refl
    ; promotionBlocked =
        falseNotTrue
    }

canonicalBlockedClaimRows : List BlockedClaimRow
canonicalBlockedClaimRows =
  mkBlockedClaimRow smoothSurgeryClaim
  ∷ mkBlockedClaimRow canonicalNeighborhoodClaim
  ∷ mkBlockedClaimRow geometrizationClaim
  ∷ mkBlockedClaimRow smoothRicciFlowNeckClaim
  ∷ mkBlockedClaimRow smoothS2CrossSectionClaim
  ∷ mkBlockedClaimRow constructedJSJGluingToriClaim
  ∷ mkBlockedClaimRow jsjUniquenessClaim
  ∷ []

blockedClaimRowCount : Nat
blockedClaimRowCount =
  listLength canonicalBlockedClaimRows

blockedClaimRowCountIs7 :
  blockedClaimRowCount ≡ 7
blockedClaimRowCountIs7 =
  refl

------------------------------------------------------------------------
-- Composite boundary surface.

data AnalogueBoundaryStatus : Set where
  analogyRecordedFailClosed :
    AnalogueBoundaryStatus

  smoothPromotionBlocked :
    AnalogueBoundaryStatus

  jsjPromotionBlocked :
    AnalogueBoundaryStatus

  thurstonPlacementCorrectedNoGeometrization :
    AnalogueBoundaryStatus

record BTNeckJSJGeometryAnalogueBoundary : Set where
  field
    btNeck :
      BTNeckAnalogue

    jsj :
      JSJAnalogue

    geometryRows :
      List GeometryPlacementRow

    geometryRowCountField :
      Nat

    geometryRowCountFieldIs4 :
      geometryRowCountField ≡ 4

    geometryRowCountMatchesRows :
      geometryRowCountField ≡ listLength geometryRows

    blockedRows :
      List BlockedClaimRow

    blockedRowCountField :
      Nat

    blockedRowCountFieldIs7 :
      blockedRowCountField ≡ 7

    blockedRowCountMatchesRows :
      blockedRowCountField ≡ listLength blockedRows

    status :
      AnalogueBoundaryStatus

    btProductTreeGeometry :
      GeometryAnalogue

    btProductTreeGeometryIsNonArchHypTree :
      btProductTreeGeometry ≡ nonArchHypTree

    hypervoxelGeometry :
      GeometryAnalogue

    hypervoxelGeometryIsFiniteFlatCell :
      hypervoxelGeometry ≡ finiteFlatCell

    btBoundaryGeometry :
      GeometryAnalogue

    btBoundaryGeometryIspAdicBoundary :
      btBoundaryGeometry ≡ pAdicBoundary

    smoothSurgeryProvedHere :
      Bool

    smoothSurgeryProvedHereIsFalse :
      smoothSurgeryProvedHere ≡ false

    canonicalNeighborhoodProvedHere :
      Bool

    canonicalNeighborhoodProvedHereIsFalse :
      canonicalNeighborhoodProvedHere ≡ false

    geometrizationProvedHere :
      Bool

    geometrizationProvedHereIsFalse :
      geometrizationProvedHere ≡ false

open BTNeckJSJGeometryAnalogueBoundary public

canonicalBTNeckJSJGeometryAnalogueBoundary :
  BTNeckJSJGeometryAnalogueBoundary
canonicalBTNeckJSJGeometryAnalogueBoundary =
  record
    { btNeck =
        canonicalBTNeckAnalogue
    ; jsj =
        canonicalJSJAnalogue
    ; geometryRows =
        canonicalGeometryPlacementRows
    ; geometryRowCountField =
        4
    ; geometryRowCountFieldIs4 =
        refl
    ; geometryRowCountMatchesRows =
        refl
    ; blockedRows =
        canonicalBlockedClaimRows
    ; blockedRowCountField =
        7
    ; blockedRowCountFieldIs7 =
        refl
    ; blockedRowCountMatchesRows =
        refl
    ; status =
        thurstonPlacementCorrectedNoGeometrization
    ; btProductTreeGeometry =
        BTProductTreeGeometry
    ; btProductTreeGeometryIsNonArchHypTree =
        refl
    ; hypervoxelGeometry =
        HypervoxelGeometry
    ; hypervoxelGeometryIsFiniteFlatCell =
        refl
    ; btBoundaryGeometry =
        BTBoundaryGeometry
    ; btBoundaryGeometryIspAdicBoundary =
        refl
    ; smoothSurgeryProvedHere =
        false
    ; smoothSurgeryProvedHereIsFalse =
        refl
    ; canonicalNeighborhoodProvedHere =
        false
    ; canonicalNeighborhoodProvedHereIsFalse =
        refl
    ; geometrizationProvedHere =
        false
    ; geometrizationProvedHereIsFalse =
        refl
    }

boundaryBTDepth :
  depth (btNeck canonicalBTNeckJSJGeometryAnalogueBoundary) ≡ 3
boundaryBTDepth =
  refl

boundaryBTCrossSectionCardinality :
  crossSectionCardinality (btNeck canonicalBTNeckJSJGeometryAnalogueBoundary)
    ≡ q+1
boundaryBTCrossSectionCardinality =
  refl

boundaryCylindricalApproxTrue :
  cylindricalApprox (btNeck canonicalBTNeckJSJGeometryAnalogueBoundary)
    ≡ true
boundaryCylindricalApproxTrue =
  refl

boundarySmoothS2CrossSectionFalse :
  smoothS2CrossSection (btNeck canonicalBTNeckJSJGeometryAnalogueBoundary)
    ≡ false
boundarySmoothS2CrossSectionFalse =
  refl

boundaryBTAtoroidalTrue :
  btPiecesAtoroidal (jsj canonicalBTNeckJSJGeometryAnalogueBoundary) ≡ true
boundaryBTAtoroidalTrue =
  refl

boundaryHypervoxelSeifertAnalogueTrue :
  hypervoxelSeifertAnalogue
    (jsj canonicalBTNeckJSJGeometryAnalogueBoundary)
    ≡ true
boundaryHypervoxelSeifertAnalogueTrue =
  refl

boundaryGluingToriConstructedFalse :
  incompressibleGluingToriConstructed
    (jsj canonicalBTNeckJSJGeometryAnalogueBoundary)
    ≡ false
boundaryGluingToriConstructedFalse =
  refl

boundaryJSJUniquenessFalse :
  jsjUniquenessProvedHere
    (jsj canonicalBTNeckJSJGeometryAnalogueBoundary)
    ≡ false
boundaryJSJUniquenessFalse =
  refl

boundaryBTProductTreeGeometryCorrect :
  btProductTreeGeometry canonicalBTNeckJSJGeometryAnalogueBoundary
    ≡ nonArchHypTree
boundaryBTProductTreeGeometryCorrect =
  refl

boundaryHypervoxelGeometryCorrect :
  hypervoxelGeometry canonicalBTNeckJSJGeometryAnalogueBoundary
    ≡ finiteFlatCell
boundaryHypervoxelGeometryCorrect =
  refl

boundaryBTBoundaryGeometryCorrect :
  btBoundaryGeometry canonicalBTNeckJSJGeometryAnalogueBoundary
    ≡ pAdicBoundary
boundaryBTBoundaryGeometryCorrect =
  refl

boundarySmoothSurgeryBlocked :
  NotTrue (smoothSurgeryProvedHere canonicalBTNeckJSJGeometryAnalogueBoundary)
boundarySmoothSurgeryBlocked =
  falseNotTrue

boundaryCanonicalNeighborhoodBlocked :
  NotTrue
    (canonicalNeighborhoodProvedHere
      canonicalBTNeckJSJGeometryAnalogueBoundary)
boundaryCanonicalNeighborhoodBlocked =
  falseNotTrue

boundaryGeometrizationBlocked :
  NotTrue (geometrizationProvedHere canonicalBTNeckJSJGeometryAnalogueBoundary)
boundaryGeometrizationBlocked =
  falseNotTrue
