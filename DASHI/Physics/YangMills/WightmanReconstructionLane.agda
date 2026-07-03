module DASHI.Physics.YangMills.WightmanReconstructionLane where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Geometry.Gauge.SUNPrimitives
open import DASHI.Physics.YangMills.ProofTargetSurface
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( dashi-internal-proof
  ; proved
  ; paperImport
  ; auditTested
  ; consequence-proof
  )

oS0TemperednessSurface : ProofTargetSurface
oS0TemperednessSurface =
  mkProofTargetSurface
    "OS0Temperedness"
    "Eriksson 2602.0088 §8.1 source route"
    "The continuum Schwinger distributions S_n extend to tempered distributions in S'(R^{4n})."
    "Uniform distributional bounds and the source tightness route."
    "OS0 temperedness is available at source-intake level."
    "OS reconstruction and P31."
    "The OS reconstruction theorem cannot be applied."
    paperImport

oS1EuclideanCovarianceSurface : ProofTargetSurface
oS1EuclideanCovarianceSurface =
  mkProofTargetSurface
    "OS1EuclideanCovariance"
    "Eriksson 2602.0092 Thm 4.2 + Cor 4.3 through P28-P30 and P32"
    "For every Euclidean transformation g, the continuum Schwinger functions satisfy S_n(gx_1,...,gx_n) = S_n(x_1,...,x_n)."
    "P20-P22, P28-P30, P32."
    "OS1 Euclidean covariance is available."
    "OS reconstruction and P31."
    "The continuum endpoint lacks Euclidean covariance."
    paperImport

oS2ReflectionPositivitySurface : ProofTargetSurface
oS2ReflectionPositivitySurface =
  mkProofTargetSurface
    "OS2ReflectionPositivity"
    "Osterwalder-Seiler reflection positivity for Wilson action plus limit-preservation route noted in DASHI OSAxiomBundle"
    "For positive-time supported test functions, the reflected Schwinger quadratic form is nonnegative."
    "Reflection-positive Wilson/Haar lattice measure and preservation through the admitted limiting procedure."
    "OS2 reflection positivity is available at audit/source-intake level."
    "OS reconstruction and P31."
    "Hilbert-space reconstruction has no positivity input."
    auditTested

oS3BosonicSymmetrySurface : ProofTargetSurface
oS3BosonicSymmetrySurface =
  mkProofTargetSurface
    "OS3BosonicSymmetry"
    "Eriksson 2602.0088 §8.1 source route"
    "Gauge-invariant bosonic Schwinger functions are symmetric under permutation of insertions."
    "Bosonic observable sector and the source finite-volume symmetry argument."
    "OS3 permutation symmetry is available."
    "OS reconstruction and P31."
    "The reconstructed Wightman distributions may fail the bosonic symmetry axiom."
    paperImport

oS4ClusterPropertySurface : ProofTargetSurface
oS4ClusterPropertySurface =
  mkProofTargetSurface
    "OS4ClusterProperty"
    "Eriksson 2602.0052 Thm 7.1 / Cor 7.3 through the DLR-LSI route"
    "Separated connected correlators decay exponentially in the admitted continuum-ready regime."
    "P12-P15 DLR-LSI and clustering route."
    "OS4 clustering is available at audit/source-intake level."
    "OS reconstruction, gap transfer, and P31."
    "Vacuum uniqueness and mass-gap transfer have no clustering input."
    auditTested

p31aAbstractOSReconstructionSurface : ProofTargetSurface
p31aAbstractOSReconstructionSurface =
  mkProofTargetSurfaceWithAuthority
    "P31aAbstractOSReconstruction"
    "DASHI abstract endpoint interface over the OS reconstruction theorem shape"
    "Assuming OS0-OS4, the endpoint lane exposes a reusable abstract OS reconstruction interface producing the Hilbert-space/Wightman package shape."
    "OS0-OS4 theorem surfaces; local endpoint queue."
    "A DASHI-owned abstract reconstruction boundary is available."
    "P31b YM OS-input bundle and the composite P31 endpoint surface."
    "The endpoint lane has no internal reconstruction interface."
    proved
    dashi-internal-proof "WightmanEndpointLemmaQueue.currentP31aAbstractOSReconstruction" consequence-proof proved

p31bYMOSInputsSurface : ProofTargetSurface
p31bYMOSInputsSurface =
  mkProofTargetSurfaceWithAuthority
    "P31bYMSatisfiesOSInputs"
    "DASHI mixed OS-input bundle over Eriksson 2602.0088, 2602.0052, and 2602.0092"
    "The Balaban/Eriksson Yang-Mills route supplies the OS input bundle OS0-OS4 and OS1 in the theorem-shaped form consumed by the abstract reconstruction interface."
    "Tier-1 OS inputs, DLR-LSI/cluster route for OS4, and O(4) covariance for OS1."
    "The YM route satisfies the OS input requirements as a bundled surface."
    "P31a abstract reconstruction and P31c cluster/gap bridge."
    "The endpoint lane cannot consume YM data as a single OS-input package."
    proved
    dashi-internal-proof "WightmanEndpointLemmaQueue.currentP31bYMSatisfiesOSInputs" consequence-proof proved

p31cClusterGapToPhysicalMassGapSurface : ProofTargetSurface
p31cClusterGapToPhysicalMassGapSurface =
  mkProofTargetSurfaceWithAuthority
    "P31cClusterGapToPhysicalMassGap"
    "DASHI mixed bridge over W.3 cluster-to-gap transfer and W.5 physical-scale identification"
    "OS4 clustering yields an abstract positive mass gap, and the source-side physical-scale identification anchors that gap to the Yang-Mills scale ΛYM."
    "OS4 cluster property, positive RG prefactor cN, positive Yang-Mills scale ΛYM, and the source mass-scale identification route."
    "The endpoint lane exposes the physical mass-gap bridge explicitly."
    "Composite P31 endpoint surface and downstream mass-gap statements."
    "The reconstructed gap is not linked to the physical Yang-Mills scale."
    proved
    dashi-internal-proof "WightmanEndpointLemmaQueue.currentP31cClusterGapToPhysicalMassGap" consequence-proof proved

record WightmanReconstructionLane : Set₁ where
  field
    os0Surface : ProofTargetSurface
    os1Surface : ProofTargetSurface
    os2Surface : ProofTargetSurface
    os3Surface : ProofTargetSurface
    os4Surface : ProofTargetSurface
    p31aSurface : ProofTargetSurface
    p31bSurface : ProofTargetSurface
    p31cSurface : ProofTargetSurface
    p31Surface : ProofTargetSurface

    os0Closed : proofTargetIsClosed os0Surface ≡ true
    os1Closed : proofTargetIsClosed os1Surface ≡ true
    os2Closed : proofTargetIsClosed os2Surface ≡ true
    os3Closed : proofTargetIsClosed os3Surface ≡ true
    os4Closed : proofTargetIsClosed os4Surface ≡ true
    p31aClosed : proofTargetIsClosed p31aSurface ≡ true
    p31bClosed : proofTargetIsClosed p31bSurface ≡ true
    p31cClosed : proofTargetIsClosed p31cSurface ≡ true
    p31Closed : proofTargetIsClosed p31Surface ≡ true

    sourceIntakeEndpointClosed : Bool
    constructiveAgdaEndpointClosed : Bool
    sourceIntakeEndpointClosedIsTrue : sourceIntakeEndpointClosed ≡ true
    constructiveAgdaEndpointClosedIsFalse :
      constructiveAgdaEndpointClosed ≡ false

    endpointBoundary : String
    endpointBoundaryIsCanonical :
      endpointBoundary ≡
      "OS0-OS4 and P31 are split into explicit theorem surfaces; P31a is the DASHI abstract reconstruction interface, P31b is the YM OS-input bundle, and P31c is the cluster/gap-to-physical-mass-gap bridge. The constructive Agda endpoint remains open."
    noClayPromotion : clayYangMillsPromoted ≡ false

canonicalWightmanReconstructionLane : WightmanReconstructionLane
canonicalWightmanReconstructionLane = record
  { os0Surface = oS0TemperednessSurface
  ; os1Surface = oS1EuclideanCovarianceSurface
  ; os2Surface = oS2ReflectionPositivitySurface
  ; os3Surface = oS3BosonicSymmetrySurface
  ; os4Surface = oS4ClusterPropertySurface
  ; p31aSurface = p31aAbstractOSReconstructionSurface
  ; p31bSurface = p31bYMOSInputsSurface
  ; p31cSurface = p31cClusterGapToPhysicalMassGapSurface
  ; p31Surface =
      mkProofTargetSurface
        "ImportedWightmanReconstructionWithMassGap"
        "Eriksson 2602.0092, Theorem 1.1 and §5"
        "Given OS0-OS4 plus the mass-gap hypotheses, one reconstructs a Hilbert space, cyclic vacuum, unitary Poincare representation, Wightman distributions, and a positive physical mass gap."
        "OS0-OS4, OS1 covariance, reflection positivity, clustering, nontriviality, and the source mass-gap transfer hypotheses."
        "The terminal Wightman endpoint is available as a source theorem surface."
        "Terminal YM mathematical sink P31."
        "No continuum Wightman QFT with positive mass gap is available."
        paperImport
  ; os0Closed = refl
  ; os1Closed = refl
  ; os2Closed = refl
  ; os3Closed = refl
  ; os4Closed = refl
  ; p31aClosed = refl
  ; p31bClosed = refl
  ; p31cClosed = refl
  ; p31Closed = refl
  ; sourceIntakeEndpointClosed = true
  ; constructiveAgdaEndpointClosed = false
  ; sourceIntakeEndpointClosedIsTrue = refl
  ; constructiveAgdaEndpointClosedIsFalse = refl
  ; endpointBoundary =
      "OS0-OS4 and P31 are split into explicit theorem surfaces; P31a is the DASHI abstract reconstruction interface, P31b is the YM OS-input bundle, and P31c is the cluster/gap-to-physical-mass-gap bridge. The constructive Agda endpoint remains open."
  ; endpointBoundaryIsCanonical = refl
  ; noClayPromotion = refl
  }
