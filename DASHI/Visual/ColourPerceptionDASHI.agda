module DASHI.Visual.ColourPerceptionDASHI where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Biology.AnimalSenseObservationThreadDischarge as AnimalSense
import DASHI.Combinatorics.TriadicVideoCodecObservationQuotient as Codec

------------------------------------------------------------------------
-- Guarded visual-colour / perception lane.
--
-- This module intentionally creates the visual-colour carrier that the repo
-- did not previously contain.  Existing local names are kept separated:
--   * RGB* elsewhere can mean Renormalization Group Benchmark scoring.
--   * Colour in QFT modules can mean SU(3) / QCD colour charge.
--   * Spectral in PNF/operator contexts is not optical colour appearance.
--
-- The present file is candidate-only: it records a DASHI-compatible
-- observation-transport surface for colour/perception without claiming qualia
-- recovery, brain closure, exact spectrum recovery, device-independent colour
-- truth, or universal aesthetic authority.

------------------------------------------------------------------------
-- Ternary / 369 primitives.

data Tri : Set where
  neg : Tri
  neu : Tri
  pos : Tri

data NonaryPhase : Set where
  n00 n01 n02 n03 n04 n05 n06 n07 n08 : NonaryPhase

------------------------------------------------------------------------
-- Optical/contact, receptor, opponent and colour-space surfaces.

record SpectralContact : Set where
  field
    contactToken : Nat

record ReceptorQuotient : Set where
  field
    longCone   : Nat
    mediumCone : Nat
    shortCone  : Nat

record OpponentResidue : Set where
  field
    redGreen   : Tri
    blueYellow : Tri
    lightDark  : Tri

record RGBA : Set where
  field
    rgbaRed   : Nat
    rgbaGreen : Nat
    rgbaBlue  : Nat
    rgbaAlpha : Nat

record CMYKA : Set where
  field
    cmykaCyan    : Nat
    cmykaMagenta : Nat
    cmykaYellow  : Nat
    cmykaKey     : Nat
    cmykaAlpha   : Nat

data Hue24 : Set where
  h00 h01 h02 h03 h04 h05 h06 h07 : Hue24
  h08 h09 h10 h11 h12 h13 h14 h15 : Hue24
  h16 h17 h18 h19 h20 h21 h22 h23 : Hue24

data PCCSTone : Set where
  vivid bright strong deep : PCCSTone
  light soft dull dark : PCCSTone
  pale grayish lightGrayish darkGrayish : PCCSTone

record PCCS : Set where
  field
    hue  : Hue24
    tone : PCCSTone

data ColourCoordinateSurface : Set where
  pccsSurface : ColourCoordinateSurface
  rgbaSurface : ColourCoordinateSurface
  cmykaSurface : ColourCoordinateSurface
  spectralContactSurface : ColourCoordinateSurface
  receptorSurface : ColourCoordinateSurface
  opponent369Surface : ColourCoordinateSurface
  hypervoxelSurface : ColourCoordinateSurface
  btBraidSurface : ColourCoordinateSurface

canonicalColourSurfaceLadder : List ColourCoordinateSurface
canonicalColourSurfaceLadder =
  spectralContactSurface
  ∷ receptorSurface
  ∷ opponent369Surface
  ∷ hypervoxelSurface
  ∷ btBraidSurface
  ∷ pccsSurface
  ∷ rgbaSurface
  ∷ cmykaSurface
  ∷ []

------------------------------------------------------------------------
-- MCCP: Multimodal Colour Contact Partition.
--
-- The coarse perceptual-contact quotient is TriColourResidue³.  It has 27
-- cells, represented explicitly as an MCCP partition.  This is a DASHI
-- quotient, not a theorem that human colour experience has exactly 27 states.

data MCCPCell : Set where
  mccpNNN mccpNN0 mccpNNP : MCCPCell
  mccpN0N mccpN00 mccpN0P : MCCPCell
  mccpNPN mccpNP0 mccpNPP : MCCPCell
  mccp0NN mccp0N0 mccp0NP : MCCPCell
  mccp00N mccp000 mccp00P : MCCPCell
  mccp0PN mccp0P0 mccp0PP : MCCPCell
  mccpPNN mccpPN0 mccpPNP : MCCPCell
  mccpP0N mccpP00 mccpP0P : MCCPCell
  mccpPPN mccpPP0 mccpPPP : MCCPCell

triColourResidueToMCCP : OpponentResidue → MCCPCell
triColourResidueToMCCP record { redGreen = neg ; blueYellow = neg ; lightDark = neg } = mccpNNN
triColourResidueToMCCP record { redGreen = neg ; blueYellow = neg ; lightDark = neu } = mccpNN0
triColourResidueToMCCP record { redGreen = neg ; blueYellow = neg ; lightDark = pos } = mccpNNP
triColourResidueToMCCP record { redGreen = neg ; blueYellow = neu ; lightDark = neg } = mccpN0N
triColourResidueToMCCP record { redGreen = neg ; blueYellow = neu ; lightDark = neu } = mccpN00
triColourResidueToMCCP record { redGreen = neg ; blueYellow = neu ; lightDark = pos } = mccpN0P
triColourResidueToMCCP record { redGreen = neg ; blueYellow = pos ; lightDark = neg } = mccpNPN
triColourResidueToMCCP record { redGreen = neg ; blueYellow = pos ; lightDark = neu } = mccpNP0
triColourResidueToMCCP record { redGreen = neg ; blueYellow = pos ; lightDark = pos } = mccpNPP
triColourResidueToMCCP record { redGreen = neu ; blueYellow = neg ; lightDark = neg } = mccp0NN
triColourResidueToMCCP record { redGreen = neu ; blueYellow = neg ; lightDark = neu } = mccp0N0
triColourResidueToMCCP record { redGreen = neu ; blueYellow = neg ; lightDark = pos } = mccp0NP
triColourResidueToMCCP record { redGreen = neu ; blueYellow = neu ; lightDark = neg } = mccp00N
triColourResidueToMCCP record { redGreen = neu ; blueYellow = neu ; lightDark = neu } = mccp000
triColourResidueToMCCP record { redGreen = neu ; blueYellow = neu ; lightDark = pos } = mccp00P
triColourResidueToMCCP record { redGreen = neu ; blueYellow = pos ; lightDark = neg } = mccp0PN
triColourResidueToMCCP record { redGreen = neu ; blueYellow = pos ; lightDark = neu } = mccp0P0
triColourResidueToMCCP record { redGreen = neu ; blueYellow = pos ; lightDark = pos } = mccp0PP
triColourResidueToMCCP record { redGreen = pos ; blueYellow = neg ; lightDark = neg } = mccpPNN
triColourResidueToMCCP record { redGreen = pos ; blueYellow = neg ; lightDark = neu } = mccpPN0
triColourResidueToMCCP record { redGreen = pos ; blueYellow = neg ; lightDark = pos } = mccpPNP
triColourResidueToMCCP record { redGreen = pos ; blueYellow = neu ; lightDark = neg } = mccpP0N
triColourResidueToMCCP record { redGreen = pos ; blueYellow = neu ; lightDark = neu } = mccpP00
triColourResidueToMCCP record { redGreen = pos ; blueYellow = neu ; lightDark = pos } = mccpP0P
triColourResidueToMCCP record { redGreen = pos ; blueYellow = pos ; lightDark = neg } = mccpPPN
triColourResidueToMCCP record { redGreen = pos ; blueYellow = pos ; lightDark = neu } = mccpPP0
triColourResidueToMCCP record { redGreen = pos ; blueYellow = pos ; lightDark = pos } = mccpPPP

record MCCPWitness : Set where
  field
    opponentResidue : OpponentResidue
    cell : MCCPCell
    cellMatchesResidue : triColourResidueToMCCP opponentResidue ≡ cell
    partitionReading : String

------------------------------------------------------------------------
-- Hypervoxel and balanced-ternary braid surface.

record ColourHypervoxel : Set where
  field
    cellToken : Nat
    spectral : Maybe SpectralContact
    receptor : Maybe ReceptorQuotient
    opponent : OpponentResidue
    phase369 : NonaryPhase
    mccpCell : MCCPCell
    frontier : Tri
    residualMagnitude : Nat
    memoryTrace : Nat

record BTColourBraid : Set where
  field
    redGreenResiduals : List Tri
    blueYellowResiduals : List Tri
    lightDarkResiduals : List Tri
    alphaContextResiduals : List Tri

------------------------------------------------------------------------
-- Formal relationship to existing codec and sensory guard architecture.

colourBraidUsesCodecLayer : Codec.CodecPipelineLayer
colourBraidUsesCodecLayer = Codec.balancedTernaryPlaneLayer

colourPerceptionInheritsNoQualiaBoundary : AnimalSense.ThreadDischargeBoundary
colourPerceptionInheritsNoQualiaBoundary = AnimalSense.noQualiaRecovery

colourPerceptionInheritsNoCrossSenseBoundary : AnimalSense.ThreadDischargeBoundary
colourPerceptionInheritsNoCrossSenseBoundary =
  AnimalSense.noArbitraryCrossSenseIdentityDischarge

------------------------------------------------------------------------
-- Candidate-only transport surface.

record ColourPerceptionTransport : Set₁ where
  field
    spectralToReceptor : SpectralContact → ReceptorQuotient
    receptorToOpponent : ReceptorQuotient → OpponentResidue
    opponentToPhase369 : OpponentResidue → NonaryPhase
    hypervoxelise : SpectralContact → ColourHypervoxel
    braidResidual : ColourHypervoxel → BTColourBraid
    toPCCS : ColourHypervoxel → Maybe PCCS
    toRGBA : ColourHypervoxel → Maybe RGBA
    toCMYKA : ColourHypervoxel → Maybe CMYKA
    transportReading : String

record ColourPerceptionBoundary : Set where
  field
    noQualiaRecovery : Bool
    noExactSpectrumRecovery : Bool
    noBrainClosure : Bool
    noUniversalAesthetic : Bool
    noDeviceTruthPromotion : Bool
    noPCCSTruthPromotion : Bool
    noCrossSurfaceIdentity : Bool
    noReceiptlessPromotion : Bool
    boundaryReading : String

canonicalColourPerceptionBoundary : ColourPerceptionBoundary
canonicalColourPerceptionBoundary =
  record
    { noQualiaRecovery = true
    ; noExactSpectrumRecovery = true
    ; noBrainClosure = true
    ; noUniversalAesthetic = true
    ; noDeviceTruthPromotion = true
    ; noPCCSTruthPromotion = true
    ; noCrossSurfaceIdentity = true
    ; noReceiptlessPromotion = true
    ; boundaryReading =
        "Colour/perception is candidate-only: opponent residues, 369 phase, hypervoxels, BT-braid refinement, PCCS, RGBA and CMYKA are guarded projection surfaces, not qualia or device-independent truth."
    }

record ColourPerceptionNonPromotionCertificate
    (transport : ColourPerceptionTransport) : Set where
  field
    boundary : ColourPerceptionBoundary
    boundaryIsCanonical : boundary ≡ canonicalColourPerceptionBoundary
    qualiaRecovered : Bool
    qualiaRecoveredIsFalse : qualiaRecovered ≡ false
    exactSpectrumRecovered : Bool
    exactSpectrumRecoveredIsFalse : exactSpectrumRecovered ≡ false
    universalAestheticPromoted : Bool
    universalAestheticPromotedIsFalse : universalAestheticPromoted ≡ false
    pccsEqualsRGBA : Bool
    pccsEqualsRGBAIsFalse : pccsEqualsRGBA ≡ false
    rgbaEqualsCMYKA : Bool
    rgbaEqualsCMYKAIsFalse : rgbaEqualsCMYKA ≡ false
    certificateReading : String

canonicalColourPerceptionNonPromotionCertificate :
  (transport : ColourPerceptionTransport) →
  ColourPerceptionNonPromotionCertificate transport
canonicalColourPerceptionNonPromotionCertificate transport =
  record
    { boundary = canonicalColourPerceptionBoundary
    ; boundaryIsCanonical = refl
    ; qualiaRecovered = false
    ; qualiaRecoveredIsFalse = refl
    ; exactSpectrumRecovered = false
    ; exactSpectrumRecoveredIsFalse = refl
    ; universalAestheticPromoted = false
    ; universalAestheticPromotedIsFalse = refl
    ; pccsEqualsRGBA = false
    ; pccsEqualsRGBAIsFalse = refl
    ; rgbaEqualsCMYKA = false
    ; rgbaEqualsCMYKAIsFalse = refl
    ; certificateReading =
        "PCCS is a design coordination quotient, RGBA is a display carrier, and CMYKA is a print/material carrier.  The MCCP maps TriColourResidue^3 to 27 coarse contact cells without promoting perception truth."
    }

------------------------------------------------------------------------
-- Toy canonical inhabitant: enough structure for downstream modules to refer
-- to the lane while keeping every bridge candidate-only.

canonicalSpectralContact : SpectralContact
canonicalSpectralContact =
  record { contactToken = 0 }

canonicalReceptorQuotient : ReceptorQuotient
canonicalReceptorQuotient =
  record { longCone = 0 ; mediumCone = 0 ; shortCone = 0 }

canonicalOpponentResidue : OpponentResidue
canonicalOpponentResidue =
  record { redGreen = neu ; blueYellow = neu ; lightDark = neu }

canonicalMCCPWitness : MCCPWitness
canonicalMCCPWitness =
  record
    { opponentResidue = canonicalOpponentResidue
    ; cell = mccp000
    ; cellMatchesResidue = refl
    ; partitionReading =
        "TriColourResidue^3 maps to the central MCCP neutral cell in the canonical toy witness."
    }

canonicalColourHypervoxel : ColourHypervoxel
canonicalColourHypervoxel =
  record
    { cellToken = 0
    ; spectral = just canonicalSpectralContact
    ; receptor = just canonicalReceptorQuotient
    ; opponent = canonicalOpponentResidue
    ; phase369 = n04
    ; mccpCell = mccp000
    ; frontier = neu
    ; residualMagnitude = 0
    ; memoryTrace = 0
    }

canonicalBTColourBraid : BTColourBraid
canonicalBTColourBraid =
  record
    { redGreenResiduals = neu ∷ []
    ; blueYellowResiduals = neu ∷ []
    ; lightDarkResiduals = neu ∷ []
    ; alphaContextResiduals = neu ∷ []
    }

canonicalPCCS : PCCS
canonicalPCCS =
  record { hue = h00 ; tone = grayish }

canonicalRGBA : RGBA
canonicalRGBA =
  record { rgbaRed = 0 ; rgbaGreen = 0 ; rgbaBlue = 0 ; rgbaAlpha = 0 }

canonicalCMYKA : CMYKA
canonicalCMYKA =
  record { cmykaCyan = 0 ; cmykaMagenta = 0 ; cmykaYellow = 0 ; cmykaKey = 0 ; cmykaAlpha = 0 }

canonicalColourPerceptionTransport : ColourPerceptionTransport
canonicalColourPerceptionTransport =
  record
    { spectralToReceptor = λ _ → canonicalReceptorQuotient
    ; receptorToOpponent = λ _ → canonicalOpponentResidue
    ; opponentToPhase369 = λ _ → n04
    ; hypervoxelise = λ _ → canonicalColourHypervoxel
    ; braidResidual = λ _ → canonicalBTColourBraid
    ; toPCCS = λ _ → just canonicalPCCS
    ; toRGBA = λ _ → just canonicalRGBA
    ; toCMYKA = λ _ → just canonicalCMYKA
    ; transportReading =
        "DASHI visual colour transport: spectral contact → receptor quotient → opponent ternary residue → 369 phase → hypervoxel field → BT-braid residual → PCCS/RGBA/CMYKA guarded projection."
    }

canonicalColourPerceptionCertificate :
  ColourPerceptionNonPromotionCertificate canonicalColourPerceptionTransport
canonicalColourPerceptionCertificate =
  canonicalColourPerceptionNonPromotionCertificate canonicalColourPerceptionTransport
