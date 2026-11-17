module DASHI.Physics.Photovoltaic.GaAsKane369MaterialDiscriminatorExact where

-- 2026-11-16: first SOURCE-QUALIFIED real-material optical testbed,
-- NOT an inhabited physical 369-to-bulk-material welding theorem.
--
-- GaAs published k.p parameters (Kane 8-band model):
-- 300K Eg=1.422 eV, Kane Ep=28.8 eV, spin-orbit Delta=0.341 eV.
-- Original source: PROMIS/Lancaster 2016 GaAs material parameter table:
-- https://www.physics.lancs.ac.uk/promis/outputs/Scientific-EU-Deliverable-D1-2-Band-structure-parameters-established-f.pdf
-- Kane optical momentum coupling definition in Cambridge University Press:
-- https://doi.org/10.1017/9781009106153.002
-- GaAs zincblende Td is NOT inversion symmetric:
-- https://pmc.ncbi.nlm.nih.gov/articles/PMC6854082/
-- These are attribution sources; no ownership or priority is transferred.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369MagneticC3PhysicalRealizationExact as P
import DASHI.Physics.Photovoltaic.Atomic369C3DipoleSelectionExact as Optical
import DASHI.Algebra.TriadicDepthOneCharacters as Characters
import DASHI.Physics.Photovoltaic.Atomic369GaAs111TrigonalCharacterExact as Trigonal

-- Scale and temperature are explicit, so eV and meV never get silently mixed.
record GaAsKaneParameterSource : Set where
  constructor gaasKaneParameterSource
  field
    Eg300KmeV : Nat
    kaneEnergyTenthsEV : Nat
    spinOrbitSplitmeV : Nat
    source : String
    directGammaGapSourcePaid : Bool
    nonzeroSPOpticalMomentumSourcePaid : Bool
    inversionSymmetryForbidsAllE1 : Bool
    full369PhysicalMapPaid : Bool
    fullSolarDeviceJVPaid : Bool

gaasKane300K : GaAsKaneParameterSource
gaasKane300K =
  gaasKaneParameterSource
    1422 288 341
    "PROMIS/Lancaster GaAs 300K 8-band k.p parameter table; Kane optical momentum and Cambridge band theory; 2016 source"
    true true false false false

open GaAsKaneParameterSource public

gaasHasPublishedDirectGap : directGammaGapSourcePaid gaasKane300K ≡ true
gaasHasPublishedDirectGap = refl

gaasPublishedKaneIsOpticalSource : nonzeroSPOpticalMomentumSourcePaid gaasKane300K ≡ true
gaasPublishedKaneIsOpticalSource = refl

gaasDoesNotPay369SameMaterialMapping : full369PhysicalMapPaid gaasKane300K ≡ false
gaasDoesNotPay369SameMaterialMapping = refl

-- The angular p-sector representation is a source-side DONOR only.
-- To count as '369-derived' the next proof must identify it with the
-- SAME material's Bloch/defect optically active valence states, and
-- the material must contain an allowed opposite-character s-like band,
-- with a physically measured dipole and charge extraction.
record GaAsAtomic369ToKaneWeld : Set₁ where
  field
    MaterialState : Set
    ValenceBlochState : Set
    ConductionBlochState : Set
    MomentumAmplitude : Set
    mapOriginalP : P.MagneticState -> ValenceBlochState
    mapKaneConduction : MaterialState -> ConductionBlochState

    -- A physical spatial C3 rotation changes an eigenstate by a phase;
    -- it does NOT permute its eigenstate labels.
    phaseMultiply : Characters.C3Phase -> ValenceBlochState -> ValenceBlochState
    phaseIdentity :
      (v : ValenceBlochState) ->
      phaseMultiply Characters.phase0 v ≡ v
    phaseComposition :
      (a b : Characters.C3Phase) (v : ValenceBlochState) ->
      phaseMultiply (Characters.multiplyPhase a b) v
      ≡ phaseMultiply a (phaseMultiply b v)

    crystalC3Rotation : ValenceBlochState -> ValenceBlochState
    sourceToCrystalC3Intertwiner :
      (m : P.MagneticState) ->
      crystalC3Rotation (mapOriginalP m)
      ≡ phaseMultiply (P.rotationPhase m) (mapOriginalP m)

    -- Independent residue/charge permutation: NOT physical rotation.
    chargeSectorTransport : ValenceBlochState -> ValenceBlochState
    sourceToCrystalChargeStepIntertwiner :
      (m : P.MagneticState) ->
      chargeSectorTransport (mapOriginalP m)
      ≡ mapOriginalP (P.chargePositiveStep m)

    kaneOpticalMomentum : ValenceBlochState -> ConductionBlochState -> MomentumAmplitude
    nonzeroKaneSource : String
    measuredKaneAmplitudeSource : String
    measuredSolarEQESource : String
    measuredUnbiasedJVSource : String
    independentMaterialAndC3Control : String

-- Separate exact finite character/sector witnesses exist in the imported
-- Trigonal module; the analytic U is checked separately in SymPy. Neither
-- inhabits this SAME-MATERIAL GaAs Bloch/8-band optical record.
-- Zincblende Td has no inversion centre: 's-like' and 'p-like' are
-- orbital representation types, not exact even/odd parity eigenlabels.

record GaAsKaneTemperatureConsistency : Set where
  constructor gaasKaneTemperatureConsistency
  field
    gap0KmeV : Nat
    gap300KmeV : Nat
    kaneEnergyTenthsEV : Nat
    spinOrbitmeV : Nat
    remoteFNegativeHundredths : Nat
    sourceDOI : String

-- Vurgaftman/Meyer/Ram-Mohan 2001 Table I supplies recommended
-- Eg(0K)=1.519 eV and F=-1.94. Reusing the 0K F and Kane E_P with the
-- 300K gap changes the derived effective mass: m*/m0=0.06224,
-- not the incorrectly quoted 0.0664. The 0K calculation gives 0.06702.
gaasKaneTemperatureReceipt : GaAsKaneTemperatureConsistency
gaasKaneTemperatureReceipt =
  gaasKaneTemperatureConsistency
    1519 1422 288 341 194
    "10.1063/1.1368156; 0K and 300K gap+mass comparisons"
