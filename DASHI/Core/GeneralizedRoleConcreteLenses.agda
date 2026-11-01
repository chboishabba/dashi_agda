module DASHI.Core.GeneralizedRoleConcreteLenses where

open import Agda.Primitive using (Setω)
open import DASHI.Core.Prelude
open import DASHI.Core.FormalRole
open import DASHI.Core.ProofLens
import DASHI.Reasoning.UnifiedCarryBraidReceipt as CarryBraid
import DASHI.Analysis.MaassFourierCarrier as MFC
import DASHI.Analysis.MaassSpectralCertification as MSC
import DASHI.Analysis.Maass.ResidualToSpectralEnclosureTheorem as Spectral

------------------------------------------------------------------------
-- Balanced-ternary / braid domain.

CarryBraidRole : FormalRole → Set
CarryBraidRole carrierSpaceRole    = CarryBraid.SharedCarrySurface
CarryBraidRole stateRole           = CarryBraid.SharedCarrySurface
CarryBraidRole operatorRole        = CarryBraid.UnifiedCarryBraidReceipt
CarryBraidRole observableRole      = CarryBraid.BraidTensionReading
CarryBraidRole spectrumToolRole    = CarryBraid.UnifiedCarryOpenObligation
CarryBraidRole boundaryGateRole    = CarryBraid.UnifiedCarryNonClaim
CarryBraidRole obstructionRole     = CarryBraid.UnifiedCarryOpenObligation
CarryBraidRole algebraRole         = CarryBraid.SharedCarrySurface
CarryBraidRole proofObligationRole = CarryBraid.UnifiedCarryOpenObligation
CarryBraidRole decompositionRole   = CarryBraid.UnifiedCarryBraidReceipt
CarryBraidRole hamiltonianRole     = CarryBraid.StabilityWindowReading
CarryBraidRole metricRole          = CarryBraid.StabilityWindowReading
CarryBraidRole projectionRole      = CarryBraid.UnifiedCarryBraidReceipt
CarryBraidRole residualRole        = CarryBraid.UnifiedCarryOpenObligation
CarryBraidRole receiptRole         = CarryBraid.UnifiedCarryBraidReceipt
CarryBraidRole functorRole         = CarryBraid.SharedCarrySurface
CarryBraidRole transitionRole      = CarryBraid.SharedCarrySurface
CarryBraidRole invariantRole       = CarryBraid.UnifiedCarryNonClaim
CarryBraidRole symmetryRole        = CarryBraid.BraidTensionReading
CarryBraidRole modeRole            = CarryBraid.SharedCarrySurface
CarryBraidRole sourceRole          = CarryBraid.SharedCarrySurface
CarryBraidRole sinkRole            = CarryBraid.SharedCarrySurface
CarryBraidRole flowRole            = CarryBraid.SharedCarrySurface
CarryBraidRole constraintRole      = CarryBraid.UnifiedCarryNonClaim
CarryBraidRole remedyRole          = CarryBraid.UnifiedCarryOpenObligation

carryBraidDomain : RoleFamily
carryBraidDomain =
  record
    { Carrier  = CarryBraid.SharedCarrySurface
    ; RoleType = CarryBraidRole
    }

data CarryBraidLensWitness :
  ProofLens →
  (r : FormalRole) →
  CarryBraidRole r →
  Set where
  btBraidReceiptWitness :
    (receipt : CarryBraid.UnifiedCarryBraidReceipt) →
    CarryBraidLensWitness btBraidLens receiptRole receipt

  btBraidResidualWitness :
    (obligation : CarryBraid.UnifiedCarryOpenObligation) →
    CarryBraidLensWitness btBraidLens residualRole obligation

  btBraidHamiltonianBoundary :
    (window : CarryBraid.StabilityWindowReading) →
    CarryBraidLensWitness hamiltonianLens hamiltonianRole window

carryBraidLenses : LensFamily carryBraidDomain
carryBraidLenses = record { LensWitness = CarryBraidLensWitness }

------------------------------------------------------------------------
-- Maass spectral domain.
--
-- A theorem is supplied as a genuine spectral witness rather than a status
-- Boolean.  The many analytic parameters remain explicit, as in the source
-- theorem, so this adapter introduces no new spectral claim.

record MaassSpectralPayload : Setω where
  field
    Γ : MFC.ΓMaass
    candidate : MSC.CandidateMaassForm Γ

MaassRole : FormalRole → Setω
MaassRole carrierSpaceRole    = MaassSpectralPayload
MaassRole stateRole           = MaassSpectralPayload
MaassRole operatorRole        = MaassSpectralPayload
MaassRole observableRole      = MaassSpectralPayload
MaassRole spectrumToolRole    = MaassSpectralPayload
MaassRole boundaryGateRole    = MaassSpectralPayload
MaassRole obstructionRole     = MaassSpectralPayload
MaassRole algebraRole         = MaassSpectralPayload
MaassRole proofObligationRole = MaassSpectralPayload
MaassRole decompositionRole   = MaassSpectralPayload
MaassRole hamiltonianRole     = MaassSpectralPayload
MaassRole metricRole          = MaassSpectralPayload
MaassRole projectionRole      = MaassSpectralPayload
MaassRole residualRole        = MaassSpectralPayload
MaassRole receiptRole         = MaassSpectralPayload
MaassRole functorRole         = MaassSpectralPayload
MaassRole transitionRole      = MaassSpectralPayload
MaassRole invariantRole       = MaassSpectralPayload
MaassRole symmetryRole        = MaassSpectralPayload
MaassRole modeRole            = MaassSpectralPayload
MaassRole sourceRole          = MaassSpectralPayload
MaassRole sinkRole            = MaassSpectralPayload
MaassRole flowRole            = MaassSpectralPayload
MaassRole constraintRole      = MaassSpectralPayload
MaassRole remedyRole          = MaassSpectralPayload

-- The universe-polymorphic Maass payload is kept in a dedicated large role
-- family rather than forced into the small RoleFamily prototype.
record MaassSpectralWitness (payload : MaassSpectralPayload) : Setω where
  open MaassSpectralPayload payload
  field
    GenuineForm SpectralInterval Radius Cusp SpectralParameter ConstantTerm : Set
    eigenvalueIn : GenuineForm → SpectralInterval → Set
    candidateWithin : MSC.CandidateMaassForm Γ → GenuineForm → Radius → Set
    EisensteinFamily : Cusp → SpectralParameter → Set
    constantTerm : MSC.CandidateMaassForm Γ → Cusp → ConstantTerm
    constantTermIsZero : ConstantTerm → Set
    continuousProjectionSmall : MSC.CandidateMaassForm Γ → Set
    windowAvoidsResidualSpectrum : SpectralInterval → Set
    windowSeparatedFromContinuousSpectrum : SpectralInterval → Set
    enclosure :
      Spectral.MaassSpectralEnclosureTheorem
        candidate
        GenuineForm SpectralInterval Radius Cusp SpectralParameter ConstantTerm
        eigenvalueIn candidateWithin EisensteinFamily constantTerm
        constantTermIsZero continuousProjectionSmall
        windowAvoidsResidualSpectrum
        windowSeparatedFromContinuousSpectrum
