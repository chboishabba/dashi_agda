module DASHI.Physics.YangMills.BalabanClayGate4PrimaryTargetAndAttachmentAuditExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Primary-source target ledger.
------------------------------------------------------------------------

data VerificationStatus : Set where
  pendingPrimarySourceCheck primarySourceVerified : VerificationStatus

record PrimaryGate4Target : Set where
  constructor primaryTarget
  field
    authors : String
    title : String
    venueYearPages : String
    doi : String
    location : String
    targetStatement : String
    verificationStatus : VerificationStatus
    relationshipToDASHI : String

open PrimaryGate4Target public

balabanLargeFieldPartII : String
balabanLargeFieldPartII =
  "Tadeusz Bałaban, Large Field Renormalization. II. Localization, Exponentiation, and Bounds for the R Operation"

tOperationEquation189 : PrimaryGate4Target
tOperationEquation189 = primaryTarget
  "Tadeusz Bałaban"
  "Large Field Renormalization. II. Localization, Exponentiation, and Bounds for the R Operation"
  "Communications in Mathematical Physics 122 (1989), 355--392"
  "10.1007/BF01238433"
  "equation (1.89), p. 387"
  "T_k(Y)1 <= exp(-(2/(1+beta_0)) p_0(g_k))"
  pendingPrimarySourceCheck
  "exact target of ExactBalabanTOperationSmallFactor; the viXra transcription is not theorem authority"

rOperationEquation1100 : PrimaryGate4Target
rOperationEquation1100 = primaryTarget
  "Tadeusz Bałaban"
  "Large Field Renormalization. II. Localization, Exponentiation, and Bounds for the R Operation"
  "Communications in Mathematical Physics 122 (1989), 355--392"
  "10.1007/BF01238433"
  "equation (1.100), p. 388"
  "|R^(k)(X;omega)| <= exp(-p_0(g_k)) exp(-kappa d_k(X)), uniformly in omega and volume"
  pendingPrimarySourceCheck
  "exact target of ROperationDecayDerivation"

boundaryEquation169 : PrimaryGate4Target
boundaryEquation169 = primaryTarget
  "Tadeusz Bałaban"
  "Large Field Renormalization. II. Localization, Exponentiation, and Bounds for the R Operation"
  "Communications in Mathematical Physics 122 (1989), 355--392"
  "10.1007/BF01238433"
  "equation (1.69), p. 377"
  "boundary activity controlled by the accumulated determining-set intersections"
  pendingPrimarySourceCheck
  "target for BoundarySupportReinjectionLaws and next-scale determining-set ownership"

p0SectionOneFour : PrimaryGate4Target
p0SectionOneFour = primaryTarget
  "Tadeusz Bałaban"
  "Large Field Renormalization. II. Localization, Exponentiation, and Bounds for the R Operation"
  "Communications in Mathematical Physics 122 (1989), 355--392"
  "10.1007/BF01238433"
  "Section 1.4, p. 362"
  "p_0(g) has a superlinear logarithmic lower-growth condition at small coupling"
  pendingPrimarySourceCheck
  "target for P0SuperlinearLogGrowth; exact constants and quantifiers must be read from the primary paper"

inductiveTheoremOne : PrimaryGate4Target
inductiveTheoremOne = primaryTarget
  "Tadeusz Bałaban"
  "Large Field Renormalization. II. Localization, Exponentiation, and Bounds for the R Operation"
  "Communications in Mathematical Physics 122 (1989), 355--392"
  "10.1007/BF01238433"
  "Theorem 1, p. 388"
  "the complete small-/large-field step preserves the inductive effective-action parameters"
  pendingPrimarySourceCheck
  "target for Gate4UVCompletionPackage"

primaryGate4Targets : List PrimaryGate4Target
primaryGate4Targets =
  tOperationEquation189 ∷ rOperationEquation1100 ∷ boundaryEquation169 ∷
  p0SectionOneFour ∷ inductiveTheoremOne ∷ []

------------------------------------------------------------------------
-- Secondary locator quarantine.
------------------------------------------------------------------------

record SecondaryLocator : Set where
  constructor locator
  field
    authors : String
    title : String
    venueOrRepository : String
    identifier : String
    doi : String
    admissibleAsAuthority : Bool
    usableAsLocator : Bool
    primaryVerificationRequired : Bool
    auditNote : String

open SecondaryLocator public

erikssonInterfaceLocator : SecondaryLocator
erikssonInterfaceLocator = locator
  "Lluis Eriksson"
  "Interface Lemmas for the Multiscale Proof of the Lattice Yang--Mills Mass Gap"
  "viXra, February 2026"
  "viXra:2602.0052v1"
  "no DOI recorded"
  false
  true
  true
  "use only to locate Bałaban equation/page references; its self-published completion chain is not imported"

erikssonUVLocator : SecondaryLocator
erikssonUVLocator = locator
  "Lluis Eriksson"
  "Ultraviolet Stability for Four-Dimensional Lattice Yang--Mills Theory: Closing the Bałaban--Doob Circuit under a Quantitative Blocking Hypothesis"
  "viXra, February 2026"
  "viXra:2602.0077v1"
  "no DOI recorded"
  false
  true
  true
  "conditional blocked-observable argument; squared-oscillation hypothesis, OS positivity, thermodynamic limit and mass gap remain outside its result"

------------------------------------------------------------------------
-- Uploaded attachment scope audit.
------------------------------------------------------------------------

data AttachmentScope : Set where
  gate4Primary gate4SecondaryLocator harmonicAnalysisOutsideGate4 : AttachmentScope

record AttachmentAudit : Set where
  constructor attachment
  field
    authors : String
    title : String
    identifier : String
    doi : String
    scope : AttachmentScope
    importedIntoGate4 : Bool
    possibleRepositoryConsumer : String
    reason : String

open AttachmentAudit public

dongLiBernsteinAttachment : AttachmentAudit
dongLiBernsteinAttachment = attachment
  "Dong Li"
  "On a Frequency Localized Bernstein Inequality and Some Generalized Poincare-Type Inequalities"
  "arXiv:1212.0183v1"
  "no DOI recorded in the uploaded paper"
  harmonicAnalysisOutsideGate4
  false
  "Navier--Stokes/fractional-dissipation or Littlewood--Paley harmonic-analysis lanes"
  "the paper proves frequency-localized Bernstein and periodic Poincare-type inequalities; it does not define or bound Bałaban T/R operations"

primaryTargetMetadataLevel : ProofLevel
primaryTargetMetadataLevel = machineChecked

secondaryLocatorQuarantineLevel : ProofLevel
secondaryLocatorQuarantineLevel = machineChecked

attachmentScopeAuditLevel : ProofLevel
attachmentScopeAuditLevel = machineChecked

primaryEquationStatementVerificationLevel : ProofLevel
primaryEquationStatementVerificationLevel = conditional
