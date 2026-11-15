module DASHI.Biology.BH4NOSCouplingEvidenceExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.GenericReceipt as Receipt
import DASHI.Biology.NitrogenOxideSpeciesCouplingExact as NOS

------------------------------------------------------------------------
-- Literature-backed NOS3/eNOS coupling evidence.
--
-- These sources pay a bounded biological relation: BH4 relative to NOS protein
-- and BH4:BH2 redox status regulate eNOS coupling, and perturbing BH4 recycling
-- can shift NO/superoxide output. They do not by themselves pay the DASHI
-- same-object/compartment/time coordinates required for a whole-system allocator
-- witness, nor do they globalize to NOS1/NOS2 or disease causation.
------------------------------------------------------------------------

crabtree2009Stoichiometry : Source.AttributedSource
crabtree2009Stoichiometry =
  Source.mkDOISource
    "Mark J Crabtree; Amy L Tatham; Yasir Al-Wakeel; Nicholas Warrick; Ashley B Hale; Shijie Cai; Keith M Channon; Nicholas J Alp"
    "Quantitative regulation of intracellular endothelial nitric-oxide synthase (eNOS) coupling by both tetrahydrobiopterin-eNOS stoichiometry and biopterin redox status: insights from cells with tet-regulated GTP cyclohydrolase I expression"
    "Journal of Biological Chemistry 284(2):1136-1144"
    "2009"
    "10.1074/jbc.M805403200"
    "https://pubmed.ncbi.nlm.nih.gov/19011239/"
    Source.academicArticleSource
    "primary eNOS/NOS3 evidence separating BH4:eNOS stoichiometry and BH4:BH2 redox status as coupling coordinates"
    Source.publicAttribution

crabtree2009Recycling : Source.AttributedSource
crabtree2009Recycling =
  Source.mkDOISource
    "Mark J Crabtree; Amy L Tatham; Ashley B Hale; Nicholas J Alp; Keith M Channon"
    "Critical role for tetrahydrobiopterin recycling by dihydrofolate reductase in regulation of endothelial nitric-oxide synthase coupling: relative importance of the de novo biopterin synthesis versus salvage pathways"
    "Journal of Biological Chemistry 284(41):28128-28136"
    "2009"
    "10.1074/jbc.M109.041483"
    "https://pubmed.ncbi.nlm.nih.gov/19666465/"
    Source.academicArticleSource
    "primary perturbational eNOS/NOS3 evidence: DHFR inhibition/knockdown lowers BH4 relative to BH2, reduces NO and increases eNOS-dependent superoxide"
    Source.publicAttribution

data NOS3EvidenceCoordinate : Set where
  bh4RelativeToNOS3 : NOS3EvidenceCoordinate
  bh4ToBh2RedoxRatio : NOS3EvidenceCoordinate
  nitricOxideOutput : NOS3EvidenceCoordinate
  superoxideOutput : NOS3EvidenceCoordinate
  recyclingPerturbation : NOS3EvidenceCoordinate

record NOS3CouplingEvidenceReceipt : Set where
  constructor nos3-coupling-evidence-receipt
  field
    receiptId : String
    source : Source.AttributedSource
    coordinates : List NOS3EvidenceCoordinate
    boundedReading : String
    isoform : NOS.NOSIsoform
    perturbational : Bool
    sameExperimentalSystem : Bool
    sameCellSingleObjectMeasurement : Bool
    directDiseaseMechanismEvidence : Bool
    directDiseaseMechanismEvidenceIsFalse : directDiseaseMechanismEvidence ≡ false

open NOS3CouplingEvidenceReceipt public

nos3StoichiometryEvidence : NOS3CouplingEvidenceReceipt
nos3StoichiometryEvidence =
  nos3-coupling-evidence-receipt
    "NOS3-BH4-E1"
    crabtree2009Stoichiometry
    ( bh4RelativeToNOS3 ∷ bh4ToBh2RedoxRatio ∷ nitricOxideOutput ∷ superoxideOutput ∷ [] )
    "In an eNOS expression system with controlled GTPCH/BH4 supply, both BH4 relative to eNOS and biopterin redox status contribute to coupling and NO-versus-superoxide output."
    NOS.endothelialNOS
    true
    true
    false
    false refl

nos3RecyclingPerturbationEvidence : NOS3CouplingEvidenceReceipt
nos3RecyclingPerturbationEvidence =
  nos3-coupling-evidence-receipt
    "NOS3-BH4-E2"
    crabtree2009Recycling
    ( recyclingPerturbation ∷ bh4ToBh2RedoxRatio ∷ nitricOxideOutput ∷ superoxideOutput ∷ [] )
    "DHFR inhibition or knockdown reduces BH4 relative to BH2 and shifts eNOS output toward reduced NO and increased eNOS-dependent superoxide in the studied endothelial/eNOS systems."
    NOS.endothelialNOS
    true
    true
    false
    false refl

record NOS3EvidenceBoundary : Set where
  constructor nos3-evidence-boundary
  field
    nos3EvidenceGlobalizesToNOS1 : Bool
    nos3EvidenceGlobalizesToNOS1IsFalse : nos3EvidenceGlobalizesToNOS1 ≡ false
    nos3EvidenceGlobalizesToNOS2 : Bool
    nos3EvidenceGlobalizesToNOS2IsFalse : nos3EvidenceGlobalizesToNOS2 ≡ false
    sameExperimentalSystemMeansSameSingleCellState : Bool
    sameExperimentalSystemMeansSameSingleCellStateIsFalse :
      sameExperimentalSystemMeansSameSingleCellState ≡ false
    couplingEvidencePaysWholeBH4Allocator : Bool
    couplingEvidencePaysWholeBH4AllocatorIsFalse : couplingEvidencePaysWholeBH4Allocator ≡ false
    couplingEvidenceEstablishesKitzerowDiseaseMechanism : Bool
    couplingEvidenceEstablishesKitzerowDiseaseMechanismIsFalse :
      couplingEvidenceEstablishesKitzerowDiseaseMechanism ≡ false

open NOS3EvidenceBoundary public

canonicalNOS3EvidenceBoundary : NOS3EvidenceBoundary
canonicalNOS3EvidenceBoundary =
  nos3-evidence-boundary false refl false refl false refl false refl false refl

canonicalBH4NOSCouplingEvidenceReceipt : Receipt.GenericReceipt
canonicalBH4NOSCouplingEvidenceReceipt =
  Receipt.mkNonPromotingReceipt
    "BH4 / NOS3 coupling evidence"
    "DASHI.Biology.BH4NOSCouplingEvidenceExact"
    "Crabtree et al. 2009 primary eNOS systems: BH4:eNOS + BH4:BH2 coordinates and DHFR/GTPCH perturbation -> NO/superoxide coupling readouts"
    "pays bounded NOS3/eNOS coupling and perturbation support while preserving source attribution and isoform scope"
    "NOS3 evidence does not globalize to NOS1/NOS2, same experimental system is not a same-single-cell state, and coupling support is not whole allocator or disease proof"
    "agda -i . DASHI/Biology/BH4NOSCouplingEvidenceExact.agda"
