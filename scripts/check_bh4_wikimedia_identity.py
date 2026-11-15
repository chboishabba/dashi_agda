from pathlib import Path

root = Path(__file__).resolve().parents[1]

identity = root / "DASHI/Wikimedia/BH4ProteinWikimediaIdentityExact.agda"
regression = root / "DASHI/Wikimedia/BH4ProteinWikimediaIdentityRegression.agda"
focused = root / "DASHI/Wikimedia/BH4ProteinWikimediaEverything.agda"
biology_root = root / "DASHI/Biology/KitzerowBH4EvidenceEverything.agda"
acquirer = root / "scripts/acquire_wikimedia_bio_identity.py"
uniprot_acquirer = root / "scripts/acquire_uniprot_bio_certificate.py"

for path in [identity, regression, focused, biology_root, acquirer, uniprot_acquirer]:
    assert path.exists(), f"missing BH4 Wikimedia identity file: {path.relative_to(root)}"

identity_text = identity.read_text()
regression_text = regression.read_text()
focused_text = focused.read_text()
biology_root_text = biology_root.read_text()
acquirer_text = acquirer.read_text()

for token in [
    "SnowballExternalIdentityAvailabilityExact",
    "bh4IdentityPanel",
    "acquiredBH4WikimediaPanel",
    "WikimediaPanelAcquisitionSummary",
    '"15" "1" "0" "0" true "7/16" false',
    "P352",
    "P702",
    "P688",
    "Q5",
    "Q1487359",
    "Q21101579",
    "Q21106788",
    "Q409532",
    "Q21204380",
    "Q21145902",
    "Q7265406",
    "Q21121716",
    "Q21114547",
    "Q408853",
    "Q420604",
    "Q420766",
    "Q21125451",
    "Q21125466",
    "Q22680132",
    "Q21109261",
    "Q285613",
    "Q14884995",
    "duplicateExactP352MayBeSilentlyCollapsed",
    "absentProteinEnwikiMeansProteinAbsent",
    "completeReciprocalEncodingCreatesMechanisticSupport",
]:
    assert token in identity_text, f"missing acquired Wikimedia biology identity token: {token}"

for token in [
    "geneQidCannotSilentlyBecomeProteinQid",
    "qidDoesNotCreateSequenceIdentity",
    "wikipediaDoesNotCreateMechanisticEvidence",
    "p352IdentityDoesNotCreateFlux",
    "duplicateP352CannotBeSilentlyCollapsed",
    "missingProteinEnwikiDoesNotMeanProteinAbsent",
    "reciprocalEncodingDoesNotCreateMechanism",
    "mtorProteinQidCorrectedByAcquisition",
    "qdprRetainsBothExactP352Items",
    "qdprResolutionIsAmbiguous",
    "allAcquiredRelationsHaveReciprocalEncodingReceipt",
    "completeUniqueIdentityIsFalseBecauseQDPRAmbiguous",
]:
    assert token in regression_text, f"missing Wikimedia biology regression token: {token}"

for token in [
    "BH4ProteinWikimediaIdentityExact",
    "BH4ProteinWikimediaIdentityRegression",
]:
    assert token in focused_text, f"missing focused Wikimedia import: {token}"
    assert token in biology_root_text, f"missing biology-root Wikimedia import: {token}"

for token in [
    "from acquire_uniprot_bio_certificate import KITZEROW_BH4_PANEL",
    "WIKIDATA_SPARQL",
    "wdt:P352",
    '"P702"',
    '"P688"',
    "exact_p352_qids",
    "reciprocal_p688_paid",
    "qid_round_trip_paid",
    "complete_identity_panel_creates_biological_truth",
    "wikipedia_coverage_creates_mechanistic_support",
]:
    assert token in acquirer_text, f"missing Wikimedia acquisition token: {token}"

print("BH4 Wikimedia/Wikidata identity max-cut regression: ok")
