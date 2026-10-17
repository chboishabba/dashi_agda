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
    "P352",
    "P702",
    "P688",
    "Q5",
    "Q1487359",
    "Q409532",
    "Q420604",
    "Q420766",
    "Q21115057",
    "Q14884995",
    "Q18030367",
    "Q18030177",
    "geneQidMayBeUsedAsProteinQidWithoutP688P702Witness",
    "qidCreatesProteinSequenceIdentity",
    "wikipediaNarrativeCreatesMechanisticEvidence",
    "wikipediaCoverageConfirmsKitzerowWholeGraph",
    "exactP352CreatesMeasuredBH4Flux",
    "unresolvedProteinQidMeansProteinAbsent",
]:
    assert token in identity_text, f"missing Wikimedia biology identity token: {token}"

for token in [
    "geneQidCannotSilentlyBecomeProteinQid",
    "qidDoesNotCreateSequenceIdentity",
    "wikipediaDoesNotCreateMechanisticEvidence",
    "p352IdentityDoesNotCreateFlux",
    "sprProteinQidSeedIsCurrent",
    "thProteinQidSeedIsCurrent",
    "mtorProteinQidSeedIsCurrent",
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
