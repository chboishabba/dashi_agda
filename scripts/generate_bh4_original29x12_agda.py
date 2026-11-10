#!/usr/bin/env python3
"""Source-qualified Rhea 29x12 -> literal Agda finite stoichiometry.

Only an acquired, exactly byte-pinned original 29x12 / three-residual
Rhea certificate is eligible. The generator does NOT invent source rows,
reaction rates, environmental exchanges, ionic mobility or evidence.
For each real column, the emitted Agda proof computes molecular CHNOP
left-kernel and signed charge cross-sum equations by definitional equality.

A successful generated Agda module is still subject to the native Agda 2.9
Golden checker. Python balance checks alone are never a kernel receipt.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

from build_bh4_stoichiometric_matrix import participant_key
from check_bh4_original_panel_spatial_events import (
    ELEMENTS, check_certificate, load_original_receipt_json,
)

MODULE = "DASHI.Biology.Molecular.BH4Original29x12GeneratedSourceExact"
DEFAULT_OUTPUT = Path("DASHI/Biology/Molecular/BH4Original29x12GeneratedSourceExact.agda")


def nat_vector(items):
    expression = "V.[]"
    for item in reversed(items):
        if type(item) is not int or item < 0:
            raise ValueError("Agda vector coefficient must be a nonnegative integer")
        expression = f"(V._∷_ {item} {expression})"
    return expression


def fin_constructor(number):
    if type(number) is not int or number < 0:
        raise ValueError("invalid original Fin index")
    result = "F.zero"
    for _ in range(number):
        result = f"(F.suc {result})"
    return result


def source_column_pairs(certificate, matrix):
    species = matrix["species_index"]
    index = {name: i for i, name in enumerate(species)}
    by_id = {str(row.get("rhea_id")): row
             for row in certificate["reactions"]
             if row.get("formula_charge_ready")}
    if len(by_id) != len(matrix["reaction_index"]):
        raise ValueError("source Rhea reaction ID multiplicity inconsistent")
    pairs = []
    for col, rid in enumerate(matrix["reaction_index"]):
        if rid not in by_id:
            raise ValueError(f"original Rhea column {rid} lacks participants")
        reactants, products = [0] * 29, [0] * 29
        for participant in by_id[rid]["participants"]:
            if type(participant.get("coefficient")) is bool:
                raise ValueError("Boolean original Rhea coefficient rejected")
            try:
                coefficient = int(str(participant["coefficient"]))
            except (TypeError, KeyError, ValueError) as exc:
                raise ValueError(f"noninteger original participant coefficient: {rid}") from exc
            if coefficient <= 0:
                raise ValueError("Rhea participant coefficient must be positive")
            key = participant_key(participant)
            if key not in index:
                raise ValueError(f"Rhea participant missing from matrix: {key}")
            side = participant.get("side")
            if side == "substrate":
                reactants[index[key]] += coefficient
            elif side == "product":
                products[index[key]] += coefficient
            else:
                raise ValueError(f"unknown Rhea participant side: {side}")
        for i in range(29):
            if products[i] - reactants[i] != int(matrix["matrix"][i][col]):
                raise ValueError(f"original Rhea source/matrix disagreement: {rid}")
        pairs.append((reactants, products))
    if len(pairs) != 12:
        raise ValueError("incomplete 12-column original Rhea finite panel")
    return pairs


def source_weights(metadata, matrix):
    species = matrix["species_index"]
    elements = {e: [metadata[key][0][e] for key in species]
                for e in ELEMENTS}
    positive = [max(metadata[key][1], 0) for key in species]
    negative = [max(-metadata[key][1], 0) for key in species]
    for values in [*elements.values(), positive, negative]:
        if len(values) != 29 or any(type(v) is not int or v < 0 for v in values):
            raise ValueError("original elemental/charge weight not a Nat^29")
    return elements, positive, negative


def verify_balanced_columns(pairs, elements, positive, negative):
    def weighted(weights, values):
        return sum(w * v for w, v in zip(weights, values))
    for j, (reactants, products) in enumerate(pairs):
        for element, weights in elements.items():
            if weighted(weights, reactants) != weighted(weights, products):
                raise ValueError(f"original reaction {j} violates {element} balance")
        if (weighted(positive, reactants) + weighted(negative, products)
                != weighted(positive, products) + weighted(negative, reactants)):
            raise ValueError(f"original reaction {j} violates signed charge balance")



def rendered_source_simplex_admission(elements):
    """Produce byte-pinned literal Agda positivity, or an explicit zero blocker."""
    if set(elements) != set(ELEMENTS) or any(len(elements[e]) != 29 for e in ELEMENTS):
        raise ValueError("exact original 29-species CHNOP weight matrix required")
    weights=[]
    for i in range(29):
        counts=[elements[e][i] for e in ELEMENTS]
        if any(type(v) is not int or v<0 for v in counts):
            raise ValueError("nonnegative exact integer original CHNOP values required")
        weights.append(sum(counts))
    zero_indices=[i for i,w in enumerate(weights) if w == 0]
    lines=[
        "generatedAggregateCHNOP : V.Vec Nat 29",
        "generatedAggregateCHNOP =",
        "  Simplex.totalCHNOPSourceWeights generatedSourceCertifiedOriginal29x12",
        "",
    ]
    if zero_indices:
        i=zero_indices[0]
        lines += [
            "-- Real source has a zero atom-weight species; reject positive simplex.",
            "generatedZeroCHNOPSpecies : F.Fin 29",
            f"generatedZeroCHNOPSpecies = {fin_constructor(i)}",
            "generatedZeroCHNOPWeight :",
            "  V.lookup generatedAggregateCHNOP generatedZeroCHNOPSpecies ≡ 0",
            "generatedZeroCHNOPWeight = refl",
            "generatedPositiveSimplexObstructed :",
            "  Simplex.SourcePositiveAggregateCHNOP",
            "    generatedSourceCertifiedOriginal29x12 → ⊥",
            "generatedPositiveSimplexObstructed =",
            "  Simplex.zeroCHNOPWeightBlocksPositiveSource",
            "    generatedSourceCertifiedOriginal29x12",
            "    generatedZeroCHNOPSpecies generatedZeroCHNOPWeight",
            "",
        ]
    else:
        lines += [
            "generatedCHNOPPositiveAt :",
            "  (species : F.Fin 29) →",
            "  Σ Nat (λ predecessor →",
            "    V.lookup generatedAggregateCHNOP species ≡ suc predecessor)",
        ]
        for i,w in enumerate(weights):
            lines.append(
                f"generatedCHNOPPositiveAt {fin_constructor(i)} = ({w-1} , refl)")
        lines += [
            "generatedPositiveCHNOP :",
            "  Simplex.SourcePositiveAggregateCHNOP",
            "    generatedSourceCertifiedOriginal29x12",
            "generatedPositiveCHNOP = record",
            "  { sourceWeightPositive = generatedCHNOPPositiveAt }",
            "generatedPositiveSimplexAdmission :",
            "  Simplex.Original369PositiveWeightedSimplexAdmission",
            "generatedPositiveSimplexAdmission =",
            "  Simplex.original369-positive-weighted-simplex-admission",
            "    generatedSourceCertifiedOriginal29x12",
            "    generatedPositiveCHNOP",
            "",
        ]
    return lines, {"all_positive": not zero_indices,
                   "zero_weight_species_indices": zero_indices,
                   "aggregate_weights": weights}

def render_agda(certificate_bytes: bytes, certificate: dict) -> str:
    matrix, metadata = check_certificate(certificate, full_panel=True)
    pairs = source_column_pairs(certificate, matrix)
    elements, positive, negative = source_weights(metadata, matrix)
    verify_balanced_columns(pairs, elements, positive, negative)
    sha = hashlib.sha256(certificate_bytes).hexdigest()
    lines = [
        f"module {MODULE} where",
        "",
        "-- GENERATED ONLY from the checked original acquired Rhea/ChEBI bytes.",
        "-- No physically measured rates, PNP fluxes, or nonfinite MTOR columns.",
        "-- Original 29 species, 12 finite columns, 3 residuals verified upstream.",
        "-- Native Agda kernel must check each explicit balance clause.",
        "open import DASHI.Core.Prelude",
        "import Data.Vec.Base as V",
        "import Data.Fin.Base as F",
        "import DASHI.Biology.Molecular.BH4PanelStoichiometricMatrixExact as Panel",
        "import DASHI.Biology.Molecular.BH4OriginalCHNOPFiveAxisSimplexBridgeExact as Simplex",
        "",
        "generatedOriginalRheaCertificateSha256 : String",
        f'generatedOriginalRheaCertificateSha256 = "{sha}"',
        "",
        "generatedOriginalReleaseIndependentlyVerified : Bool",
        "generatedOriginalReleaseIndependentlyVerified = false",
        "",
        "generatedColumns : V.Vec (Panel.OriginalFiniteReaction 29) 12",
        "generatedColumns =",
    ]
    col_expr = "V.[]"
    for reactants, products in reversed(pairs):
        pair_expr = ("(Panel.original-finite-reaction "
                     + nat_vector(reactants) + " " + nat_vector(products) + ")")
        col_expr = "(V._∷_ " + pair_expr + " " + col_expr + ")"
    lines.append("  " + col_expr)
    lines += [
        "",
        "generatedElementWeights : Panel.OriginalCHNOPElement → V.Vec Nat 29",
    ]
    element_names = {
        "C": "carbonElement", "H": "hydrogenElement",
        "N": "nitrogenElement", "O": "oxygenElement",
        "P": "phosphorusElement",
    }
    for element in ELEMENTS:
        lines.append(
            f"generatedElementWeights Panel.{element_names[element]} = "
            + nat_vector(elements[element]))
    lines += [
        "",
        "generatedPositiveCharges : V.Vec Nat 29",
        "generatedPositiveCharges = " + nat_vector(positive),
        "generatedNegativeCharges : V.Vec Nat 29",
        "generatedNegativeCharges = " + nat_vector(negative),
        "",
        "generatedColumnBalance :",
        "  (element : Panel.OriginalCHNOPElement) (column : F.Fin 12) →",
        "  Panel.panelWeighted (generatedElementWeights element)",
        "    (Panel.originalReactants (V.lookup generatedColumns column))",
        "    ≡ Panel.panelWeighted (generatedElementWeights element)",
        "      (Panel.originalProducts (V.lookup generatedColumns column))",
    ]
    for element in ELEMENTS:
        for i in range(12):
            lines.append(
                f"generatedColumnBalance Panel.{element_names[element]} "
                + fin_constructor(i) + " = refl")
    lines += [
        "",
        "generatedSignedChargeBalance : (column : F.Fin 12) →",
        "  (Panel.panelWeighted generatedPositiveCharges",
        "    (Panel.originalReactants (V.lookup generatedColumns column))",
        "    + Panel.panelWeighted generatedNegativeCharges",
        "      (Panel.originalProducts (V.lookup generatedColumns column)))",
        "    ≡",
        "  (Panel.panelWeighted generatedPositiveCharges",
        "    (Panel.originalProducts (V.lookup generatedColumns column))",
        "    + Panel.panelWeighted generatedNegativeCharges",
        "      (Panel.originalReactants (V.lookup generatedColumns column)))",
    ]
    for i in range(12):
        lines.append(
            "generatedSignedChargeBalance " + fin_constructor(i) + " = refl")
    lines += [
        "",
        "generatedSourceCertifiedOriginal29x12 : Panel.SourceCertifiedOriginal29x12",
        "generatedSourceCertifiedOriginal29x12 = record",
        "  { sourceFiniteColumns = generatedColumns",
        "  ; sourceElementWeights = generatedElementWeights",
        "  ; sourceColumnLeftKernel = generatedColumnBalance",
        "  ; sourcePositiveChargeWeights = generatedPositiveCharges",
        "  ; sourceNegativeChargeWeights = generatedNegativeCharges",
        "  ; sourceColumnSignedCharge = generatedSignedChargeBalance",
        "  }",
        "",
    ]
    simplex_lines, _ = rendered_source_simplex_admission(elements)
    lines.extend(simplex_lines)
    return "\n".join(lines)


def self_test():
    assert fin_constructor(0) == "F.zero"
    assert fin_constructor(2) == "(F.suc (F.suc F.zero))"
    assert nat_vector([0, 2]) == "(V._∷_ 0 (V._∷_ 2 V.[]))"
    sample = {e: [1]*29 for e in ELEMENTS}
    lines, status = rendered_source_simplex_admission(sample)
    assert status["all_positive"] and status["aggregate_weights"] == [5]*29
    assert sum("generatedCHNOPPositiveAt (F." in line for line in lines) == 28
    sample["C"][0] = 0
    for e in ELEMENTS[1:]:
        sample[e][0] = 0
    lines, status = rendered_source_simplex_admission(sample)
    assert not status["all_positive"]
    assert status["zero_weight_species_indices"] == [0]
    assert "generatedPositiveSimplexObstructed :" in lines
    assert "generatedPositiveSimplexAdmission :" not in lines
    verify_balanced_columns(
        [([1, 0], [0, 1])],
        {"C": [2, 2], "H": [1, 1], "N": [0, 0],
         "O": [0, 0], "P": [0, 0]}, [1, 1], [0, 0])
    try:
        verify_balanced_columns(
            [([1, 0], [0, 1])],
            {"C": [2, 3]}, [1, 1], [0, 0])
    except ValueError:
        pass
    else:
        raise AssertionError("unbalanced source column admitted")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path)
    parser.add_argument("--expected-certificate-sha256",
                        help="original byte-pinned Rhea certificate digest")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        print("PASS: original Rhea -> Agda generator structural negative controls")
        return
    if args.certificate is None or args.expected_certificate_sha256 is None:
        parser.error("exact original --certificate and --expected-certificate-sha256 are required")
    raw = args.certificate.read_bytes()
    observed = hashlib.sha256(raw).hexdigest()
    expected = args.expected_certificate_sha256.lower()
    if len(expected) != 64 or any(c not in "0123456789abcdef" for c in expected):
        parser.error("expected SHA256 must be 64 lowercase-compatible hex digits")
    if observed != expected:
        raise ValueError(
            "original Rhea certificate byte hash differs from pinned source; refuse Agda generation")
    certificate = load_original_receipt_json(raw)
    generated = render_agda(raw, certificate)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(generated, encoding="utf-8")
    print(json.dumps({
        "status": "source-generated-not-kernel-checked",
        "original_certificate_sha256": observed,
        "generated_agda_sha256": hashlib.sha256(generated.encode("utf-8")).hexdigest(),
        "original_species": 29,
        "original_finite_reactions": 12,
        "original_nonfinite_residuals": 3,
        "original_release_independently_verified": False,
        "physical_kinetic_flux_proved": False,
        "agda_kernel_accepted": False,
        "file": str(args.output),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
