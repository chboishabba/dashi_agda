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


def rendered_source_rational_producer():
    """Emit source-DEFINITIONAL Q columns and all 72 rational balance clauses.

    This consumes generatedColumns and generatedElementWeights directly:
    NO second hand-entered matrix. All 72 closed Q-equivalences must
    reduce in the pinned Agda kernel, never asserted by a source flag.
    """
    lines = [
        "",
        "-- Exact rational image of the SAME generated Nat source columns.",
        "-- The generated rational proof is still untrusted until Agda checks it.",
        "sourceNatAsRational : Nat → Q.ℚᵘ",
        "sourceNatAsRational n = (+ n / 1)",
        "",
        "generatedRationalReactants : V.Vec (V.Vec Q.ℚᵘ 29) 12",
        "generatedRationalReactants =",
        "  V.map (λ column → V.map sourceNatAsRational",
        "    (Panel.originalReactants column)) generatedColumns",
        "",
        "generatedRationalProducts : V.Vec (V.Vec Q.ℚᵘ 29) 12",
        "generatedRationalProducts =",
        "  V.map (λ column → V.map sourceNatAsRational",
        "    (Panel.originalProducts column)) generatedColumns",
        "",
        "-- Exact source-derived NET 29×12 operator, without a second S.",
        "generatedRationalStoichiometry : Operator.Matrix 29 12",
        "generatedRationalStoichiometry =",
        "  V.tabulate (λ species → V.tabulate (λ column →",
        "    Q._-_",
        "      (V.lookup (V.lookup generatedRationalProducts column) species)",
        "      (V.lookup (V.lookup generatedRationalReactants column) species)))",
        "",
        "-- Original 27×54 source-native incidence and generated Rhea",
        "-- stoichiometry now inhabit ONE typed 369 rational RHS.",
        "generatedOriginalRationalInputs :",
        "  Operator.Matrix 54 29 →",
        "  Operator.Matrix 27 12 →",
        "  Operator.Rational369SemidiscreteInputs",
        "generatedOriginalRationalInputs fluxes rates =",
        "  NativeGeometry.originalNativeRationalInputs",
        "    fluxes generatedRationalStoichiometry rates",
        "",
        "generatedOriginalRationalRHS :",
        "  Operator.Matrix 54 29 →",
        "  Operator.Matrix 27 12 → Operator.Matrix 27 29",
        "generatedOriginalRationalRHS fluxes rates =",
        "  Operator.rational369SemidiscreteRHS",
        "    (generatedOriginalRationalInputs fluxes rates)",
        "",
        "generatedOriginalRationalRHSAt :",
        "  (fluxes : Operator.Matrix 54 29)",
        "  (rates : Operator.Matrix 27 12)",
        "  (site : F.Fin 27) (species : F.Fin 29) →",
        "  V.lookup (V.lookup (generatedOriginalRationalRHS fluxes rates)",
        "    site) species",
        "  ≡ Q._+_",
        "      (Operator.bondContribution",
        "        (generatedOriginalRationalInputs fluxes rates)",
        "        site species)",
        "      (Operator.reactionContribution",
        "        (generatedOriginalRationalInputs fluxes rates)",
        "        site species)",
        "generatedOriginalRationalRHSAt fluxes rates site species =",
        "  Operator.rational369SemidiscreteAt",
        "    (generatedOriginalRationalInputs fluxes rates)",
        "    site species",
        "",
        "generatedRationalSignedCharge : V.Vec Q.ℚᵘ 29",
        "generatedRationalSignedCharge =",
        "  V.zipWith (λ positive negative → Q._-_",
        "    (sourceNatAsRational positive)",
        "    (sourceNatAsRational negative))",
        "    generatedPositiveCharges generatedNegativeCharges",
        "",
        "generatedRationalAxes : V.Vec (V.Vec Q.ℚᵘ 29) 6",
        "generatedRationalAxes =",
        "  V._∷_ (V.map sourceNatAsRational",
        "    (generatedElementWeights Panel.carbonElement))",
        "    (V._∷_ (V.map sourceNatAsRational",
        "      (generatedElementWeights Panel.hydrogenElement))",
        "    (V._∷_ (V.map sourceNatAsRational",
        "      (generatedElementWeights Panel.nitrogenElement))",
        "    (V._∷_ (V.map sourceNatAsRational",
        "      (generatedElementWeights Panel.oxygenElement))",
        "    (V._∷_ (V.map sourceNatAsRational",
        "      (generatedElementWeights Panel.phosphorusElement))",
        "    (V._∷_ generatedRationalSignedCharge V.[])))))",
        "",
        "-- This is the ORIGINAL source's 6×12 columnwise left kernel",
        "-- expressed over rational equivalence, not Nat propositional",
        "-- equality or a separately asserted global zero-defect field.",
        "generatedRationalColumnsBalance :",
        "  (axis : F.Fin 6) (column : F.Fin 12) →",
        "  Q._≃_",
        "    (Lift.sourceWeightedRow",
        "      (V.lookup generatedRationalAxes axis)",
        "      (V.lookup generatedRationalReactants column))",
        "    (Lift.sourceWeightedRow",
        "      (V.lookup generatedRationalAxes axis)",
        "      (V.lookup generatedRationalProducts column))",
    ]
    for axis in range(6):
        for col in range(12):
            lines.append(
                f"generatedRationalColumnsBalance {fin_constructor(axis)} "
                f"{fin_constructor(col)} = QP.≃-reflexive refl")
    lines += [
        "",
        "generatedRationalNetColumnsZero :",
        "  (axis : F.Fin 6) (column : F.Fin 12) →",
        "  Q._≃_",
        "    (V.lookup",
        "      (Kernel.weightedStoichiometryColumns",
        "        (V.lookup generatedRationalAxes axis)",
        "        generatedRationalStoichiometry)",
        "      column)",
        "    Q.0ℚᵘ",
    ]
    for axis in range(6):
        for col in range(12):
            lines.append(
                f"generatedRationalNetColumnsZero {fin_constructor(axis)} "
                f"{fin_constructor(col)} = QP.≃-reflexive refl")
    lines += [
        "",
        "-- Any 27×12 rational original rate field and 54×29 rational",
        "-- native flux field now inherits all six conserved axes.",
        "-- Incidence-to-paired-form and original SG laws remain OPEN.",
        "generatedOriginalSixAxisRationalProducer :",
        "  (rates : V.Vec (V.Vec Q.ℚᵘ 12) 27)",
        "  (fluxes : V.Vec (V.Vec Q.ℚᵘ 29) 54)",
        "  (axis : F.Fin 6) →",
        "  Q._≃_",
        "    (Q._+_",
        "      (Native.pairedNativeBondCollection",
        "        (V.lookup generatedRationalAxes axis) fluxes)",
        "      (Rates.spatialRateWeightedTotal",
        "        (V.lookup generatedRationalAxes axis)",
        "        generatedRationalReactants rates))",
        "    (Rates.spatialRateWeightedTotal",
        "      (V.lookup generatedRationalAxes axis)",
        "      generatedRationalProducts rates)",
        "generatedOriginalSixAxisRationalProducer rates fluxes =",
        "  Composer.originalSixAxisNativeAndReactionBalance",
        "    generatedRationalAxes",
        "    generatedRationalReactants generatedRationalProducts",
        "    rates fluxes generatedRationalColumnsBalance",
        "",
        "generatedOriginalSixAxisBishopProducer :",
        "  (rates : V.Vec (V.Vec Q.ℚᵘ 12) 27)",
        "  (fluxes : V.Vec (V.Vec Q.ℚᵘ 29) 54)",
        "  (axis : F.Fin 6) →",
        "  R._≃_",
        "    (Embed.embed",
        "      (Q._+_",
        "        (Native.pairedNativeBondCollection",
        "          (V.lookup generatedRationalAxes axis) fluxes)",
        "        (Rates.spatialRateWeightedTotal",
        "          (V.lookup generatedRationalAxes axis)",
        "          generatedRationalReactants rates)))",
        "    (Embed.embed",
        "      (Rates.spatialRateWeightedTotal",
        "        (V.lookup generatedRationalAxes axis)",
        "        generatedRationalProducts rates))",
        "generatedOriginalSixAxisBishopProducer rates fluxes =",
        "  Composer.originalSixAxisNativeReactionBalanceBishop",
        "    generatedRationalAxes",
        "    generatedRationalReactants generatedRationalProducts",
        "    rates fluxes generatedRationalColumnsBalance",
        "",
        "generatedOriginalComputedSixAxisBishopConservation :",
        "  (fluxes : Operator.Matrix 54 29)",
        "  (rates : Operator.Matrix 27 12)",
        "  (axis : F.Fin 6) →",
        "  R._≃_",
        "    (Lift.bishopSpatialWeighted",
        "      (V.map Embed.embed",
        "        (V.lookup generatedRationalAxes axis))",
        "      (V.map (V.map Embed.embed)",
        "        (generatedOriginalRationalRHS fluxes rates)))",
        "    (Embed.embed Q.0ℚᵘ)",
        "generatedOriginalComputedSixAxisBishopConservation fluxes rates =",
        "  NativeComputed.originalNativeComputedSixAxisBishopConserves",
        "    fluxes generatedRationalStoichiometry rates",
        "    generatedRationalAxes",
        "    (λ axis →",
        "      Kernel.originalReactionAllSitesZeroFromSourceColumns",
        "        fluxes generatedRationalStoichiometry rates",
        "        (V.lookup generatedRationalAxes axis)",
        "        (generatedRationalNetColumnsZero axis))",
        "",
        "-- The same ORIGINAL chemical columns preserve ALL six",
        "-- weights for arbitrary actual Bishop-real reaction rates.",
        "-- No rational-rate-only restriction on this reaction theorem.",
        "generatedOriginalBishopAnyReactionRatesConserve :",
        "  (rates : V.Vec (V.Vec R.ℝ 12) 27)",
        "  (axis : F.Fin 6) →",
        "  R._≃_",
        "    (BishopRates.bishopSpatialRateWeightedTotal",
        "      (V.map Embed.embed (V.lookup generatedRationalAxes axis))",
        "      (V.map (V.map Embed.embed) generatedRationalReactants)",
        "      rates)",
        "    (BishopRates.bishopSpatialRateWeightedTotal",
        "      (V.map Embed.embed (V.lookup generatedRationalAxes axis))",
        "      (V.map (V.map Embed.embed) generatedRationalProducts)",
        "      rates)",
        "generatedOriginalBishopAnyReactionRatesConserve rates axis =",
        "  BishopRates.original369BishopArbitraryReactionRatesConserve",
        "    (V.lookup generatedRationalAxes axis)",
        "    generatedRationalReactants generatedRationalProducts",
        "    rates (generatedRationalColumnsBalance axis)",
        "",
    ]
    return lines

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
        "import Data.Rational.Unnormalised as Q",
        "import Data.Rational.Unnormalised.Properties as QP",
        "open import Data.Integer.Base using (+_)",
        "open import Data.Rational.Unnormalised using (_/_)",
        "import Real as R",
        "import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Embed",
        "import DASHI.Biology.Molecular.BH4RationalToBishopFiniteContinuityExact as Lift",
        "import DASHI.Biology.Molecular.BH4RationalNativeSourceCompositionExact as Composer",
        "import DASHI.Biology.Molecular.BH4RationalNativeBondCancellationExact as Native",
        "import DASHI.Biology.Molecular.BH4RationalRateWeightedSourceConservationExact as Rates",
        "import DASHI.Biology.Molecular.BH4OriginalRationalSemidiscreteOperatorExact as Operator",
        "import DASHI.Biology.Molecular.BH4OriginalNative369IncidenceExact as NativeGeometry",
        "import DASHI.Biology.Molecular.BH4OriginalRationalReactionColumnKernelExact as Kernel",
        "import DASHI.Biology.Molecular.BH4OriginalNativeComputedBishopConservationExact as NativeComputed",
        "import DASHI.Biology.Molecular.BH4OriginalBishopArbitraryReactionRatesExact as BishopRates",
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
    lines.extend(rendered_source_rational_producer())
    return "\n".join(lines)


def self_test():
    assert fin_constructor(0) == "F.zero"
    assert fin_constructor(2) == "(F.suc (F.suc F.zero))"
    assert nat_vector([0, 2]) == "(V._∷_ 0 (V._∷_ 2 V.[]))"
    source_rational_lines = rendered_source_rational_producer()
    assert sum(line.startswith("generatedRationalColumnsBalance F.")
               or line.startswith("generatedRationalColumnsBalance (F.")
               for line in source_rational_lines) == 72
    assert "generatedOriginalSixAxisBishopProducer rates fluxes =" in source_rational_lines
    assert "generatedRationalReactants =" in source_rational_lines
    assert sum(line.startswith("generatedRationalNetColumnsZero F.")
               or line.startswith("generatedRationalNetColumnsZero (F.")
               for line in source_rational_lines) == 72
    assert "generatedOriginalComputedSixAxisBishopConservation fluxes rates =" in source_rational_lines
    assert "generatedOriginalBishopAnyReactionRatesConserve rates axis =" in source_rational_lines
    assert "generatedOriginalRationalInputs fluxes rates =" in source_rational_lines
    assert "generatedOriginalRationalRHSAt fluxes rates site species =" in source_rational_lines
    assert "generatedRationalStoichiometry =" in source_rational_lines
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
    # The machine-readable result is independently computed from the
    # strict checked original certificate, not inferred from code text.
    original_matrix, original_metadata = check_certificate(
        certificate, full_panel=True)
    original_elements, _, _ = source_weights(
        original_metadata, original_matrix)
    _, simplex_status = rendered_source_simplex_admission(original_elements)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(generated, encoding="utf-8")
    print(json.dumps({
        "status": "source-generated-not-kernel-checked",
        "original_certificate_sha256": observed,
        "generated_agda_sha256": hashlib.sha256(generated.encode("utf-8")).hexdigest(),
        "original_species": 29,
        "original_finite_reactions": 12,
        "original_nonfinite_residuals": 3,
        "source_CHNOP_all_29_weights_positive": simplex_status["all_positive"],
        "source_CHNOP_zero_weight_species_indices": simplex_status["zero_weight_species_indices"],
        "source_literal_positive_simplex_agda_emitted": simplex_status["all_positive"],
        "source_literal_zero_weight_obstruction_agda_emitted": not simplex_status["all_positive"],
        "source_CHNOP_positivity_agda_kernel_checked": False,
        "source_rational_column_balance_proof_clauses_emitted": 72,
        "source_rational_net_column_zero_proof_clauses_emitted": 72,
        "source_computed_783_Bishop_conservation_producer_emitted": True,
        "source_computed_783_Bishop_conservation_agda_kernel_checked": False,
        "source_Bishop_arbitrary_real_reaction_rates_conservation_emitted": True,
        "source_Bishop_arbitrary_real_reaction_rates_agda_kernel_checked": False,
        "source_rational_producer_definitionally_uses_generated_Nat_columns": True,
        "source_rational_producer_agda_kernel_checked": False,
        "same_source_native_incidence_and_rational_stoichiometry_RHS_emitted": True,
        "source_783_coordinate_rational_RHS_kernel_checked": False,
        "original_release_independently_verified": False,
        "physical_kinetic_flux_proved": False,
        "agda_kernel_accepted": False,
        "file": str(args.output),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
