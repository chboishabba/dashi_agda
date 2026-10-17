#!/usr/bin/env python3
"""Full IIT-4 numerical oracle adapter using PyPhi when installed.

DASHI's local finite reference owns the small system-phi fixtures. This adapter
is the source-faithful execution route for mechanism/purview distinctions,
relations, and big-Phi. It intentionally imports PyPhi lazily so the rest of
the repository remains usable where PyPhi is unavailable.

The default command reproduces the Albantakis et al. (2023) Fig. 1A worked
example under the explicit IIT_4_0_2023 preset. ``--input`` accepts a JSON
binary state-by-node TPM or factored multi-valued marginals plus a state.

Provenance note: ``CALIBRATED_PYPHI_REFERENCE_COMMIT`` records the public PyPhi
source revision against which this adapter was reviewed. It is not claimed to
be the commit of the PyPhi package installed at execution time; each receipt
also records the installed PyPhi version separately.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

CALIBRATED_PYPHI_REFERENCE_COMMIT = "4ebee8686d703e68e602f74236b8a600b55247f8"


def _load_pyphi():
    try:
        import numpy as np
        import pyphi
        from pyphi.conf import presets
    except ImportError as exc:
        raise RuntimeError(
            "PyPhi oracle unavailable. Install a compatible current PyPhi and rerun; "
            "do not substitute DASHI's stored calibration constants for a fresh CES run."
        ) from exc
    return np, pyphi, presets


def _runtime_provenance(pyphi: Any) -> dict:
    return {
        "pyphi_installed_version": getattr(pyphi, "__version__", "unknown"),
        "pyphi_calibration_reference_commit": CALIBRATED_PYPHI_REFERENCE_COMMIT,
        "runtime_commit_equals_calibration_commit": "not_asserted_without_runtime_commit_metadata",
    }


def _analysis_receipt(analysis: Any) -> dict:
    ces = analysis.ces
    relations = ces.relations.materialize()
    return {
        "system_phi_s": float(analysis.phi),
        "distinctions": [
            {
                "mechanism": list(distinction.mechanism),
                "phi_d": float(distinction.phi),
                "cause_purview": list(distinction.cause_purview),
                "effect_purview": list(distinction.effect_purview),
            }
            for distinction in ces.distinctions
        ],
        "relation_count": len(relations),
        "relations": [
            {
                "mechanisms": [list(mechanism) for mechanism in relation.mechanisms],
                "phi_r": float(relation.phi),
                "num_faces": relation.num_faces,
            }
            for relation in relations
        ],
        "sum_phi_distinctions": float(ces.sum_phi_distinctions),
        "sum_phi_relations": float(ces.sum_phi_relations),
        "big_phi": float(ces.big_phi),
    }


def worked_example_receipt() -> dict:
    _np, pyphi, presets = _load_pyphi()
    pyphi.config.progress_bars = False
    pyphi.config.iit = presets.iit4_2023["iit"]
    substrate = pyphi.examples.iit4_2023_fig1a_substrate()
    analysis = pyphi.analyze(substrate, (0, 1, 1), subset=(0, 1))
    return {
        "contract": "iit4_pyphi_oracle",
        "formalism": "IIT_4_0_2023",
        "source_fixture": "Albantakis et al. 2023 Fig.1A, subset aB, state aBC",
        **_runtime_provenance(pyphi),
        **_analysis_receipt(analysis),
    }


def json_fixture_receipt(path: Path) -> dict:
    np, pyphi, presets = _load_pyphi()
    payload = json.loads(path.read_text())
    formalism = payload.get("formalism", "IIT_4_0_2023")
    if formalism == "IIT_4_0_2023":
        pyphi.config.iit = presets.iit4_2023["iit"]
    elif formalism == "IIT_4_0_2026":
        pyphi.config.iit = presets.iit4_2026["iit"]
    else:
        raise ValueError(f"unsupported formalism {formalism!r}")
    pyphi.config.progress_bars = False

    state = tuple(payload["state"])
    labels = tuple(payload.get("node_labels", [f"u{i}" for i in range(len(state))]))
    if "marginals" in payload:
        if "state_space" not in payload:
            raise ValueError("multi-valued marginals require explicit state_space")
        substrate = pyphi.Substrate(
            marginals=[np.asarray(factor, dtype=float) for factor in payload["marginals"]],
            state_space=tuple(tuple(values) for values in payload["state_space"]),
            node_labels=labels,
        )
    else:
        substrate = pyphi.Substrate(np.asarray(payload["tpm"], dtype=float), node_labels=labels)

    subset = tuple(payload.get("subset", range(len(state))))
    analysis = pyphi.analyze(substrate, state, subset=subset)
    return {
        "contract": "iit4_pyphi_oracle",
        "formalism": formalism,
        "source_fixture": str(path),
        **_runtime_provenance(pyphi),
        **_analysis_receipt(analysis),
    }


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Run a full IIT-4 PyPhi CES oracle and emit a JSON receipt."
    )
    parser.add_argument("--input", type=Path, help="JSON TPM/marginal fixture; default is the IIT-4 worked example")
    parser.add_argument("--output", type=Path, help="optional receipt output path")
    args = parser.parse_args()
    receipt = json_fixture_receipt(args.input) if args.input else worked_example_receipt()
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
