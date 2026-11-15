#!/usr/bin/env python3
"""Strict original-schema verification for GO-CAM and SBML source models.

Requires official gocam-py Pydantic Model and libSBML. Missing dependency,
schema error, or SBML error severity >= ERROR fails closed. The receipt
proves only parsing/structural validity under the reported library versions:
no causal identity, source publication agreement, units, predictive fitness,
calibration or ITIR/PNF promotion is asserted.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib.metadata
import json
from pathlib import Path


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_models(gocam_path: Path, sbml_path: Path) -> dict:
    try:
        from gocam.datamodel import Model
    except ImportError as exc:
        raise RuntimeError("official gocam package required for schema check") from exc
    try:
        import libsbml
    except ImportError as exc:
        raise RuntimeError("libSBML required for full SBML parsing") from exc

    model = Model.model_validate_json(gocam_path.read_text(encoding="utf-8"))
    if not model.id or not model.title or not model.status:
        raise ValueError("validated GO-CAM missing required model metadata")
    sbml = libsbml.readSBMLFromString(sbml_path.read_text(encoding="utf-8"))
    if sbml is None:
        raise ValueError("SBML parser returned null document")
    errors = []
    for i in range(sbml.getNumErrors()):
        err = sbml.getError(i)
        errors.append({
            "severity": int(err.getSeverity()),
            "error_id": int(err.getErrorId()),
            "message": str(err.getMessage()),
        })
    if any(err["severity"] >= libsbml.LIBSBML_SEV_ERROR for err in errors):
        raise ValueError("libSBML reports structural/schema errors: " +
                         json.dumps(errors[:10],sort_keys=True))
    model_sbml = sbml.getModel()
    if model_sbml is None:
        raise ValueError("SBML model missing")
    if not model_sbml.getId():
        raise ValueError("SBML model id missing")
    # No silent use of unset units as a numeric physical calibration.
    missing_parameter_units = [
        model_sbml.getParameter(i).getId()
        for i in range(model_sbml.getNumParameters())
        if not model_sbml.getParameter(i).isSetUnits()
    ]
    missing_kinetic_laws = [
        model_sbml.getReaction(i).getId()
        for i in range(model_sbml.getNumReactions())
        if not model_sbml.getReaction(i).isSetKineticLaw()
    ]
    return {
        "status":"source-schema-validated-not-physically-calibrated",
        "gocam_source_sha256":file_sha256(gocam_path),
        "sbml_source_sha256":file_sha256(sbml_path),
        "gocam_model_id":model.id,
        "sbml_model_id":model_sbml.getId(),
        "gocam_activities":len(model.activities or []),
        "sbml_species":model_sbml.getNumSpecies(),
        "sbml_reactions":model_sbml.getNumReactions(),
        "gocam_package_version":importlib.metadata.version("gocam"),
        "libsbml_version":libsbml.getLibSBMLDottedVersion(),
        "sbml_error_and_warning_receipts":errors,
        "missing_parameter_units":missing_parameter_units,
        "missing_kinetic_laws":missing_kinetic_laws,
        "source_to_source_identity_established":False,
        "original_research_measurement_validated":False,
        "SI_calibration_established":False,
        "pnf_mutation_performed":False,
    }


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gocam",type=Path,required=True)
    parser.add_argument("--sbml",type=Path,required=True)
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    result=verify_models(args.gocam,args.sbml)
    args.output.write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")


if __name__=="__main__":
    main()
