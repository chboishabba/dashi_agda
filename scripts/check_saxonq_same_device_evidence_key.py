#!/usr/bin/env python3
"""Fail-closed cross-device evidence matching for NV quantum hardware.

Documentary exactness only: never promotes a vendor claim into a measured
hardware result. Source ownership retained in Docs/papers/
SaxonQPrimaryHardwareSameObjectCrossPR20261026.md.
Adaptation: Johl Brown with OpenAI assistance, 2026-10-26.
"""
from dataclasses import dataclass

@dataclass(frozen=True)
class DeviceRun:
    source_root: str
    device_model: str
    chip_or_core_id: str
    apparatus_config: str
    experiment_protocol: str
    run_date: str
    control_calibration: str
    raw_observation_id: str

    def complete(self):
        return all(getattr(self, x).strip() not in {"", "unknown", "not_reported", "no_raw_data"}\n                   for x in self.__dataclass_fields__)

def same_device_run(a: DeviceRun, b: DeviceRun):
    """Full exact match *required* for auto-join; incomplete keys fail closed."""
    return a.complete() and b.complete() and a == b

def test():
    base=DeviceRun("synthetic:reference","synthetic_three_qubit_Grover",
                   "synthetic_chip", "synthetic_config", "synthetic_protocol", "2026-10-26",
                   "synthetic_calibration","synthetic_raw_id")
    assert same_device_run(base,base)  # fabricated fixture, NOT hardware evidence
    paper=DeviceRun("arxiv:2609.13022","three_nuclear_spin_Grover",
                    "unknown", "unknown", "three_qubit_Grover", "unknown",
                    "unknown", "unknown")
    assert not same_device_run(paper,paper)
    partial=DeviceRun(*([""]*8))
    assert not same_device_run(partial,partial)
    vendor=DeviceRun("saxonq:2026-08","SXQ128","aggregate_16_cores",
                     "manufacturer_product","product_announcement",
                     "2026-08","not_reported","no_raw_data")
    assert not same_device_run(base,vendor)
    fields=list(base.__dataclass_fields__)
    for field in fields:
        changed={f:getattr(base,f) for f in fields}
        changed[field]+="_different"
        assert not same_device_run(base,DeviceRun(**changed)),field
    print("PASS: fail-closed source/run joins and eight-field mismatch cases")

if __name__=="__main__":
    test()
