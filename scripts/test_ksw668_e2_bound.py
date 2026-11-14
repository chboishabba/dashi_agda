#!/usr/bin/env python3
"""E2 no-network Poisson source-admission / uncertainty negative controls."""
import math
import ksw668_e2_zero_count_exclusion as E2

assert abs(E2.one_sided_upper_mean(0)+math.log(.05))<1e-10
assert abs(E2.one_sided_upper_mean(1)-4.743864518390578)<1e-9

try:E2.source_bound({"observed_count":0})
except ValueError:pass
else:raise AssertionError("Unmeasured nuclear observation accepted")

record={key:"source metadata" for key in (
    "original_authors_and_provenance","individual_specimen_id",
    "experimental_protocol","matched_control_id","registered_isotope_assay")}
record.update(original_file_sha256="a"*64,observed_count=0,
              efficiency_lower=.5,background_count_lower=0.,
              exposure_seconds=3600.,conditioned_nuclear_detection=True)
out=E2.source_bound(record)
assert abs(out["produced_additional_events_upper"]-5.991464547)<1e-7
assert out["same_body_physical_exclusion_established"] is False

record["conditioned_nuclear_detection"]=False
try:E2.source_bound(record)
except ValueError:pass
else:raise AssertionError("Uncalibrated isotope assay accepted")
print("PASS source-gated E2 confidence bound and no-dataset refusal")
