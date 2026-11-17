#!/usr/bin/env python3
"""BSD S5/S6 original 28-gate scope audit; source test, NOT kernel verification.
Attribution: Clay/Wiles prize vs refined statement, Rubin selected CM example,
original DASHI BSD boundary module. No universal BSD theorem is supplied.
"""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
manifest=json.loads((ROOT/"Docs/roadmaps/ClaySixFrontierABCExactGates20261114.json").read_text())
z=manifest["clay_six_millennium_endpoints_20261115"]
gates={g["id"]:g for g in z["newly_added_exact_gates"]}
s5,s6=gates["S5"],gates["S6"]
src=(ROOT/"DASHI/Mathematics/Arithmetic/BSDUniversalScopeFirewallExact.agda").read_text()
assert z["expanded_portfolio_decisions_settled"]==14
assert z["expanded_portfolio_active_gates"]==14
assert z["clay_endpoint_theorems_proved_count"]==0
assert s5["settled"] is True and s5["native_kernel_acceptance"] is False
assert s5["original_endpoint_proved"] is False
assert s6["settled"] is False and s6["status"]=="OPEN"
assert s6["native_kernel_acceptance"] is False
assert s6["original_endpoint_proved"] is False
assert s6["official_clay_prize_formal_statement"]=="UNIVERSAL_RANK_EQUALITY"
assert s6["refined_strong_bsd_status"]=="OPEN_SEPARATE_REFINEMENT"
assert not s6["universal_rank_equality_proved"]
assert not s6["universal_sha_finiteness_proved"]
assert not s6["universal_strong_leading_coefficient_proved"]
for term in ("UniversalBSDRankInterface","UniversalBSDRefinedInterface",
             "rankForEveryCurve","strongForEveryCurve",
             "toySelectedTrue","toyUniversalFalse"):
    assert term in src,term
assert "universalBSDProof :" not in src
print("PASS: S5 classical, S5 native unpaid, S6 Clay rank and refined strong both open; original 14/28")
