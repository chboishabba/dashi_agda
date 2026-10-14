#!/usr/bin/env python3
"""Phase-sensitive Ogg-vs-control diagnostic for the JMD climbing-gym cut.

This is an exploratory finite permutation diagnostic over the SAME first-849
zeta-zero sample used by ``monster_climbing_gym_replay.py``.  It does not claim
that the selected statistic was preregistered and therefore does not report a
confirmatory p-value.

For t in the zero sample define

    C(t) = sum_{p in Ogg15} p^(i t)
           - 3 sum_{q in nonOgg5} q^(i t).

The coefficients are centered because 15 - 3*5 = 0.  The control enumerates
all C(20,5)=15504 choices of which five primes carry coefficient -3 while the
other fifteen carry +1.  Thus no RNG is involved.
"""
from __future__ import annotations

import argparse
import cmath
import itertools
import json
import math
from pathlib import Path
from typing import Sequence

OGG_PRIMES=(2,3,5,7,11,13,17,19,23,29,31,41,47,59,71)
NON_OGG_CONTROLS=(37,43,53,61,67)
ALL_PRIMES=OGG_PRIMES+NON_OGG_CONTROLS
ACTUAL_CONTROL_INDICES=tuple(range(len(OGG_PRIMES),len(ALL_PRIMES)))


def load_zero_cache(path:Path)->list[float]:
    payload=json.loads(path.read_text())
    scale=int(payload["scale"]); encoded=[int(x) for x in payload["first_plus_deltas"]]
    values=[]; current=0
    for index,value in enumerate(encoded):
        current=value if index==0 else current+value
        values.append(current/scale)
    if len(values)!=849 or any(a>=b for a,b in zip(values,values[1:])):
        raise ValueError("expected ordered first-849 zero cache")
    return values


def _phase_moments(zeros:Sequence[float])->tuple[list[complex],list[list[complex]]]:
    """Return E[p^(it)] and Gram matrix E[p^(it) conj(q^(it))]."""
    if not zeros: raise ValueError("zero sample must be nonempty")
    n=len(zeros)
    vectors=[[cmath.exp(1j*t*math.log(p)) for t in zeros] for p in ALL_PRIMES]
    means=[sum(v)/n for v in vectors]
    gram=[]
    for i in range(len(ALL_PRIMES)):
        row=[]
        vi=vectors[i]
        for j in range(len(ALL_PRIMES)):
            vj=vectors[j]
            row.append(sum(vi[k]*vj[k].conjugate() for k in range(n))/n)
        gram.append(row)
    return means,gram


def _partition_statistics(means:Sequence[complex],gram:Sequence[Sequence[complex]],selected:Sequence[int])->tuple[float,float]:
    """Mean |C|^2 and |mean C| for one balanced five-control assignment."""
    m=len(ALL_PRIMES)
    base_energy=sum(gram[i][j].real for i in range(m) for j in range(m))
    column_real_sums=[sum(gram[i][j].real for i in range(m)) for j in range(m)]
    base_mean=sum(means)
    energy=(base_energy
            -8.0*sum(column_real_sums[j] for j in selected)
            +16.0*sum(gram[j][k].real for j in selected for k in selected))
    mean_vector=base_mean-4.0*sum(means[j] for j in selected)
    return float(energy),float(abs(mean_vector))


def exhaustive_balanced_partition_control(zeros:Sequence[float])->dict[str,object]:
    means,gram=_phase_moments(zeros)
    actual_energy,actual_coherence=_partition_statistics(means,gram,ACTUAL_CONTROL_INDICES)
    assignment_count=0; energy_le=0; energy_ge=0; coherence_le=0; coherence_ge=0
    energy_min=math.inf; energy_max=-math.inf; coherence_min=math.inf; coherence_max=-math.inf
    for selected in itertools.combinations(range(len(ALL_PRIMES)),len(NON_OGG_CONTROLS)):
        energy,coherence=_partition_statistics(means,gram,selected)
        assignment_count+=1
        energy_le+=energy<=actual_energy; energy_ge+=energy>=actual_energy
        coherence_le+=coherence<=actual_coherence; coherence_ge+=coherence>=actual_coherence
        energy_min=min(energy_min,energy); energy_max=max(energy_max,energy)
        coherence_min=min(coherence_min,coherence); coherence_max=max(coherence_max,coherence)
    return {
        "contract":"monster_climbing_gym_phase_control",
        "zero_count":len(zeros),
        "ogg_count":len(OGG_PRIMES),
        "control_count":len(NON_OGG_CONTROLS),
        "assignment_count":assignment_count,
        "actual_mean_energy":actual_energy,
        "energy_lower_or_equal_count":energy_le,
        "energy_upper_or_equal_count":energy_ge,
        "energy_lower_tail_fraction":energy_le/assignment_count,
        "energy_upper_tail_fraction":energy_ge/assignment_count,
        "energy_min":energy_min,
        "energy_max":energy_max,
        "actual_mean_vector_magnitude":actual_coherence,
        "coherence_lower_or_equal_count":coherence_le,
        "coherence_upper_or_equal_count":coherence_ge,
        "coherence_lower_tail_fraction":coherence_le/assignment_count,
        "coherence_upper_tail_fraction":coherence_ge/assignment_count,
        "coherence_min":coherence_min,
        "coherence_max":coherence_max,
        "multiple_statistic_warning":True,
        "confirmatory_p_value_claimed":False,
        "monster_specificity_claimed":False,
        "formal_promotion":False,
    }


def main()->None:
    parser=argparse.ArgumentParser(); parser.add_argument("--zeros-json",type=Path,required=True); parser.add_argument("--output",type=Path)
    args=parser.parse_args(); result=exhaustive_balanced_partition_control(load_zero_cache(args.zeros_json))
    text=json.dumps(result,indent=2,sort_keys=True)+"\n"
    if args.output: args.output.write_text(text)
    else: print(text,end="")


if __name__=="__main__":main()
