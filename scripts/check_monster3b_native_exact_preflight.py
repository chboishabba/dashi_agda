#!/usr/bin/env python3
"""Actual native mmgroup ABI/metric/denominator smoke test, no synthetic fallback.

Run before the expensive source-bound vacuum producer. Checks actual native
rational unit actions against Seysen's independent fixed-point CRT carrier
and standard MMV reductions. Does not authenticate the marked 3B cover.
"""
import json
from importlib.metadata import version
import numpy as np
from monster3b_conway_exact_crt import ConwayNative, reduce_vector, DIM, require
from mmgroup import MM, MMV
from mmgroup.mm_crt_space import MMV_CRT, compress_data

def run():
    N=ConwayNative()
    # Cover the external diagonal, off-diagonal A and other coordinate families.
    probes=(0,24,300,576,852,49428,196883)
    words=[MM(tag,1) for tag in ("d","p","x","y","t","l")]
    words += [MM("t",1)*MM("p",1)*MM("l",1),
              MM("d",1)*MM("x",1)*MM("y",1)]
    space=MMV_CRT(17)
    checks=0
    for j in probes:
        u=N.unit(j)
        for g in words:
            v=N.act(u,g)
            reference=space([("E",j)])*g
            # The upstream vector_get_item currently returns scaled floats,
            # despite the older integer-return docstring. Use its exact
            # expanded CRT integer buffer and original external chart instead.
            reference.expand()
            expected=np.asarray(compress_data(reference.data_int),dtype=object)
            require(expected.shape==(DIM,),"native CRT reference external coordinates")
            require(not np.any(v.b) and np.array_equal(v.a*(1<<17),expected*v.d),
                    "actual fixed-point CRT reference discrepancy")
            for p,root in ((31,5),(127,19)):
                r=MMV(p)("E",j)*g
                require(np.array_equal(reduce_vector(v,p,root),np.asarray(r["E"],dtype=np.int64)%p),
                        "actual native reduction discrepancy")
            require(N.act(v,g**-1)==u,"actual native inverse discrepancy")
            checks+=4
    print(json.dumps({"status":"ACTUAL_NATIVE_CRT_PREFLIGHT","mmgroup_version":version("mmgroup"),
                      "probes":len(probes),"words":len(words),"checks":checks,
                      "marked_3B_cover_authenticated":False,"actual_Hom_extracted":False}))
if __name__=="__main__":run()
