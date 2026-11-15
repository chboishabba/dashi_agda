#!/usr/bin/env python3
"""F8 three-grid acceptance. The genuine 3D convergence gate FAILS CLOSED."""
import json
import numpy as np
from pathlib import Path
from ksw668_f8_moving_maxcut import calc

def run():
    grids=((256,.012,.003),(512,.007,.0017),(768,.005,.00125))
    rows={kind:[calc(nX=n,dy=dy,dt=dt,source_type=kind)
                 for n,dy,dt in grids]
          for kind in ("plane","compact_3d_TT")}
    def metrics(v):
        coarse,medium,fine=v
        def drift(k):
            return abs(fine[k]-medium[k])/max(abs(fine[k]),1e-30)
        return dict(field_last_pair_relative_drift=drift("retarded_tensor_Hyy"),
            Weyl_last_pair_relative_drift=drift("intrinsic_4D_electric_Weyl"),
            outside_bulk_field=fine["far_field"],
            far_to_signal_ratio=fine["far_to_receiver_ratio"],
            field_signs=[x["retarded_tensor_Hyy"]>0 for x in v],
            Weyl_signs=[x["intrinsic_4D_electric_Weyl"]>0 for x in v])
    m={kind:metrics(r) for kind,r in rows.items()}
    accept=all(m[k]["field_last_pair_relative_drift"]<.01
       and m[k]["Weyl_last_pair_relative_drift"]<.01
       and m[k]["far_to_signal_ratio"]<1e-5 for k in rows)
    obj=dict(original_metric="a(t)=t AdS5 moving Israel brane",
       observer_t=6,geometry="r=r_g(6)-0.008",
       results=rows,metrics=m,full_B4_converged=bool(accept),
       compact_3D_physical_stress_action=False,physical_observation=False,
       exact_numerical_error_certificate=False,
       numerical_scheme="SSP-RK3, 2nd-order one-sided y, Fourier brane spatial",
       note="Plane TT wave is infinite total transverse energy; compact-3D TT has finite continuum energy but ultraviolet and Weyl numerical convergence fail.")
    return obj

if __name__=="__main__":
    obj=run()
    p=Path(__file__).with_name("ksw668_f8_refinement_receipt.json")
    dumps=lambda v:json.dumps(v,indent=2,default=lambda n:n.item() if isinstance(n,np.generic) else str(n))
    p.write_text(dumps(obj)+"\n",encoding="utf8")
    print(dumps({"metrics":obj["metrics"],
                 "full_B4_converged":obj["full_B4_converged"]}))
    if obj["full_B4_converged"]:
        print("PASS numerical provisional threshold; rigorous certification STILL needed")
    else:
        print("OPEN B4: numerical convergence gate not met; no physical promotion")
