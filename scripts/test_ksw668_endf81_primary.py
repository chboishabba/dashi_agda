#!/usr/bin/env python3
"""No-network ENDF/B-VIII.1 original-format MT103 parser negative controls.

Synthetic ENDF source MUST NOT be confused with actual original NNDC bytes.
"""
import importlib.util,tempfile
from pathlib import Path
from math import isclose
p=Path(__file__).with_name("ksw668_endf81_n14np_original.py")
spec=importlib.util.spec_from_file_location("source",p)
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

def record(values,mat=725,mf=3,mt=103,ns=1):
    return "".join(f"{v:>11}" for v in values)+f"{mat:>4}{mf:>2}{mt:>3}{ns:>5}\n"

with tempfile.TemporaryDirectory() as dirname:
    path=Path(dirname)/"n-007_N_014.endf"
    path.write_text("".join([
        record([7014,13.87,0,0,0,0],ns=1),
        record([.5,.5,0,0,1,4],ns=2),
        record([4,2,0,0,0,0],ns=3),
        record([.01,1,1,2,10,3],ns=4),
        record([100,4,0,0,0,0],ns=5),
    ]))
    grid=m.get_grid(path,False)
    assert grid["np"]==4
    assert m.interpolate(grid,.01)==1
    assert m.interpolate(grid,100)==4
    assert isclose(m.interpolate(grid,5.5),2.5)
    rate=m.source_rate(grid,[(.01,2),(100,2)],1e20,
                       flux_source="SYNTHETIC-only 2 cm^-2 s^-1 eV^-1")
    assert rate["modelled_rate_per_second"]>0
    try:m.interpolate(grid,200)
    except ValueError:pass
    else:raise AssertionError("Out-of-domain cross section wrongly extrapolated")
    try:m.get_grid(path,True)
    except ValueError:pass
    else:raise AssertionError("Unverified synthetic file wrongly source-admitted")
assert m.endf_float(" 1.234567+5")==123456.7
assert m.endf_float("-1.000000-3")==-.001
print("PASS original ENDF TAB1/MT103 interpolation, no padding confusion and source-SHA rejection")
