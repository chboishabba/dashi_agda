"""Sequential exact coefficient parity and resource receipt for the CM backends."""
import argparse
import json
from pathlib import Path
import resource
import subprocess
import sys
import tempfile
from time import perf_counter


def run(backend, output):
    import check_cm163_modular_diagonal as base
    import check_cm163_derivative_slice as jet
    hook = None
    if backend == 'fast':
        import check_cm163_fast as fast
        hook = fast.logder
    start = perf_counter()
    P = base.diagonal(41, hook)
    diagonal_time = perf_counter()-start
    S = jet.slice_poly(41, -640320**3, hook)
    construction_time = perf_counter()-start
    jet.main(lambda p: P, lambda p,K: S)
    coeffs = [[int(c) for c in poly.all_coeffs()] for poly in (P,S)]
    # Signed hexadecimal is lossless and avoids decimal conversion limits.
    raw = json.dumps([[hex(c) for c in v] for v in coeffs], separators=(',',':')).encode('ascii')
    Path(output).write_bytes(raw)
    result = dict(backend=backend, diagonal_seconds=diagonal_time,
                  construction_seconds=construction_time,
                  total_seconds=perf_counter()-start,
                  peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                  coefficient_slots=sum(map(len,coeffs)),
                  coefficient_bits=sum(1+abs(c).bit_length() for v in coeffs for c in v),
                  max_output_coefficient_bits=max(abs(c).bit_length() for v in coeffs for c in v),
                  serialized_bytes=len(raw))
    if hook is not None:
        result.update(packed_operand_bits=fast.peak, packed_multiplications=fast.calls)
    print(json.dumps(result),flush=True)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--backend',choices=('scalar','fast'))
    parser.add_argument('--output')
    args=parser.parse_args()
    if args.backend:
        assert args.output
        run(args.backend,args.output)
        return
    with tempfile.TemporaryDirectory() as tmp:
        files=[Path(tmp)/f'{name}.json' for name in ('scalar','fast')]
        for name,path in zip(('scalar','fast'),files):
            subprocess.run([sys.executable,__file__,'--backend',name,'--output',str(path)],check=True)
        a,b=(p.read_bytes() for p in files)
        assert a==b
        print('PASS full degree-41 diagonal and specialization byte-for-byte coefficient parity',flush=True)

if __name__=='__main__':
    main()
