#!/usr/bin/env python3
"""Dryad SCENAR original-file acquisition with fail-closed provenance.
Original dataset: Marc Fischler (2021), DOI 10.5061/dryad.63xsj3v2s.
No embedded original data and no patient-level GitHub upload.
"""
import argparse
import hashlib
import json
from pathlib import Path
from urllib.request import Request, urlopen

DOI = '10.5061/dryad.63xsj3v2s'
SOURCES = (
    'https://datadryad.org/downloads/file_stream/915627',
    'https://datadryad.org/api/v2/files/915627/download',
)


def acquire(output, timeout=15):
    output = Path(output)
    if output.exists():
        raise FileExistsError('Refuse to overwrite a source file or pre-existing path')
    attempts = []
    for url in SOURCES:
        try:
            request = Request(url, headers={'User-Agent': 'DASHI-original-source-verification/1.0'})
            with urlopen(request, timeout=timeout) as response:
                if 'html' in response.headers.get('Content-Type', '').lower():
                    raise ValueError('HTML response, not the original workbook or archive')
                data = response.read(5_000_001)
                if len(data) > 5_000_000:
                    raise ValueError('Unexpected source payload larger than 5 MB')
                if data[:4] != b'PK\x03\x04':
                    raise ValueError('Not a ZIP/XLSX content signature; archive package requires manual handling')
                digest = hashlib.sha256(data).hexdigest()
                output.parent.mkdir(parents=True, exist_ok=True)
                output.write_bytes(data)
                return {'status': 'BYTES_ACQUIRED_UNVERIFIED_ORIGINAL_IDENTITY', 'doi': DOI,
                        'source_url': url, 'sha256': digest, 'size_bytes': len(data),
                        'original_dataset_hash_published': False,
                        'warning': 'Match filename, internal worksheets, license and deposit version manually.'}
        except (OSError, ValueError) as error:
            attempts.append({'url': url, 'exception': type(error).__name__, 'detail': str(error)[:180]})
    return {'status': 'NO_SOURCE_BYTES', 'doi': DOI, 'attempts': attempts}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--download', action='store_true')
    parser.add_argument('--timeout', type=int, default=15)
    parser.add_argument('--out', type=Path, default=Path.home()/'.cache'/'dashi'/'scenar-original'/'Scenar_-_Dryad_Corrigé.xlsx')
    args = parser.parse_args()
    result = (acquire(args.out, args.timeout) if args.download else
              {'status': 'PLAN_ONLY', 'doi': DOI, 'filename': args.out.name, 'sources': SOURCES})
    print(json.dumps(result, indent=2))
    if args.download and result['status'] == 'NO_SOURCE_BYTES':
        raise SystemExit(2)

if __name__ == '__main__':
    main()
