#!/usr/bin/env python3
"""Rai UCL 2025 observational EEG archive byte admission: NO trial claims.

This adapter reuses the Hardt neural byte-integrity owner but intentionally
omits intervention/heldout/sham records that were not part of this study.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
from hardt_neural_source_bytes_gate import digest, _bounded_file, SHA

DOI = '10.5522/04/28508744.v1'
ARTICLE_ID = 28508744


def audit(manifest_path: Path):
    manifest_path = manifest_path.resolve(strict=True)
    root = manifest_path.parent
    manifest = json.loads(manifest_path.read_text(encoding='utf-8'))
    if (not isinstance(manifest, dict)
        or manifest.get('dataset_doi') != DOI
        or manifest.get('version') != 1
        or manifest.get('article_id') != ARTICLE_ID
        or not isinstance(manifest.get('source_owner'), str)
        or not all(author in manifest['source_owner'] for author in ('Rai', 'Orgs'))):
        raise ValueError('original UCL dataset DOI/version/owner not established by manifest')
    metadata_path = _bounded_file(root, manifest.get('api_snapshot_file'))
    expected = manifest.get('api_snapshot_sha256')
    if not isinstance(expected, str) or not SHA.fullmatch(expected) or digest(metadata_path) != expected:
        raise ValueError('API snapshot local byte hash missing/mismatched')
    meta = json.loads(metadata_path.read_text(encoding='utf-8'))
    if (not isinstance(meta, dict)
        or meta.get('id') != ARTICLE_ID
        or meta.get('version') != 1
        or meta.get('doi') != DOI
        or not isinstance(meta.get('files'), list)
        or not meta['files']):
        raise ValueError('original Figshare API article metadata mismatch')
    files = meta['files']
    ids = [f.get('id') for f in files]
    if any(type(i) is not int or i <= 0 for i in ids) or len(ids) != len(set(ids)):
        raise ValueError('duplicate or invalid original archive file IDs')
    orig = {f['id']: f for f in files}
    selected = manifest.get('files')
    if not isinstance(selected, list) or not selected:
        raise ValueError('at least one actual archive file and checksum required')
    seen = set()
    checked = []
    for item in selected:
        if not isinstance(item, dict) or type(item.get('file_id')) is not int:
            raise ValueError('invalid local file identity')
        fid = item['file_id']
        if fid in seen or fid not in orig:
            raise ValueError('unlisted or repeated file ID')
        seen.add(fid)
        original = orig[fid]
        if (item.get('file_name') != original.get('name')
            or type(original.get('size')) is not int
            or original['size'] <= 0):
            raise ValueError('source file name/size mismatch')
        file_path = _bounded_file(root, item.get('relative_path'))
        if file_path.stat().st_size != original['size']:
            raise ValueError('source file-size mismatch')
        requested_sha = item.get('sha256')
        sha = digest(file_path)
        if not isinstance(requested_sha, str) or not SHA.fullmatch(requested_sha) or sha != requested_sha:
            raise ValueError('file SHA256 mismatch')
        original_md5 = original.get('computed_md5')
        if original_md5:
            with file_path.open('rb') as stream:
                md5 = hashlib.file_digest(stream, 'md5').hexdigest()
            if md5 != original_md5:
                raise ValueError('published Figshare checksum mismatch')
        checked.append({'file_id': fid, 'name': original['name'],
                        'size_bytes': original['size'], 'sha256': sha})
    return {
        'local_api_snapshot_hash_matched': True,
        'local_files_byte_matched': len(checked),
        'original_api_inventory_files': len(files),
        'all_api_listed_files_locally_checked': set(ids) == seen,
        'files': checked,
        'network_origin_of_api_snapshot_authenticated': False,
        'human_subject_ids_joined_to_paper': False,
        'paper_results_reproduced': False,
        'causal_remote_effect_verified': False,
        'evidence_scope': 'syntactic file and snapshot integrity; no research-data semantic validation',
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('manifest', type=Path)
    args = ap.parse_args()
    print(json.dumps(audit(args.manifest), indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
