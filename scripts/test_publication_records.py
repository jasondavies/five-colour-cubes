#!/usr/bin/env python3
"""Publication preserves evidence identities without disclosing local paths."""
import hashlib
import json
import unittest
from pathlib import Path
from publish_verification_record import extract, portable


class PublicationRecords(unittest.TestCase):
    def test_extract_preserves_evidence(self):
        data = {'status':'passed', 'source_sha256':{'Proof.lean':'a'*64},
                'environment':{'audit_python':{'executable':'/home/example/env/python', 'version':'3.12'}},
                'tool_sha256':{'/home/example/tools/lean':'b'*64},
                'pid':1234, 'retry_reason':'private diagnostic',
                'verification_record':'/tmp/run.json', 'verification_record_sha256':'c'*64}
        raw=json.dumps(data).encode()
        result=extract(raw)
        self.assertEqual(result['raw_record_sha256'],hashlib.sha256(raw).hexdigest())
        self.assertEqual(result['source_sha256'],data['source_sha256'])
        self.assertEqual(result['tool_sha256'],{'lean':'b'*64})
        self.assertEqual(result['preceding_raw_record_sha256'],'c'*64)
        self.assertNotIn('pid',result)
        self.assertNotIn('retry_reason',result)
        self.assertNotIn('executable',result['environment']['python'])
        self.assertNotIn('/home/',json.dumps(result))

    def test_unknown_path_and_ambiguous_tools_rejected(self):
        for value in ['/nix/store/tool', '/Users/example/file', 'C:\\Users\\example',
                      {'/opt/bin/lean':'hash'}, 'command /home/example/tool']:
            with self.subTest(value=value), self.assertRaises(ValueError):portable(value)
        data={'status':'passed','tool_sha256':{'/a/lean':'a','/b/lean':'b'}}
        with self.assertRaises(ValueError):extract(json.dumps(data).encode())
        with self.assertRaises(ValueError):extract(b'{"status":"running"}')

    def test_public_records_are_portable_extracts(self):
        root=Path(__file__).resolve().parents[1]
        records=list((root/'verification').glob('*.json'))
        self.assertTrue(records)
        for path in records:
            data=json.loads(path.read_text())
            self.assertEqual(data['format'],'five-colour-verification-extract-v1')
            self.assertEqual(len(data['raw_record_sha256']),64)
            portable(data)


if __name__ == '__main__':
    unittest.main()
