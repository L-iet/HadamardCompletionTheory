# SPDX-License-Identifier: Apache-2.0
"""Exercise runtime placement and receipt loading without compiling mathlib."""
import errno
import hashlib
import json
import os
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

import bootstrap_native_mathlib as bootstrap
import native_runtime


class NativeRuntimeTest(unittest.TestCase):
    def exercise_bootstrap(self, explicit=False, readonly=False):
        with TemporaryDirectory() as temporary:
            root = Path(temporary).resolve() / 'source'
            allowed = root / '.lake' / 'build'
            allowed.mkdir(parents=True)
            output = allowed / ('custom-runtime' if explicit else 'cyclic-native')
            original_mkdir = Path.mkdir

            def guarded_mkdir(path, *args, **kwargs):
                if not path.resolve().is_relative_to(allowed):
                    raise OSError(errno.EROFS, 'Read-only file system', str(path))
                return original_mkdir(path, *args, **kwargs)

            def build(project, destination, args):
                self.assertEqual(project, root)
                self.assertEqual(destination, output)
                (destination / 'logs').mkdir()
                bootstrap.atomic(destination / 'result.json', {'loader': {'file': 'fixture'}})

            argv = ['bootstrap_native_mathlib.py', '--project-root', str(root)]
            if explicit:
                argv += ['--output-dir', str(output)]
            if readonly:
                root.chmod(0o555)
                (root / '.lake').chmod(0o555)
            try:
                with patch.object(bootstrap.sys, 'argv', argv), patch.object(bootstrap, 'build', build):
                    if readonly:
                        # Actual POSIX permissions, in addition to the portable policy model.
                        with self.assertRaises(OSError):
                            (root / '.lake' / 'cyclic-native').mkdir()
                        bootstrap.main()
                    else:
                        with patch.object(Path, 'mkdir', guarded_mkdir):
                            with self.assertRaises(OSError) as error:
                                (root / '.lake' / 'cyclic-native').mkdir()
                            self.assertEqual(error.exception.errno, errno.EROFS)
                            bootstrap.main()
                self.assertTrue((output / 'build.lock').is_file())
                self.assertEqual(json.loads((output / 'result.json').read_text())['loader']['file'], 'fixture')
                self.assertFalse((root / '.lake' / 'cyclic-native').exists())
            finally:
                root.chmod(0o755)
                (root / '.lake').chmod(0o755)

    def test_default_cache_under_writable_build_tree(self):
        self.exercise_bootstrap()

    def test_explicit_lake_build_directory(self):
        self.exercise_bootstrap(explicit=True)

    @unittest.skipUnless(os.name == 'posix' and os.geteuid() != 0,
                         'Requires POSIX permissions and a non-root user')
    def test_actual_readonly_source(self):
        self.exercise_bootstrap(readonly=True)

    def test_reader_uses_bootstrap_receipt_and_checks_loader_digest(self):
        with TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            output = bootstrap.default_output_dir(root)
            output.mkdir(parents=True)
            loader = output / 'fixture-loader'
            loader.write_bytes(b'runtime fixture, not an executable')
            receipt = {'loader': {'file': str(loader),
                                 'sha256': hashlib.sha256(loader.read_bytes()).hexdigest()}}
            bootstrap.atomic(output / 'result.json', receipt)
            with patch.object(native_runtime, 'ROOT', root), patch.object(native_runtime.subprocess, 'run') as run:
                self.assertEqual(native_runtime.native_lean_args(), ['--plugin=' + str(loader)])
                args = run.call_args.args[0]
                self.assertEqual(Path(args[args.index('--output-dir') + 1]), output)
                loader.write_bytes(b'changed')
                with self.assertRaises(AssertionError):
                    native_runtime.native_lean_args()


if __name__ == '__main__':
    unittest.main()
