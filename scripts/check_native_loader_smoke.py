# SPDX-License-Identifier: Apache-2.0
"""Compile and load a tiny plugin with the production flags; no mathlib rebuild."""
from pathlib import Path
import os
import subprocess

from bootstrap_native_mathlib import native_compile_flags, run, smoke_test_loader


def main():
    root = Path(__file__).resolve().parents[1]
    out = root / '.lake/build/native-loader-smoke'
    (out / 'logs').mkdir(parents=True, exist_ok=True)
    windows = os.name == 'nt'
    prefix = Path(subprocess.check_output(['lean', '--print-prefix'], cwd=root, text=True).strip())
    compiler = prefix / 'bin' / ('leanc.exe' if windows else 'leanc')
    source = out / 'CyclicNativeLoader.lean'
    source.write_text('module\nimport Lean.LoadDynlib\ninitialize pure ()\n', encoding='utf-8', newline='\n')
    generated = out / 'CyclicNativeLoader.c'
    obj = out / 'CyclicNativeLoader.o'
    library = out / ('CyclicNativeLoader.dll' if windows else 'libCyclicNativeLoader.so')
    commands = [
        ['lean', '-M4096', '--root=' + str(out), '-c', str(generated), str(source)],
        [str(compiler), *native_compile_flags(windows), str(generated), '-o', str(obj)],
        [str(compiler), '-shared', str(obj), '-o', str(library)],
    ]
    for index, command in enumerate(commands):
        code = run(command, root, out / 'logs' / f'compile-{index}.log')
        if code:
            raise RuntimeError(f'Loader smoke compilation failed ({code}); see {out / "logs"}')
    smoke_test_loader(root, out, library)
    print('Tiny native plugin compiled and loaded with production export flags.')


if __name__ == '__main__':
    main()
