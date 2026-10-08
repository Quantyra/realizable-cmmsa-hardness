"""Owned GCP cache mounts; no compiler or VM lifecycle operations.

Callers hold a thread lease through terminal and verified custody. The lower
cache must have separately verified provenance and no concurrent writer.
"""
from pathlib import Path
import subprocess


class CacheMount:
    def __init__(self, run_workspace, warm_cache, *, command=None):
        self.workspace = Path(run_workspace).resolve(strict=True)
        self.warm = Path(warm_cache).resolve(strict=True)
        if self.workspace == self.warm or self.workspace in self.warm.parents or self.warm in self.workspace.parents:
            raise ValueError('Run workspace and warm cache must be disjoint')
        self.root = self.workspace / 'cache-mount'
        self.view = self.workspace / '.lake'
        self.command = command or self._native
        self.mounted = []
        self.receipts = []

    @staticmethod
    def _native(argv):
        result = subprocess.run(argv, capture_output=True)
        return result.returncode, result.stdout.decode(errors='replace'), result.stderr.decode(errors='replace')

    def _call(self, argv):
        code, out, err = self.command(argv)
        self.receipts.append({'argv': argv, 'native_exit': code, 'stdout': out, 'stderr': err})
        if code:
            raise RuntimeError('Owned cache mount command failed: ' + repr(argv))

    def open(self):
        # Refuse existing or symlinked targets. Never reuse another run's mount.
        if self.root.exists() or self.root.is_symlink() or self.view.exists() or self.view.is_symlink():
            raise FileExistsError('Cache mount targets already exist')
        self.root.mkdir()
        for name in ('lower', 'upper', 'work'):
            (self.root / name).mkdir()
        self.view.mkdir()
        try:
            lower = self.root / 'lower'
            self._call(['sudo', '-n', 'mount', '--bind', str(self.warm), str(lower)])
            self.mounted.append(lower)
            self._call(['sudo', '-n', 'mount', '-o', 'remount,bind,ro', str(lower)])
            self._call(['sudo', '-n', 'mount', '-t', 'overlay', 'overlay', '-o',
                        'lowerdir=' + str(lower) + ',upperdir=' + str(self.root / 'upper') +
                        ',workdir=' + str(self.root / 'work'), str(self.view)])
            self.mounted.append(self.view)
            return self.view
        except Exception:
            self.close()
            raise

    def close(self):
        # Stop at a failed unmount; preserve that mount and all lower layers.
        # Never force unmount, delete cache data, or touch foreign targets.
        while self.mounted:
            target = self.mounted[-1]
            if target not in (self.root / 'lower', self.view):
                raise ValueError('Foreign mount target')
            self._call(['sudo', '-n', 'umount', str(target)])
            self.mounted.pop()

