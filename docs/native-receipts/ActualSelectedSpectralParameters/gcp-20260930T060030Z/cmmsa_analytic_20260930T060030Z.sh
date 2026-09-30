#!/usr/bin/env bash
set -Eeuo pipefail
systemctl is-active --quiet quantyra-idle-shutdown.timer
systemctl is-enabled --quiet quantyra-idle-shutdown.timer
sudo systemd-run --unit=cmmsa_analytic_20260930T060030Z-hard-stop --on-active=18min /sbin/shutdown -h now
mkdir -p /tmp/cmmsa_analytic_20260930T060030Z-evidence
trap 'rc=$?; printf "%s\n" "$rc" >/tmp/cmmsa_analytic_20260930T060030Z-evidence/native-exit; tar -czf /tmp/cmmsa_analytic_20260930T060030Z-evidence.tar.gz -C /tmp/cmmsa_analytic_20260930T060030Z-evidence .; exit "$rc"' EXIT
echo '02154b894b1426ae4d8559cdfb82a2e0b0b7ecd8ae50a0dcbfa54ff3cfddb2a4  /tmp/cmmsa_analytic_20260930T060030Z.tar.gz' | sha256sum -c -
WORK="$HOME/cmmsa_analytic_20260930T040837Z"
if [ 'yes' = 'yes' ]; then
  test -d "$WORK/.lake/build"
  python3 - "$WORK" /tmp/cmmsa_analytic_20260930T060030Z.tar.gz lean/PvNP/RealizableHardness/ActualSelectedSpectralParameters.lean <<'PY'
import hashlib,pathlib,sys,tarfile
root=pathlib.Path(sys.argv[1]); target=sys.argv[3]
with tarfile.open(sys.argv[2]) as t:
    for m in t:
        if m.isfile() and m.name != target:
            assert (root/m.name).read_bytes() == t.extractfile(m).read(), m.name
    (root/target).write_bytes(t.extractfile(target).read())
print('REUSED_DEPENDENCY_BYTES_VERIFIED')
PY
else
  mkdir "$WORK"
  tar -xzf /tmp/cmmsa_analytic_20260930T060030Z.tar.gz -C "$WORK"
  cd "$WORK"
  mkdir .lake
  cp -a "$HOME/realizable-cmmsa-hardness/.lake/packages" .lake/packages
  echo '57FB6E096BA99E75F27CF16BB6C156704BBEBF41F454BAC1F8B445997A1D1963  /tmp/cmmsa_cslib_d9be641_cache.tar.gz' | sha256sum -c -
  tar -xzf /tmp/cmmsa_cslib_d9be641_cache.tar.gz -C .lake/packages
fi
cd "$WORK"
test "$(git -C .lake/packages/cslib rev-parse HEAD)" = d9be64196bf145edd019f1ccfeaee0c11166ba6b
mkdir -p offline-bin
printf '#!/usr/bin/env bash
case "$1" in clone|fetch|pull|ls-remote) echo "Network Git disabled" >&2; exit 93;; esac
exec /usr/bin/git "$@"
' >offline-bin/git
chmod +x offline-bin/git
echo 'B63A45A65D370EAE35A6E2E741BF35913822D18A5A64B01F02F172C8C4FF4C8C  lean/PvNP/RealizableHardness/ActualSelectedSpectralParameters.lean' | sha256sum -c -
export PATH="$PWD/offline-bin:$HOME/.elan/bin:$PATH"
lean --version >/tmp/cmmsa_analytic_20260930T060030Z-evidence/toolchain.txt
git -C .lake/packages/cslib rev-parse HEAD >/tmp/cmmsa_analytic_20260930T060030Z-evidence/cslib-revision.txt
sha256sum lake-manifest.json lean-toolchain lean/PvNP/RealizableHardness/ActualSelectedSpectralParameters.lean >/tmp/cmmsa_analytic_20260930T060030Z-evidence/source-before.sha256
rm -f .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedSpectralParameters.olean
timeout --signal=TERM --kill-after=20s 900s lake build PvNP.RealizableHardness.ActualSelectedSpectralParameters >/tmp/cmmsa_analytic_20260930T060030Z-evidence/build.stdout 2>/tmp/cmmsa_analytic_20260930T060030Z-evidence/build.stderr
sha256sum lean/PvNP/RealizableHardness/ActualSelectedSpectralParameters.lean .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedSpectralParameters.olean >/tmp/cmmsa_analytic_20260930T060030Z-evidence/pins.sha256
