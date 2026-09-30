#!/usr/bin/env bash
set -Eeuo pipefail
systemctl is-active --quiet quantyra-idle-shutdown.timer
systemctl is-enabled --quiet quantyra-idle-shutdown.timer
sudo systemd-run --unit=cmmsa_analytic_20260930T072056Z-hard-stop --on-active=18min /sbin/shutdown -h now
mkdir -p /tmp/cmmsa_analytic_20260930T072056Z-evidence
trap 'rc=$?; printf "%s\n" "$rc" >/tmp/cmmsa_analytic_20260930T072056Z-evidence/native-exit; tar -czf /tmp/cmmsa_analytic_20260930T072056Z-evidence.tar.gz -C /tmp/cmmsa_analytic_20260930T072056Z-evidence .; exit "$rc"' EXIT
echo '1ad5e46215e8c4bbb524238a2d03ff29e408388f9f059eb16b381bf38128c82a  /tmp/cmmsa_analytic_20260930T072056Z.tar.gz' | sha256sum -c -
WORK="$HOME/cmmsa_analytic_20260930T040837Z"
if [ 'yes' = 'yes' ]; then
  test -d "$WORK/.lake/build"
  python3 - "$WORK" /tmp/cmmsa_analytic_20260930T072056Z.tar.gz lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMomentChecks.lean,lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.lean,lean/PvNP/RealizableHardness/ActualFiniteMomentLpBounds.lean,lean/PvNP/RealizableHardness/ActualSelectedSpectralParameters.lean,lean/PvNP/RealizableHardness/ActualCoordinateZoomFailureTransport.lean <<'PY'
import hashlib,pathlib,sys,tarfile
root=pathlib.Path(sys.argv[1]); targets=sys.argv[3].split(',')
with tarfile.open(sys.argv[2]) as t:
    for m in t:
        if m.isfile() and m.name not in targets:
            assert (root/m.name).read_bytes() == t.extractfile(m).read(), m.name
    for target in targets:
        (root/target).write_bytes(t.extractfile(target).read())
print('REUSED_DEPENDENCY_BYTES_VERIFIED')
PY
else
  mkdir "$WORK"
  tar -xzf /tmp/cmmsa_analytic_20260930T072056Z.tar.gz -C "$WORK"
  cd "$WORK"
  mkdir .lake
  cp -a "$HOME/realizable-cmmsa-hardness/.lake/packages" .lake/packages
  echo 'UNUSED_REUSE_CACHE  /tmp/UNUSED_REUSE_CACHE' | sha256sum -c -
  tar -xzf /tmp/UNUSED_REUSE_CACHE -C .lake/packages
fi
cd "$WORK"
test "$(git -C .lake/packages/cslib rev-parse HEAD)" = d9be64196bf145edd019f1ccfeaee0c11166ba6b
mkdir -p offline-bin
printf '#!/usr/bin/env bash
case "$1" in clone|fetch|pull|ls-remote) echo "Network Git disabled" >&2; exit 93;; esac
exec /usr/bin/git "$@"
' >offline-bin/git
chmod +x offline-bin/git
echo 'CB950518912E5CBC7EA8BDB1D4A349B1DB379E81BC847FBEE71D0A9EB888742F  lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMomentChecks.lean' | sha256sum -c -
echo '4D293F6EB83A322F9C4601D88D9EF680A0AB26AAA2BBED70F88E7A2EBDF1154E  lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.lean' | sha256sum -c -
echo 'BF9C27E32D08A6D4FCE7853D6D45F5BF2BA229635BE0C2AC7229A02979B5532B  lean/PvNP/RealizableHardness/ActualFiniteMomentLpBounds.lean' | sha256sum -c -
echo '78FB8DF0B635E950ED087C3598530B328AD25EC5AC4B2DBF556CBE433A46E582  lean/PvNP/RealizableHardness/ActualSelectedSpectralParameters.lean' | sha256sum -c -
echo '61A72A92A2BA4B3460C6391E6A860A4EEE7C28137772DD8616D80295EC10B441  lean/PvNP/RealizableHardness/ActualCoordinateZoomFailureTransport.lean' | sha256sum -c -
export PATH="$PWD/offline-bin:$HOME/.elan/bin:$PATH"
lean --version >/tmp/cmmsa_analytic_20260930T072056Z-evidence/toolchain.txt
git -C .lake/packages/cslib rev-parse HEAD >/tmp/cmmsa_analytic_20260930T072056Z-evidence/cslib-revision.txt
sha256sum lake-manifest.json lean-toolchain lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMomentChecks.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.lean lean/PvNP/RealizableHardness/ActualFiniteMomentLpBounds.lean lean/PvNP/RealizableHardness/ActualSelectedSpectralParameters.lean lean/PvNP/RealizableHardness/ActualCoordinateZoomFailureTransport.lean >/tmp/cmmsa_analytic_20260930T072056Z-evidence/source-before.sha256
rm -f .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMomentChecks.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualFiniteMomentLpBounds.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedSpectralParameters.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualCoordinateZoomFailureTransport.olean
set +e
timeout --signal=TERM --kill-after=20s 900s lake build PvNP.RealizableHardness.ActualSelectedSpectralParameters >/tmp/cmmsa_analytic_20260930T072056Z-evidence/prebuild-0.stdout 2>/tmp/cmmsa_analytic_20260930T072056Z-evidence/prebuild-0.stderr
rc=$?
set -e
printf "%s\n" "$rc" >/tmp/cmmsa_analytic_20260930T072056Z-evidence/prebuild-0.native-exit
if [ "$rc" -ne 0 ]; then exit "$rc"; fi
set +e
timeout --signal=TERM --kill-after=20s 900s lake build PvNP.RealizableHardness.ActualSelectedComplementAnalyticMoment >/tmp/cmmsa_analytic_20260930T072056Z-evidence/prebuild-1.stdout 2>/tmp/cmmsa_analytic_20260930T072056Z-evidence/prebuild-1.stderr
rc=$?
set -e
printf "%s\n" "$rc" >/tmp/cmmsa_analytic_20260930T072056Z-evidence/prebuild-1.native-exit
if [ "$rc" -ne 0 ]; then exit "$rc"; fi
timeout --signal=TERM --kill-after=20s 900s lake build PvNP.RealizableHardness.ActualSelectedComplementAnalyticMomentChecks >/tmp/cmmsa_analytic_20260930T072056Z-evidence/build.stdout 2>/tmp/cmmsa_analytic_20260930T072056Z-evidence/build.stderr
sha256sum lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMomentChecks.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.lean lean/PvNP/RealizableHardness/ActualFiniteMomentLpBounds.lean lean/PvNP/RealizableHardness/ActualSelectedSpectralParameters.lean lean/PvNP/RealizableHardness/ActualCoordinateZoomFailureTransport.lean .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMomentChecks.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualFiniteMomentLpBounds.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedSpectralParameters.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualCoordinateZoomFailureTransport.olean >/tmp/cmmsa_analytic_20260930T072056Z-evidence/pins.sha256
