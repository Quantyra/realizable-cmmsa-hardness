#!/usr/bin/env bash
set -Eeuo pipefail
systemctl is-active --quiet quantyra-idle-shutdown.timer
systemctl is-enabled --quiet quantyra-idle-shutdown.timer
sudo systemd-run --unit=cmmsa_analytic_20260930T064137Z-hard-stop --on-active=18min /sbin/shutdown -h now
mkdir -p /tmp/cmmsa_analytic_20260930T064137Z-evidence
trap 'rc=$?; printf "%s\n" "$rc" >/tmp/cmmsa_analytic_20260930T064137Z-evidence/native-exit; tar -czf /tmp/cmmsa_analytic_20260930T064137Z-evidence.tar.gz -C /tmp/cmmsa_analytic_20260930T064137Z-evidence .; exit "$rc"' EXIT
echo '647142c2433637e15d82402de5fb360e8b33e19d69a74178eaee5e2de2e12b2f  /tmp/cmmsa_analytic_20260930T064137Z.tar.gz' | sha256sum -c -
WORK="$HOME/cmmsa_analytic_20260930T040837Z"
if [ 'yes' = 'yes' ]; then
  test -d "$WORK/.lake/build"
  python3 - "$WORK" /tmp/cmmsa_analytic_20260930T064137Z.tar.gz lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.lean,lean/PvNP/RealizableHardness/ActualFiniteMomentLpBounds.lean,lean/PvNP/RealizableHardness/ActualSelectedSpectralParameters.lean <<'PY'
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
  tar -xzf /tmp/cmmsa_analytic_20260930T064137Z.tar.gz -C "$WORK"
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
echo '51E37B9D96C502FFC45EAD4C15D0106741D8AC809C49B7B121B73CFF0F81DBCC  lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.lean' | sha256sum -c -
echo 'BF9C27E32D08A6D4FCE7853D6D45F5BF2BA229635BE0C2AC7229A02979B5532B  lean/PvNP/RealizableHardness/ActualFiniteMomentLpBounds.lean' | sha256sum -c -
echo '78FB8DF0B635E950ED087C3598530B328AD25EC5AC4B2DBF556CBE433A46E582  lean/PvNP/RealizableHardness/ActualSelectedSpectralParameters.lean' | sha256sum -c -
export PATH="$PWD/offline-bin:$HOME/.elan/bin:$PATH"
lean --version >/tmp/cmmsa_analytic_20260930T064137Z-evidence/toolchain.txt
git -C .lake/packages/cslib rev-parse HEAD >/tmp/cmmsa_analytic_20260930T064137Z-evidence/cslib-revision.txt
sha256sum lake-manifest.json lean-toolchain lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.lean lean/PvNP/RealizableHardness/ActualFiniteMomentLpBounds.lean lean/PvNP/RealizableHardness/ActualSelectedSpectralParameters.lean >/tmp/cmmsa_analytic_20260930T064137Z-evidence/source-before.sha256
rm -f .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualFiniteMomentLpBounds.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedSpectralParameters.olean
set +e
timeout --signal=TERM --kill-after=20s 900s lake build PvNP.RealizableHardness.ActualSelectedSpectralParameters >/tmp/cmmsa_analytic_20260930T064137Z-evidence/prebuild-0.stdout 2>/tmp/cmmsa_analytic_20260930T064137Z-evidence/prebuild-0.stderr
rc=$?
set -e
printf "%s\n" "$rc" >/tmp/cmmsa_analytic_20260930T064137Z-evidence/prebuild-0.native-exit
if [ "$rc" -ne 0 ]; then exit "$rc"; fi
timeout --signal=TERM --kill-after=20s 900s lake build PvNP.RealizableHardness.ActualSelectedComplementAnalyticMoment >/tmp/cmmsa_analytic_20260930T064137Z-evidence/build.stdout 2>/tmp/cmmsa_analytic_20260930T064137Z-evidence/build.stderr
sha256sum lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.lean lean/PvNP/RealizableHardness/ActualFiniteMomentLpBounds.lean lean/PvNP/RealizableHardness/ActualSelectedSpectralParameters.lean .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualFiniteMomentLpBounds.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedSpectralParameters.olean >/tmp/cmmsa_analytic_20260930T064137Z-evidence/pins.sha256
