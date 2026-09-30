#!/usr/bin/env bash
set -Eeuo pipefail
systemctl is-active --quiet quantyra-idle-shutdown.timer
systemctl is-enabled --quiet quantyra-idle-shutdown.timer
sudo systemd-run --unit=cmmsa_analytic_20260930T055419Z-hard-stop --on-active=18min /sbin/shutdown -h now
mkdir -p /tmp/cmmsa_analytic_20260930T055419Z-evidence
trap 'rc=$?; printf "%s\n" "$rc" >/tmp/cmmsa_analytic_20260930T055419Z-evidence/native-exit; tar -czf /tmp/cmmsa_analytic_20260930T055419Z-evidence.tar.gz -C /tmp/cmmsa_analytic_20260930T055419Z-evidence .; exit "$rc"' EXIT
echo '46a46e75be70dbe282cddd48347e8353da8f0b120ad5e4eb80ff5f87e0b7a7af  /tmp/cmmsa_analytic_20260930T055419Z.tar.gz' | sha256sum -c -
WORK="$HOME/cmmsa_analytic_20260930T040837Z"
if [ 'yes' = 'yes' ]; then
  test -d "$WORK/.lake/build"
  python3 - "$WORK" /tmp/cmmsa_analytic_20260930T055419Z.tar.gz lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.lean,lean/PvNP/RealizableHardness/ActualFiniteMomentLpBounds.lean <<'PY'
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
  tar -xzf /tmp/cmmsa_analytic_20260930T055419Z.tar.gz -C "$WORK"
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
echo '6315055DD40C60CD24AE23E095A71B7AFAF0EE39F89545EF01197625E5D81AE6  lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.lean' | sha256sum -c -
echo 'BF9C27E32D08A6D4FCE7853D6D45F5BF2BA229635BE0C2AC7229A02979B5532B  lean/PvNP/RealizableHardness/ActualFiniteMomentLpBounds.lean' | sha256sum -c -
export PATH="$PWD/offline-bin:$HOME/.elan/bin:$PATH"
lean --version >/tmp/cmmsa_analytic_20260930T055419Z-evidence/toolchain.txt
git -C .lake/packages/cslib rev-parse HEAD >/tmp/cmmsa_analytic_20260930T055419Z-evidence/cslib-revision.txt
sha256sum lake-manifest.json lean-toolchain lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.lean lean/PvNP/RealizableHardness/ActualFiniteMomentLpBounds.lean >/tmp/cmmsa_analytic_20260930T055419Z-evidence/source-before.sha256
rm -f .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualFiniteMomentLpBounds.olean
timeout --signal=TERM --kill-after=20s 900s lake build PvNP.RealizableHardness.ActualSelectedComplementAnalyticMoment >/tmp/cmmsa_analytic_20260930T055419Z-evidence/build.stdout 2>/tmp/cmmsa_analytic_20260930T055419Z-evidence/build.stderr
sha256sum lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.lean lean/PvNP/RealizableHardness/ActualFiniteMomentLpBounds.lean .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualFiniteMomentLpBounds.olean >/tmp/cmmsa_analytic_20260930T055419Z-evidence/pins.sha256
