#!/usr/bin/env bash
set -Eeuo pipefail
systemctl is-active --quiet quantyra-idle-shutdown.timer
systemctl is-enabled --quiet quantyra-idle-shutdown.timer
sudo systemd-run --unit=cmmsa_analytic_20260930T040837Z-hard-stop --on-active=18min /sbin/shutdown -h now
mkdir -p "$HOME/cmmsa_analytic_20260930T040837Z" /tmp/cmmsa_analytic_20260930T040837Z-evidence
trap 'rc=$?; printf "%s\n" "$rc" >/tmp/cmmsa_analytic_20260930T040837Z-evidence/native-exit; tar -czf /tmp/cmmsa_analytic_20260930T040837Z-evidence.tar.gz -C /tmp/cmmsa_analytic_20260930T040837Z-evidence .; exit "$rc"' EXIT
echo '177c7336570325114f97ada06f11e983d8530e63484b955bbd1b71bd1a8afbf7  /tmp/cmmsa_analytic_20260930T040837Z.tar.gz' | sha256sum -c -
tar -xzf /tmp/cmmsa_analytic_20260930T040837Z.tar.gz -C "$HOME/cmmsa_analytic_20260930T040837Z"
cd "$HOME/cmmsa_analytic_20260930T040837Z"
mkdir .lake
cp -a "$HOME/realizable-cmmsa-hardness/.lake/packages" .lake/packages
echo '57FB6E096BA99E75F27CF16BB6C156704BBEBF41F454BAC1F8B445997A1D1963  /tmp/cmmsa_cslib_d9be641_cache.tar.gz' | sha256sum -c -
tar -xzf /tmp/cmmsa_cslib_d9be641_cache.tar.gz -C .lake/packages
test "$(git -C .lake/packages/cslib rev-parse HEAD)" = d9be64196bf145edd019f1ccfeaee0c11166ba6b
mkdir offline-bin
printf '#!/usr/bin/env bash
case "$1" in clone|fetch|pull|ls-remote) echo "Network Git disabled" >&2; exit 93;; esac
exec /usr/bin/git "$@"
' >offline-bin/git
chmod +x offline-bin/git
echo 'B1A675ABA9AA49C638290E2E697BFA7595EFB34D833097DDB88309EE437C8CCD  lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.lean' | sha256sum -c -
export PATH="$PWD/offline-bin:$HOME/.elan/bin:$PATH"
lean --version >/tmp/cmmsa_analytic_20260930T040837Z-evidence/toolchain.txt
timeout --signal=TERM --kill-after=20s 900s lake build PvNP.RealizableHardness.ActualSelectedComplementAnalyticMoment >/tmp/cmmsa_analytic_20260930T040837Z-evidence/build.stdout 2>/tmp/cmmsa_analytic_20260930T040837Z-evidence/build.stderr
sha256sum lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.lean .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.olean >/tmp/cmmsa_analytic_20260930T040837Z-evidence/pins.sha256
