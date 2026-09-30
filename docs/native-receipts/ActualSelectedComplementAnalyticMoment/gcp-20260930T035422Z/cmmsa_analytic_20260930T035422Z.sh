#!/usr/bin/env bash
set -Eeuo pipefail
systemctl is-active --quiet quantyra-idle-shutdown.timer
systemctl is-enabled --quiet quantyra-idle-shutdown.timer
sudo systemd-run --unit=cmmsa_analytic_20260930T035422Z-hard-stop --on-active=18min /sbin/shutdown -h now
mkdir -p "$HOME/cmmsa_analytic_20260930T035422Z" /tmp/cmmsa_analytic_20260930T035422Z-evidence
trap 'rc=$?; printf "%s\n" "$rc" >/tmp/cmmsa_analytic_20260930T035422Z-evidence/native-exit; tar -czf /tmp/cmmsa_analytic_20260930T035422Z-evidence.tar.gz -C /tmp/cmmsa_analytic_20260930T035422Z-evidence .; exit "$rc"' EXIT
echo 'f18026bd0472d084bf9a88170333dc0d3e7b454317881b099505bc608ac6b2bd  /tmp/cmmsa_analytic_20260930T035422Z.tar.gz' | sha256sum -c -
tar -xzf /tmp/cmmsa_analytic_20260930T035422Z.tar.gz -C "$HOME/cmmsa_analytic_20260930T035422Z"
cd "$HOME/cmmsa_analytic_20260930T035422Z"
mkdir .lake
ln -s "$HOME/realizable-cmmsa-hardness/.lake/packages" .lake/packages
echo '063A44B352F181692072B98A7C71ADB9EE29FC911F1C40732EBEAB4BED1371D2  lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.lean' | sha256sum -c -
export PATH="$HOME/.elan/bin:$PATH"
timeout --signal=TERM --kill-after=20s 900s lake build PvNP.RealizableHardness.ActualSelectedComplementAnalyticMoment >/tmp/cmmsa_analytic_20260930T035422Z-evidence/build.stdout 2>/tmp/cmmsa_analytic_20260930T035422Z-evidence/build.stderr
sha256sum lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.lean .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.olean >/tmp/cmmsa_analytic_20260930T035422Z-evidence/pins.sha256
