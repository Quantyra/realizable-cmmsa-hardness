#!/usr/bin/env bash
set -Eeuo pipefail
systemctl is-active --quiet quantyra-idle-shutdown.timer
systemctl is-enabled --quiet quantyra-idle-shutdown.timer
sudo systemd-run --unit=cmmsa_analytic_20260930T192759Z-hard-stop --on-active=18min /sbin/shutdown -h now
mkdir -p /tmp/cmmsa_analytic_20260930T192759Z-evidence
trap 'rc=$?; printf "%s\n" "$rc" >/tmp/cmmsa_analytic_20260930T192759Z-evidence/native-exit; tar -czf /tmp/cmmsa_analytic_20260930T192759Z-evidence.tar.gz -C /tmp/cmmsa_analytic_20260930T192759Z-evidence .; exit "$rc"' EXIT
echo '37173d9037fdbdc9161660be213fe036e86beb74bb1f93e3e637350454a252df  /tmp/cmmsa_analytic_20260930T192759Z.tar.gz' | sha256sum -c -
WORK="$HOME/cmmsa_analytic_20260930T040837Z"
if [ 'yes' = 'yes' ]; then
  test -d "$WORK/.lake/build"
  python3 - "$WORK" /tmp/cmmsa_analytic_20260930T192759Z.tar.gz lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMarginChecks.lean,lean/PvNP/RealizableHardness/ActualOriginalFailureRowGenericFixedMomentCallerChecks.lean,lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparisonChecks.lean,lean/PvNP/RealizableHardness/ActualSelectedSpectralTailGeometryChecks.lean,lean/PvNP/RealizableHardness/ActualSelectedHighEnergyTailChecks.lean,lean/PvNP/RealizableHardness/ActualOriginalFailureFixedMomentCallerChecks.lean,lean/PvNP/RealizableHardness/ActualOriginalFailureAnalyticCallerChecks.lean,lean/PvNP/RealizableHardness/ActualOriginalFailureAnalyticCaller.lean,lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticNumerics.lean,lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticNumericsChecks.lean,lean/PvNP/RealizableHardness/ActualFiniteMomentLpBounds.lean,lean/PvNP/RealizableHardness/ActualSelectedSpectralParameters.lean,lean/PvNP/RealizableHardness/ActualCoordinateZoomFailureTransport.lean,lean/PvNP/RealizableHardness/ActualCoordinateZoomFailureTransportChecks.lean,lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.lean,lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMomentChecks.lean,lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMargin.lean,lean/PvNP/RealizableHardness/ActualOriginalFailureFixedMomentCaller.lean,lean/PvNP/RealizableHardness/ActualSelectedHighEnergyTail.lean,lean/PvNP/RealizableHardness/ActualSelectedSpectralTailGeometry.lean,lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparison.lean,lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignal.lean,lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignalChecks.lean,lean/PvNP/RealizableHardness/ActualOriginalFailureRowGenericFixedMomentCaller.lean <<'PY'
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
  tar -xzf /tmp/cmmsa_analytic_20260930T192759Z.tar.gz -C "$WORK"
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
echo 'CF8E63970FD89732C1395A38E6D93C42E965E29B028489FABA3C9FA430A12101  lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMarginChecks.lean' | sha256sum -c -
echo 'B8EE0F47746576586AA9B51767103636E3E8EA66D36F01924D97871A6F969B0E  lean/PvNP/RealizableHardness/ActualOriginalFailureRowGenericFixedMomentCallerChecks.lean' | sha256sum -c -
echo 'E53579C62F6D57D73734AB66962AC0DA2C85DF17AC972D8E4794702CF4070A9F  lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparisonChecks.lean' | sha256sum -c -
echo '67680C360F9C028A4D938A130964CFD93686E205F10433DB9CD882E66182F0B2  lean/PvNP/RealizableHardness/ActualSelectedSpectralTailGeometryChecks.lean' | sha256sum -c -
echo 'B7BABC42B952076DAE4A7439D531D0E6F0F01D493B235ECB3AADA52AA6E46EC6  lean/PvNP/RealizableHardness/ActualSelectedHighEnergyTailChecks.lean' | sha256sum -c -
echo '4E53C23BB30CF46521BCB2A03579121CF8F1A8BE45E35BABC68022332880963F  lean/PvNP/RealizableHardness/ActualOriginalFailureFixedMomentCallerChecks.lean' | sha256sum -c -
echo '05B05D02EFFA7EFFFE8CBF21F31F3618FA54279AC7A6447064E8E725F30BF580  lean/PvNP/RealizableHardness/ActualOriginalFailureAnalyticCallerChecks.lean' | sha256sum -c -
echo '77D92F05D632743A5B8B445CBCAAAD3DE5241C4E7E9E9841A50A506A6EDB4153  lean/PvNP/RealizableHardness/ActualOriginalFailureAnalyticCaller.lean' | sha256sum -c -
echo '92A4E4C37936C3A012263EC5834A2EB7D39EFC5A921B651951D1D276C991BE8A  lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticNumerics.lean' | sha256sum -c -
echo 'DE235CC60483EE0BF269A581EF22123E40CCFD3EADAA0055DF1799684E27962E  lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticNumericsChecks.lean' | sha256sum -c -
echo 'BF9C27E32D08A6D4FCE7853D6D45F5BF2BA229635BE0C2AC7229A02979B5532B  lean/PvNP/RealizableHardness/ActualFiniteMomentLpBounds.lean' | sha256sum -c -
echo '78FB8DF0B635E950ED087C3598530B328AD25EC5AC4B2DBF556CBE433A46E582  lean/PvNP/RealizableHardness/ActualSelectedSpectralParameters.lean' | sha256sum -c -
echo 'D157ED4CDEF826EDF470D93C4715934613291AAA14F6484459C3835F9EAEA02E  lean/PvNP/RealizableHardness/ActualCoordinateZoomFailureTransport.lean' | sha256sum -c -
echo 'BD7A3607C3027755D76A55EB5FF5AEFED6A361D518F7B1A858C077476EECD96D  lean/PvNP/RealizableHardness/ActualCoordinateZoomFailureTransportChecks.lean' | sha256sum -c -
echo 'BFAE5D2ECAA63D258742FC776B3A21720744F0238A6624D4800304072FFE92F9  lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.lean' | sha256sum -c -
echo '8D2F2596FEA7917F306F1F26907563DD78181D5973305F644F597BC704383979  lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMomentChecks.lean' | sha256sum -c -
echo '29BD63CC0A9DB1D281A2F563FF39601BE567509FE4618E2E0F303BC70202D390  lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMargin.lean' | sha256sum -c -
echo '9C342FC46185F19EFD2652C9AF2CA99C81D52DCA69ED06997EE32CCD09497096  lean/PvNP/RealizableHardness/ActualOriginalFailureFixedMomentCaller.lean' | sha256sum -c -
echo '147F5070807487DC4D0966033186DE965BA9FC575C22BD233D3D55B8E54CE4AE  lean/PvNP/RealizableHardness/ActualSelectedHighEnergyTail.lean' | sha256sum -c -
echo '96895F1887B1D1F744AD79619C8910FBEB63CAC9C0741569247960072DE2E1FD  lean/PvNP/RealizableHardness/ActualSelectedSpectralTailGeometry.lean' | sha256sum -c -
echo '557ECCC674D31877E3DCE8D3D6D44DF5DCE91A9CFD78BBE6A5DE8C8967BCC4AE  lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparison.lean' | sha256sum -c -
echo 'EF3601C6FF9A4DACE7FBD3B64AE5D7CD461666EB995B0C5E0FE0AC6B3D294C4E  lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignal.lean' | sha256sum -c -
echo '3279C65C46676F95F3D1129EEDE791E6DF7C3160FA8C4442FE4777C8710571F3  lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignalChecks.lean' | sha256sum -c -
echo '71D83E3D7FB09915ED5BEC3E05EA4553FADEB61EE77F580499FFD32CF18EE9A8  lean/PvNP/RealizableHardness/ActualOriginalFailureRowGenericFixedMomentCaller.lean' | sha256sum -c -
export PATH="$PWD/offline-bin:$HOME/.elan/bin:$PATH"
lean --version >/tmp/cmmsa_analytic_20260930T192759Z-evidence/toolchain.txt
git -C .lake/packages/cslib rev-parse HEAD >/tmp/cmmsa_analytic_20260930T192759Z-evidence/cslib-revision.txt
sha256sum lake-manifest.json lean-toolchain lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMarginChecks.lean lean/PvNP/RealizableHardness/ActualOriginalFailureRowGenericFixedMomentCallerChecks.lean lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparisonChecks.lean lean/PvNP/RealizableHardness/ActualSelectedSpectralTailGeometryChecks.lean lean/PvNP/RealizableHardness/ActualSelectedHighEnergyTailChecks.lean lean/PvNP/RealizableHardness/ActualOriginalFailureFixedMomentCallerChecks.lean lean/PvNP/RealizableHardness/ActualOriginalFailureAnalyticCallerChecks.lean lean/PvNP/RealizableHardness/ActualOriginalFailureAnalyticCaller.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticNumerics.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticNumericsChecks.lean lean/PvNP/RealizableHardness/ActualFiniteMomentLpBounds.lean lean/PvNP/RealizableHardness/ActualSelectedSpectralParameters.lean lean/PvNP/RealizableHardness/ActualCoordinateZoomFailureTransport.lean lean/PvNP/RealizableHardness/ActualCoordinateZoomFailureTransportChecks.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMomentChecks.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMargin.lean lean/PvNP/RealizableHardness/ActualOriginalFailureFixedMomentCaller.lean lean/PvNP/RealizableHardness/ActualSelectedHighEnergyTail.lean lean/PvNP/RealizableHardness/ActualSelectedSpectralTailGeometry.lean lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparison.lean lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignal.lean lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignalChecks.lean lean/PvNP/RealizableHardness/ActualOriginalFailureRowGenericFixedMomentCaller.lean >/tmp/cmmsa_analytic_20260930T192759Z-evidence/source-before.sha256
rm -f .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignal.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignalChecks.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualOriginalFailureRowGenericFixedMomentCaller.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualOriginalFailureRowGenericFixedMomentCallerChecks.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMargin.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMarginChecks.olean
set +e
timeout --signal=TERM --kill-after=20s 900s lake build PvNP.RealizableHardness.ActualSelectedHighErrorAdditiveSignal >/tmp/cmmsa_analytic_20260930T192759Z-evidence/prebuild-0.stdout 2>/tmp/cmmsa_analytic_20260930T192759Z-evidence/prebuild-0.stderr
rc=$?
set -e
printf "%s\n" "$rc" >/tmp/cmmsa_analytic_20260930T192759Z-evidence/prebuild-0.native-exit
if [ "$rc" -ne 0 ]; then exit "$rc"; fi
sha256sum lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignal.lean .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignal.olean >/tmp/cmmsa_analytic_20260930T192759Z-evidence/prebuild-0.pins.sha256
set +e
timeout --signal=TERM --kill-after=20s 900s lake build PvNP.RealizableHardness.ActualSelectedHighErrorAdditiveSignalChecks >/tmp/cmmsa_analytic_20260930T192759Z-evidence/prebuild-1.stdout 2>/tmp/cmmsa_analytic_20260930T192759Z-evidence/prebuild-1.stderr
rc=$?
set -e
printf "%s\n" "$rc" >/tmp/cmmsa_analytic_20260930T192759Z-evidence/prebuild-1.native-exit
if [ "$rc" -ne 0 ]; then exit "$rc"; fi
sha256sum lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignalChecks.lean .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignalChecks.olean >/tmp/cmmsa_analytic_20260930T192759Z-evidence/prebuild-1.pins.sha256
set +e
timeout --signal=TERM --kill-after=20s 900s lake build PvNP.RealizableHardness.ActualOriginalFailureRowGenericFixedMomentCaller >/tmp/cmmsa_analytic_20260930T192759Z-evidence/prebuild-2.stdout 2>/tmp/cmmsa_analytic_20260930T192759Z-evidence/prebuild-2.stderr
rc=$?
set -e
printf "%s\n" "$rc" >/tmp/cmmsa_analytic_20260930T192759Z-evidence/prebuild-2.native-exit
if [ "$rc" -ne 0 ]; then exit "$rc"; fi
sha256sum lean/PvNP/RealizableHardness/ActualOriginalFailureRowGenericFixedMomentCaller.lean .lake/build/lib/lean/PvNP/RealizableHardness/ActualOriginalFailureRowGenericFixedMomentCaller.olean >/tmp/cmmsa_analytic_20260930T192759Z-evidence/prebuild-2.pins.sha256
set +e
timeout --signal=TERM --kill-after=20s 900s lake build PvNP.RealizableHardness.ActualOriginalFailureRowGenericFixedMomentCallerChecks >/tmp/cmmsa_analytic_20260930T192759Z-evidence/prebuild-3.stdout 2>/tmp/cmmsa_analytic_20260930T192759Z-evidence/prebuild-3.stderr
rc=$?
set -e
printf "%s\n" "$rc" >/tmp/cmmsa_analytic_20260930T192759Z-evidence/prebuild-3.native-exit
if [ "$rc" -ne 0 ]; then exit "$rc"; fi
sha256sum lean/PvNP/RealizableHardness/ActualOriginalFailureRowGenericFixedMomentCallerChecks.lean .lake/build/lib/lean/PvNP/RealizableHardness/ActualOriginalFailureRowGenericFixedMomentCallerChecks.olean >/tmp/cmmsa_analytic_20260930T192759Z-evidence/prebuild-3.pins.sha256
set +e
timeout --signal=TERM --kill-after=20s 900s lake build PvNP.RealizableHardness.ActualSelectedComplementAnalyticMargin >/tmp/cmmsa_analytic_20260930T192759Z-evidence/prebuild-4.stdout 2>/tmp/cmmsa_analytic_20260930T192759Z-evidence/prebuild-4.stderr
rc=$?
set -e
printf "%s\n" "$rc" >/tmp/cmmsa_analytic_20260930T192759Z-evidence/prebuild-4.native-exit
if [ "$rc" -ne 0 ]; then exit "$rc"; fi
sha256sum lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMargin.lean .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMargin.olean >/tmp/cmmsa_analytic_20260930T192759Z-evidence/prebuild-4.pins.sha256
timeout --signal=TERM --kill-after=20s 900s lake build PvNP.RealizableHardness.ActualSelectedComplementAnalyticMarginChecks >/tmp/cmmsa_analytic_20260930T192759Z-evidence/build.stdout 2>/tmp/cmmsa_analytic_20260930T192759Z-evidence/build.stderr
sha256sum lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMarginChecks.lean lean/PvNP/RealizableHardness/ActualOriginalFailureRowGenericFixedMomentCallerChecks.lean lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparisonChecks.lean lean/PvNP/RealizableHardness/ActualSelectedSpectralTailGeometryChecks.lean lean/PvNP/RealizableHardness/ActualSelectedHighEnergyTailChecks.lean lean/PvNP/RealizableHardness/ActualOriginalFailureFixedMomentCallerChecks.lean lean/PvNP/RealizableHardness/ActualOriginalFailureAnalyticCallerChecks.lean lean/PvNP/RealizableHardness/ActualOriginalFailureAnalyticCaller.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticNumerics.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticNumericsChecks.lean lean/PvNP/RealizableHardness/ActualFiniteMomentLpBounds.lean lean/PvNP/RealizableHardness/ActualSelectedSpectralParameters.lean lean/PvNP/RealizableHardness/ActualCoordinateZoomFailureTransport.lean lean/PvNP/RealizableHardness/ActualCoordinateZoomFailureTransportChecks.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMomentChecks.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMargin.lean lean/PvNP/RealizableHardness/ActualOriginalFailureFixedMomentCaller.lean lean/PvNP/RealizableHardness/ActualSelectedHighEnergyTail.lean lean/PvNP/RealizableHardness/ActualSelectedSpectralTailGeometry.lean lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparison.lean lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignal.lean lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignalChecks.lean lean/PvNP/RealizableHardness/ActualOriginalFailureRowGenericFixedMomentCaller.lean .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignal.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignalChecks.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualOriginalFailureRowGenericFixedMomentCaller.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualOriginalFailureRowGenericFixedMomentCallerChecks.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMargin.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMarginChecks.olean >/tmp/cmmsa_analytic_20260930T192759Z-evidence/pins.sha256
