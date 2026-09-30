#!/usr/bin/env bash
set -Eeuo pipefail
systemctl is-active --quiet quantyra-idle-shutdown.timer
systemctl is-enabled --quiet quantyra-idle-shutdown.timer
sudo systemd-run --unit=cmmsa_analytic_20260930T121153Z-hard-stop --on-active=18min /sbin/shutdown -h now
mkdir -p /tmp/cmmsa_analytic_20260930T121153Z-evidence
trap 'rc=$?; printf "%s\n" "$rc" >/tmp/cmmsa_analytic_20260930T121153Z-evidence/native-exit; tar -czf /tmp/cmmsa_analytic_20260930T121153Z-evidence.tar.gz -C /tmp/cmmsa_analytic_20260930T121153Z-evidence .; exit "$rc"' EXIT
echo '960c147d2a6559014f767429611e6cbe493e93593c65eaf133cd00138832a25e  /tmp/cmmsa_analytic_20260930T121153Z.tar.gz' | sha256sum -c -
WORK="$HOME/cmmsa_analytic_20260930T040837Z"
if [ 'yes' = 'yes' ]; then
  test -d "$WORK/.lake/build"
  python3 - "$WORK" /tmp/cmmsa_analytic_20260930T121153Z.tar.gz lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparisonChecks.lean,lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMarginChecks.lean,lean/PvNP/RealizableHardness/ActualSelectedSpectralTailGeometryChecks.lean,lean/PvNP/RealizableHardness/ActualSelectedHighEnergyTailChecks.lean,lean/PvNP/RealizableHardness/ActualOriginalFailureFixedMomentCallerChecks.lean,lean/PvNP/RealizableHardness/ActualOriginalFailureAnalyticCallerChecks.lean,lean/PvNP/RealizableHardness/ActualOriginalFailureAnalyticCaller.lean,lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticNumerics.lean,lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticNumericsChecks.lean,lean/PvNP/RealizableHardness/ActualFiniteMomentLpBounds.lean,lean/PvNP/RealizableHardness/ActualSelectedSpectralParameters.lean,lean/PvNP/RealizableHardness/ActualCoordinateZoomFailureTransport.lean,lean/PvNP/RealizableHardness/ActualCoordinateZoomFailureTransportChecks.lean,lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.lean,lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMomentChecks.lean,lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMargin.lean,lean/PvNP/RealizableHardness/ActualOriginalFailureFixedMomentCaller.lean,lean/PvNP/RealizableHardness/ActualSelectedHighEnergyTail.lean,lean/PvNP/RealizableHardness/ActualSelectedSpectralTailGeometry.lean,lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparison.lean <<'PY'
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
  tar -xzf /tmp/cmmsa_analytic_20260930T121153Z.tar.gz -C "$WORK"
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
echo 'E53579C62F6D57D73734AB66962AC0DA2C85DF17AC972D8E4794702CF4070A9F  lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparisonChecks.lean' | sha256sum -c -
echo '58A7BFD6A8F16236DBA38ECE1A5D98F6719007AC2DCA9B6E56DDB6601A02E099  lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMarginChecks.lean' | sha256sum -c -
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
echo 'BEFEB457353C68EB262DC488528D00A509F8C5B5A88B5924E1A490EADEE21F40  lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMargin.lean' | sha256sum -c -
echo '9C342FC46185F19EFD2652C9AF2CA99C81D52DCA69ED06997EE32CCD09497096  lean/PvNP/RealizableHardness/ActualOriginalFailureFixedMomentCaller.lean' | sha256sum -c -
echo '147F5070807487DC4D0966033186DE965BA9FC575C22BD233D3D55B8E54CE4AE  lean/PvNP/RealizableHardness/ActualSelectedHighEnergyTail.lean' | sha256sum -c -
echo '96895F1887B1D1F744AD79619C8910FBEB63CAC9C0741569247960072DE2E1FD  lean/PvNP/RealizableHardness/ActualSelectedSpectralTailGeometry.lean' | sha256sum -c -
echo 'CFD5C8CA77CFDEBA226673CD3EFAFC1624929D135173BEE8E1698B591A6A1590  lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparison.lean' | sha256sum -c -
export PATH="$PWD/offline-bin:$HOME/.elan/bin:$PATH"
lean --version >/tmp/cmmsa_analytic_20260930T121153Z-evidence/toolchain.txt
git -C .lake/packages/cslib rev-parse HEAD >/tmp/cmmsa_analytic_20260930T121153Z-evidence/cslib-revision.txt
sha256sum lake-manifest.json lean-toolchain lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparisonChecks.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMarginChecks.lean lean/PvNP/RealizableHardness/ActualSelectedSpectralTailGeometryChecks.lean lean/PvNP/RealizableHardness/ActualSelectedHighEnergyTailChecks.lean lean/PvNP/RealizableHardness/ActualOriginalFailureFixedMomentCallerChecks.lean lean/PvNP/RealizableHardness/ActualOriginalFailureAnalyticCallerChecks.lean lean/PvNP/RealizableHardness/ActualOriginalFailureAnalyticCaller.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticNumerics.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticNumericsChecks.lean lean/PvNP/RealizableHardness/ActualFiniteMomentLpBounds.lean lean/PvNP/RealizableHardness/ActualSelectedSpectralParameters.lean lean/PvNP/RealizableHardness/ActualCoordinateZoomFailureTransport.lean lean/PvNP/RealizableHardness/ActualCoordinateZoomFailureTransportChecks.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMomentChecks.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMargin.lean lean/PvNP/RealizableHardness/ActualOriginalFailureFixedMomentCaller.lean lean/PvNP/RealizableHardness/ActualSelectedHighEnergyTail.lean lean/PvNP/RealizableHardness/ActualSelectedSpectralTailGeometry.lean lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparison.lean >/tmp/cmmsa_analytic_20260930T121153Z-evidence/source-before.sha256
rm -f .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparison.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparisonChecks.olean
set +e
timeout --signal=TERM --kill-after=20s 900s lake build PvNP.RealizableHardness.ActualSelectedHighErrorSignalComparison >/tmp/cmmsa_analytic_20260930T121153Z-evidence/prebuild-0.stdout 2>/tmp/cmmsa_analytic_20260930T121153Z-evidence/prebuild-0.stderr
rc=$?
set -e
printf "%s\n" "$rc" >/tmp/cmmsa_analytic_20260930T121153Z-evidence/prebuild-0.native-exit
if [ "$rc" -ne 0 ]; then exit "$rc"; fi
sha256sum lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparison.lean .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparison.olean >/tmp/cmmsa_analytic_20260930T121153Z-evidence/prebuild-0.pins.sha256
timeout --signal=TERM --kill-after=20s 900s lake build PvNP.RealizableHardness.ActualSelectedHighErrorSignalComparisonChecks >/tmp/cmmsa_analytic_20260930T121153Z-evidence/build.stdout 2>/tmp/cmmsa_analytic_20260930T121153Z-evidence/build.stderr
sha256sum lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparisonChecks.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMarginChecks.lean lean/PvNP/RealizableHardness/ActualSelectedSpectralTailGeometryChecks.lean lean/PvNP/RealizableHardness/ActualSelectedHighEnergyTailChecks.lean lean/PvNP/RealizableHardness/ActualOriginalFailureFixedMomentCallerChecks.lean lean/PvNP/RealizableHardness/ActualOriginalFailureAnalyticCallerChecks.lean lean/PvNP/RealizableHardness/ActualOriginalFailureAnalyticCaller.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticNumerics.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticNumericsChecks.lean lean/PvNP/RealizableHardness/ActualFiniteMomentLpBounds.lean lean/PvNP/RealizableHardness/ActualSelectedSpectralParameters.lean lean/PvNP/RealizableHardness/ActualCoordinateZoomFailureTransport.lean lean/PvNP/RealizableHardness/ActualCoordinateZoomFailureTransportChecks.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMomentChecks.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMargin.lean lean/PvNP/RealizableHardness/ActualOriginalFailureFixedMomentCaller.lean lean/PvNP/RealizableHardness/ActualSelectedHighEnergyTail.lean lean/PvNP/RealizableHardness/ActualSelectedSpectralTailGeometry.lean lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparison.lean .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparison.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparisonChecks.olean >/tmp/cmmsa_analytic_20260930T121153Z-evidence/pins.sha256
