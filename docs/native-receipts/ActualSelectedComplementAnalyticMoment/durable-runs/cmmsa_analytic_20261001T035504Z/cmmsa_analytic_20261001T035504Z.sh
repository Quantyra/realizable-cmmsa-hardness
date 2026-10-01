#!/usr/bin/env bash
set -Eeuo pipefail
systemctl is-active --quiet quantyra-idle-shutdown.timer
systemctl is-enabled --quiet quantyra-idle-shutdown.timer
sudo systemd-run --unit=cmmsa_analytic_20261001T035504Z-hard-stop --on-active=18min /sbin/shutdown -h now
mkdir -p /tmp/cmmsa_analytic_20261001T035504Z-evidence
trap 'rc=$?; printf "%s\n" "$rc" >/tmp/cmmsa_analytic_20261001T035504Z-evidence/native-exit; tar -czf /tmp/cmmsa_analytic_20261001T035504Z-evidence.tar.gz -C /tmp/cmmsa_analytic_20261001T035504Z-evidence .; exit "$rc"' EXIT
echo '615e500cc1f9098a9b844c93abdb7571b4e4cd72a384d7cc211cee604c1842fe  /tmp/cmmsa_analytic_20261001T035504Z.tar.gz' | sha256sum -c -
WORK="$HOME/cmmsa_analytic_20260930T040837Z"
if [ 'yes' = 'yes' ]; then
  test -d "$WORK/.lake/build"
  python3 - "$WORK" /tmp/cmmsa_analytic_20261001T035504Z.tar.gz lean/PvNP/RealizableHardness/ActualFiniteAppendSpectral47ExactInhabitantChecks.lean,lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMarginChecks.lean,lean/PvNP/RealizableHardness/ActualOriginalFailureRowGenericFixedMomentCallerChecks.lean,lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparisonChecks.lean,lean/PvNP/RealizableHardness/ActualSelectedSpectralTailGeometryChecks.lean,lean/PvNP/RealizableHardness/ActualSelectedHighEnergyTailChecks.lean,lean/PvNP/RealizableHardness/ActualOriginalFailureFixedMomentCallerChecks.lean,lean/PvNP/RealizableHardness/ActualOriginalFailureAnalyticCallerChecks.lean,lean/PvNP/RealizableHardness/ActualOriginalFailureAnalyticCaller.lean,lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticNumerics.lean,lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticNumericsChecks.lean,lean/PvNP/RealizableHardness/ActualFiniteMomentLpBounds.lean,lean/PvNP/RealizableHardness/ActualSelectedSpectralParameters.lean,lean/PvNP/RealizableHardness/ActualCoordinateZoomFailureTransport.lean,lean/PvNP/RealizableHardness/ActualCoordinateZoomFailureTransportChecks.lean,lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.lean,lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMomentChecks.lean,lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMargin.lean,lean/PvNP/RealizableHardness/ActualOriginalFailureFixedMomentCaller.lean,lean/PvNP/RealizableHardness/ActualSelectedHighEnergyTail.lean,lean/PvNP/RealizableHardness/ActualSelectedSpectralTailGeometry.lean,lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparison.lean,lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignal.lean,lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignalChecks.lean,lean/PvNP/RealizableHardness/ActualOriginalFailureRowGenericFixedMomentCaller.lean,lean/PvNP/RealizableHardness/ActualFiniteAppendSpectral47.lean,lean/PvNP/RealizableHardness/ActualFiniteAppendSpectral47Checks.lean,lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46.lean,lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46Checks.lean,lean/PvNP/RealizableHardness/ActualFiniteBinarySurjectionCounting.lean,lean/PvNP/RealizableHardness/ActualFiniteBinarySurjectionCountingChecks.lean,lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46Derivative.lean,lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46DerivativeChecks.lean,lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46BooleanGlobalness.lean,lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46BooleanGlobalnessChecks.lean,lean/PvNP/RealizableHardness/ActualFiniteBinaryImageFibres.lean,lean/PvNP/RealizableHardness/ActualFiniteBinaryImageFibresChecks.lean,lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46FinitePeeling.lean,lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46FinitePeelingChecks.lean,lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46MixedPeeling.lean,lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46MixedPeelingChecks.lean,lean/PvNP/RealizableHardness/ActualFiniteBinaryImageOrbit.lean,lean/PvNP/RealizableHardness/ActualFiniteBinaryImageOrbitChecks.lean,lean/PvNP/RealizableHardness/ActualFiniteBinaryImageOrbitFourier.lean,lean/PvNP/RealizableHardness/ActualFiniteBinaryImageOrbitFourierChecks.lean,lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46PA4Transport.lean,lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46PA4TransportChecks.lean,lean/PvNP/RealizableHardness/ActualFiniteAppendImageWeighted.lean,lean/PvNP/RealizableHardness/ActualFiniteAppendImageWeightedChecks.lean,lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46FourierA16.lean,lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46FourierA16Checks.lean,lean/PvNP/RealizableHardness/ActualFiniteAppendImageTailBridge.lean,lean/PvNP/RealizableHardness/ActualFiniteAppendImageTailBridgeChecks.lean,lean/PvNP/RealizableHardness/ActualFiniteFrameProductRatio.lean,lean/PvNP/RealizableHardness/ActualFiniteFrameProductRatioChecks.lean,lean/PvNP/RealizableHardness/ActualFiniteAppendImagePerImageEnergy.lean,lean/PvNP/RealizableHardness/ActualFiniteAppendImagePerImageEnergyChecks.lean,lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46CommonDerivative.lean,lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46CommonDerivativeChecks.lean,lean/PvNP/RealizableHardness/ActualFiniteAppendGlobalImageEnergy.lean,lean/PvNP/RealizableHardness/ActualFiniteAppendGlobalImageEnergyChecks.lean,lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46CommonA16.lean,lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46CommonA16Checks.lean,lean/PvNP/RealizableHardness/ActualFiniteAppendSpectral47ExactInhabitant.lean <<'PY'
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
  tar -xzf /tmp/cmmsa_analytic_20261001T035504Z.tar.gz -C "$WORK"
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
echo 'E8EE4F3A3B4F7E875A147D7CB87A520C52BA838087FC713771B437F551EFBC4F  lean/PvNP/RealizableHardness/ActualFiniteAppendSpectral47ExactInhabitantChecks.lean' | sha256sum -c -
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
echo '26A2011F190746E0B80788C42C7C0F0C1120A31D6D0FD8A3E09569999A1ABCCC  lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMargin.lean' | sha256sum -c -
echo '9C342FC46185F19EFD2652C9AF2CA99C81D52DCA69ED06997EE32CCD09497096  lean/PvNP/RealizableHardness/ActualOriginalFailureFixedMomentCaller.lean' | sha256sum -c -
echo '147F5070807487DC4D0966033186DE965BA9FC575C22BD233D3D55B8E54CE4AE  lean/PvNP/RealizableHardness/ActualSelectedHighEnergyTail.lean' | sha256sum -c -
echo '96895F1887B1D1F744AD79619C8910FBEB63CAC9C0741569247960072DE2E1FD  lean/PvNP/RealizableHardness/ActualSelectedSpectralTailGeometry.lean' | sha256sum -c -
echo '557ECCC674D31877E3DCE8D3D6D44DF5DCE91A9CFD78BBE6A5DE8C8967BCC4AE  lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparison.lean' | sha256sum -c -
echo 'EF3601C6FF9A4DACE7FBD3B64AE5D7CD461666EB995B0C5E0FE0AC6B3D294C4E  lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignal.lean' | sha256sum -c -
echo '3279C65C46676F95F3D1129EEDE791E6DF7C3160FA8C4442FE4777C8710571F3  lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignalChecks.lean' | sha256sum -c -
echo '71D83E3D7FB09915ED5BEC3E05EA4553FADEB61EE77F580499FFD32CF18EE9A8  lean/PvNP/RealizableHardness/ActualOriginalFailureRowGenericFixedMomentCaller.lean' | sha256sum -c -
echo '1240DCAC934609D098BE4EBBE56EA800B4E0E3B053DE28FE33E71A6AB2F8AC9B  lean/PvNP/RealizableHardness/ActualFiniteAppendSpectral47.lean' | sha256sum -c -
echo 'EB96FB368B4E43C6F265E17ABE1D895E60A1D8A719CA559D0C22318C097847AD  lean/PvNP/RealizableHardness/ActualFiniteAppendSpectral47Checks.lean' | sha256sum -c -
echo 'D9AD6A98C41DC1FF2C0CF23D55C8D133E25C87BAABB99F1F1D66916A8EAA35C9  lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46.lean' | sha256sum -c -
echo 'DA60196AD8DCA02FB085AC937784FA4C1F33F478B34084497C69B9254C10AC56  lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46Checks.lean' | sha256sum -c -
echo '10242EF87526FCEDA64B834F816034D2C3F8CEEBEE0311017FA84F343673A55F  lean/PvNP/RealizableHardness/ActualFiniteBinarySurjectionCounting.lean' | sha256sum -c -
echo '0ACAB9C452957AAE2A54ADC5E7765A7771CAF4B47AE895B86335B9F8C37EF1B4  lean/PvNP/RealizableHardness/ActualFiniteBinarySurjectionCountingChecks.lean' | sha256sum -c -
echo '144A611EEFDE9E8748EB3BB5CA35DEDE89FD4AEDAD08DBC7ED27F156D66650E0  lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46Derivative.lean' | sha256sum -c -
echo 'D77099291728345828787943311048E9B3D32B071E29AA309505B4C2328FCE2B  lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46DerivativeChecks.lean' | sha256sum -c -
echo 'A6FB4CA92F38059AD4ADCF3EBF61E8CFFCFA7239EDEC31AE46BDF6E0543C2374  lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46BooleanGlobalness.lean' | sha256sum -c -
echo '36F1096433584C64E765491C9B7FF619B9819A46A9E128ABAE596BADA9597E11  lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46BooleanGlobalnessChecks.lean' | sha256sum -c -
echo 'E9A75321F80A6C3452BE95FC6A04E73F23C50724AE35F1973C4BABC124464E98  lean/PvNP/RealizableHardness/ActualFiniteBinaryImageFibres.lean' | sha256sum -c -
echo '1BF676EF8BEB273E09C6E5E8D1499451ED0B52D67A65C36A4B26BFA47454F24E  lean/PvNP/RealizableHardness/ActualFiniteBinaryImageFibresChecks.lean' | sha256sum -c -
echo '7FC942C7D147F546EE29E66D2D47DBDD7051FB1EAECCB354185DD257BB034B3A  lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46FinitePeeling.lean' | sha256sum -c -
echo '81A27BF3984CF8109F96AD1A42405718AB939BE05EA3AB48B54CF689DC42D9C9  lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46FinitePeelingChecks.lean' | sha256sum -c -
echo '370AA294AC09E6427AD7F1CD4590C4035660F4A250EEC28894CBA41413C0B9D5  lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46MixedPeeling.lean' | sha256sum -c -
echo '0D5FDE276556AC73A83BA7BB745D372ED1AB39AB8B938376D17918A43228CCD3  lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46MixedPeelingChecks.lean' | sha256sum -c -
echo 'D2BF441593DDE51A8DAD1B2414B8D098A6B2E9913C24E765D1C4397556B383CC  lean/PvNP/RealizableHardness/ActualFiniteBinaryImageOrbit.lean' | sha256sum -c -
echo 'EBB60AFA2BAA3AE0A895FB9EC85E735560C87A786BD7BBC9477A95B6B019C1FB  lean/PvNP/RealizableHardness/ActualFiniteBinaryImageOrbitChecks.lean' | sha256sum -c -
echo '10A87647DBE07681300A250266A469374EF3B7BB02FF818D97A5ABEFDB682F1A  lean/PvNP/RealizableHardness/ActualFiniteBinaryImageOrbitFourier.lean' | sha256sum -c -
echo '00B5FB9A16D3CC739E9C7D88DB54402F54A4E0B676EED976305143586859177C  lean/PvNP/RealizableHardness/ActualFiniteBinaryImageOrbitFourierChecks.lean' | sha256sum -c -
echo '422BD73ECC247765F8FA34B0DA8C0B41E4520FFAC9EBC16B9C88187E7E36FA7A  lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46PA4Transport.lean' | sha256sum -c -
echo '4FC3798B0C01DD094AE5779574CB6DF6573E3662ABFB1945258C059A6B4A979E  lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46PA4TransportChecks.lean' | sha256sum -c -
echo '0E2FE0E1A75B0CCC8E4955D97C0BE3973C0309B63D5A4224F342B05992ED66F8  lean/PvNP/RealizableHardness/ActualFiniteAppendImageWeighted.lean' | sha256sum -c -
echo 'FE908E05D20E5E7E1260307C3059444D0212DB823AC7E15EC6647FEF353077DD  lean/PvNP/RealizableHardness/ActualFiniteAppendImageWeightedChecks.lean' | sha256sum -c -
echo 'DE73C854A42AE18CCD6C0517D141ABF9DE5C9EFB71D51A2B914B6ABD9C74BF62  lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46FourierA16.lean' | sha256sum -c -
echo '9284ABEEEC32E468B2ED975E31EC522668E0AF2E6E9D6E76783702C9CD530DFE  lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46FourierA16Checks.lean' | sha256sum -c -
echo '7653F4D668DDA26C627B80844197A71751604A58A2ED85C30A8A3DF4C32D92AF  lean/PvNP/RealizableHardness/ActualFiniteAppendImageTailBridge.lean' | sha256sum -c -
echo '55EC94603343F293CA6869A8E06190867F0BEF05AEC9BFE64620CECDA076D183  lean/PvNP/RealizableHardness/ActualFiniteAppendImageTailBridgeChecks.lean' | sha256sum -c -
echo '92072C900DD1B3B0D77FF39D7B3F28856DD67957FEF407D79CBD25F1D547FD4C  lean/PvNP/RealizableHardness/ActualFiniteFrameProductRatio.lean' | sha256sum -c -
echo 'F8C224316A92A59C673A5CBF332B7CA97FC71CF030D865F08B79868E8F45707C  lean/PvNP/RealizableHardness/ActualFiniteFrameProductRatioChecks.lean' | sha256sum -c -
echo 'B3CBD9FD3DCE4E296432C1D3C8C3803CC4E16BFFA70AFFAFC0D8521CCDE0BE9A  lean/PvNP/RealizableHardness/ActualFiniteAppendImagePerImageEnergy.lean' | sha256sum -c -
echo 'A12D0ACB8B11B35C18101C26B8E1D98318DBFB4B6101AA6CC32E1D2F854C23F5  lean/PvNP/RealizableHardness/ActualFiniteAppendImagePerImageEnergyChecks.lean' | sha256sum -c -
echo '5F56C105F99EFBCB8B62A0E3B8FDA7A9683CA04B09C4F8524238A362E94D4EF3  lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46CommonDerivative.lean' | sha256sum -c -
echo '5D54C5978EFEFF6CB39DAD6DD70998E78E5154637732D16311E7B85E262C3016  lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46CommonDerivativeChecks.lean' | sha256sum -c -
echo '575A3773351409B8BA2FDCE1D88145C5D0D2E9C49550B6B89D3787E5F699F7BC  lean/PvNP/RealizableHardness/ActualFiniteAppendGlobalImageEnergy.lean' | sha256sum -c -
echo '1263F9BA88B9217A27B836DD8287D2DFCD7CD99A55E28E1BA1967056328DE62E  lean/PvNP/RealizableHardness/ActualFiniteAppendGlobalImageEnergyChecks.lean' | sha256sum -c -
echo '5FA83F553678D3FA77936F9B176A6EF7853C6DAF9AE57CBAD323D3B41DB604A8  lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46CommonA16.lean' | sha256sum -c -
echo 'F57DEC4EBC3BEA54169C65E79673CD0DE532232AE874D96CC686B96179A47A88  lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46CommonA16Checks.lean' | sha256sum -c -
echo 'BC308C23C592F5F52A09F4E01723197882C3CA6B366E02D5EBDA1342F87A4FEF  lean/PvNP/RealizableHardness/ActualFiniteAppendSpectral47ExactInhabitant.lean' | sha256sum -c -
export PATH="$PWD/offline-bin:$HOME/.elan/bin:$PATH"
lean --version >/tmp/cmmsa_analytic_20261001T035504Z-evidence/toolchain.txt
git -C .lake/packages/cslib rev-parse HEAD >/tmp/cmmsa_analytic_20261001T035504Z-evidence/cslib-revision.txt
sha256sum lake-manifest.json lean-toolchain lean/PvNP/RealizableHardness/ActualFiniteAppendSpectral47ExactInhabitantChecks.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMarginChecks.lean lean/PvNP/RealizableHardness/ActualOriginalFailureRowGenericFixedMomentCallerChecks.lean lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparisonChecks.lean lean/PvNP/RealizableHardness/ActualSelectedSpectralTailGeometryChecks.lean lean/PvNP/RealizableHardness/ActualSelectedHighEnergyTailChecks.lean lean/PvNP/RealizableHardness/ActualOriginalFailureFixedMomentCallerChecks.lean lean/PvNP/RealizableHardness/ActualOriginalFailureAnalyticCallerChecks.lean lean/PvNP/RealizableHardness/ActualOriginalFailureAnalyticCaller.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticNumerics.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticNumericsChecks.lean lean/PvNP/RealizableHardness/ActualFiniteMomentLpBounds.lean lean/PvNP/RealizableHardness/ActualSelectedSpectralParameters.lean lean/PvNP/RealizableHardness/ActualCoordinateZoomFailureTransport.lean lean/PvNP/RealizableHardness/ActualCoordinateZoomFailureTransportChecks.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMomentChecks.lean lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMargin.lean lean/PvNP/RealizableHardness/ActualOriginalFailureFixedMomentCaller.lean lean/PvNP/RealizableHardness/ActualSelectedHighEnergyTail.lean lean/PvNP/RealizableHardness/ActualSelectedSpectralTailGeometry.lean lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparison.lean lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignal.lean lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignalChecks.lean lean/PvNP/RealizableHardness/ActualOriginalFailureRowGenericFixedMomentCaller.lean lean/PvNP/RealizableHardness/ActualFiniteAppendSpectral47.lean lean/PvNP/RealizableHardness/ActualFiniteAppendSpectral47Checks.lean lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46.lean lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46Checks.lean lean/PvNP/RealizableHardness/ActualFiniteBinarySurjectionCounting.lean lean/PvNP/RealizableHardness/ActualFiniteBinarySurjectionCountingChecks.lean lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46Derivative.lean lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46DerivativeChecks.lean lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46BooleanGlobalness.lean lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46BooleanGlobalnessChecks.lean lean/PvNP/RealizableHardness/ActualFiniteBinaryImageFibres.lean lean/PvNP/RealizableHardness/ActualFiniteBinaryImageFibresChecks.lean lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46FinitePeeling.lean lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46FinitePeelingChecks.lean lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46MixedPeeling.lean lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46MixedPeelingChecks.lean lean/PvNP/RealizableHardness/ActualFiniteBinaryImageOrbit.lean lean/PvNP/RealizableHardness/ActualFiniteBinaryImageOrbitChecks.lean lean/PvNP/RealizableHardness/ActualFiniteBinaryImageOrbitFourier.lean lean/PvNP/RealizableHardness/ActualFiniteBinaryImageOrbitFourierChecks.lean lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46PA4Transport.lean lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46PA4TransportChecks.lean lean/PvNP/RealizableHardness/ActualFiniteAppendImageWeighted.lean lean/PvNP/RealizableHardness/ActualFiniteAppendImageWeightedChecks.lean lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46FourierA16.lean lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46FourierA16Checks.lean lean/PvNP/RealizableHardness/ActualFiniteAppendImageTailBridge.lean lean/PvNP/RealizableHardness/ActualFiniteAppendImageTailBridgeChecks.lean lean/PvNP/RealizableHardness/ActualFiniteFrameProductRatio.lean lean/PvNP/RealizableHardness/ActualFiniteFrameProductRatioChecks.lean lean/PvNP/RealizableHardness/ActualFiniteAppendImagePerImageEnergy.lean lean/PvNP/RealizableHardness/ActualFiniteAppendImagePerImageEnergyChecks.lean lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46CommonDerivative.lean lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46CommonDerivativeChecks.lean lean/PvNP/RealizableHardness/ActualFiniteAppendGlobalImageEnergy.lean lean/PvNP/RealizableHardness/ActualFiniteAppendGlobalImageEnergyChecks.lean lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46CommonA16.lean lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46CommonA16Checks.lean lean/PvNP/RealizableHardness/ActualFiniteAppendSpectral47ExactInhabitant.lean >/tmp/cmmsa_analytic_20261001T035504Z-evidence/source-before.sha256
rm -f .lake/build/lib/lean/PvNP/RealizableHardness/ActualFiniteAppendImageTailBridge.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualFiniteAppendImageTailBridgeChecks.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualFiniteAppendGlobalImageEnergy.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualFiniteAppendGlobalImageEnergyChecks.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualFiniteAppendSpectral47ExactInhabitant.olean .lake/build/lib/lean/PvNP/RealizableHardness/ActualFiniteAppendSpectral47ExactInhabitantChecks.olean
aggregate=0
set +e
timeout --signal=TERM --kill-after=20s 900s lake build PvNP.RealizableHardness.ActualFiniteAppendImageTailBridge >/tmp/cmmsa_analytic_20261001T035504Z-evidence/stage-0.stdout 2>/tmp/cmmsa_analytic_20261001T035504Z-evidence/stage-0.stderr
rc=$?
set -e
printf "%s\n" "$rc" >/tmp/cmmsa_analytic_20261001T035504Z-evidence/stage-0.native-exit

source_rc=$rc
if [ "$rc" -ne 0 ]; then aggregate=1; fi
if [ "$rc" -eq 0 ]; then sha256sum lean/PvNP/RealizableHardness/ActualFiniteAppendImageTailBridge.lean .lake/build/lib/lean/PvNP/RealizableHardness/ActualFiniteAppendImageTailBridge.olean >/tmp/cmmsa_analytic_20261001T035504Z-evidence/stage-0.pins.sha256; fi
if [ "$source_rc" -eq 0 ]; then
set +e
timeout --signal=TERM --kill-after=20s 900s lake build PvNP.RealizableHardness.ActualFiniteAppendImageTailBridgeChecks >/tmp/cmmsa_analytic_20261001T035504Z-evidence/stage-1.stdout 2>/tmp/cmmsa_analytic_20261001T035504Z-evidence/stage-1.stderr
rc=$?
set -e
else
rc=125
printf "Skipped: corresponding source stage failed\n" >/tmp/cmmsa_analytic_20261001T035504Z-evidence/stage-1.skip
fi
printf "%s\n" "$rc" >/tmp/cmmsa_analytic_20261001T035504Z-evidence/stage-1.native-exit

if [ "$rc" -ne 0 ] && [ "$rc" -ne 125 ]; then aggregate=1; fi
if [ "$rc" -eq 0 ]; then sha256sum lean/PvNP/RealizableHardness/ActualFiniteAppendImageTailBridgeChecks.lean .lake/build/lib/lean/PvNP/RealizableHardness/ActualFiniteAppendImageTailBridgeChecks.olean >/tmp/cmmsa_analytic_20261001T035504Z-evidence/stage-1.pins.sha256; fi
set +e
timeout --signal=TERM --kill-after=20s 900s lake build PvNP.RealizableHardness.ActualFiniteAppendGlobalImageEnergy >/tmp/cmmsa_analytic_20261001T035504Z-evidence/stage-2.stdout 2>/tmp/cmmsa_analytic_20261001T035504Z-evidence/stage-2.stderr
rc=$?
set -e
printf "%s\n" "$rc" >/tmp/cmmsa_analytic_20261001T035504Z-evidence/stage-2.native-exit

source_rc=$rc
if [ "$rc" -ne 0 ]; then aggregate=1; fi
if [ "$rc" -eq 0 ]; then sha256sum lean/PvNP/RealizableHardness/ActualFiniteAppendGlobalImageEnergy.lean .lake/build/lib/lean/PvNP/RealizableHardness/ActualFiniteAppendGlobalImageEnergy.olean >/tmp/cmmsa_analytic_20261001T035504Z-evidence/stage-2.pins.sha256; fi
if [ "$source_rc" -eq 0 ]; then
set +e
timeout --signal=TERM --kill-after=20s 900s lake build PvNP.RealizableHardness.ActualFiniteAppendGlobalImageEnergyChecks >/tmp/cmmsa_analytic_20261001T035504Z-evidence/stage-3.stdout 2>/tmp/cmmsa_analytic_20261001T035504Z-evidence/stage-3.stderr
rc=$?
set -e
else
rc=125
printf "Skipped: corresponding source stage failed\n" >/tmp/cmmsa_analytic_20261001T035504Z-evidence/stage-3.skip
fi
printf "%s\n" "$rc" >/tmp/cmmsa_analytic_20261001T035504Z-evidence/stage-3.native-exit

if [ "$rc" -ne 0 ] && [ "$rc" -ne 125 ]; then aggregate=1; fi
if [ "$rc" -eq 0 ]; then sha256sum lean/PvNP/RealizableHardness/ActualFiniteAppendGlobalImageEnergyChecks.lean .lake/build/lib/lean/PvNP/RealizableHardness/ActualFiniteAppendGlobalImageEnergyChecks.olean >/tmp/cmmsa_analytic_20261001T035504Z-evidence/stage-3.pins.sha256; fi
set +e
timeout --signal=TERM --kill-after=20s 900s lake build PvNP.RealizableHardness.ActualFiniteAppendSpectral47ExactInhabitant >/tmp/cmmsa_analytic_20261001T035504Z-evidence/stage-4.stdout 2>/tmp/cmmsa_analytic_20261001T035504Z-evidence/stage-4.stderr
rc=$?
set -e
printf "%s\n" "$rc" >/tmp/cmmsa_analytic_20261001T035504Z-evidence/stage-4.native-exit

source_rc=$rc
if [ "$rc" -ne 0 ]; then aggregate=1; fi
if [ "$rc" -eq 0 ]; then sha256sum lean/PvNP/RealizableHardness/ActualFiniteAppendSpectral47ExactInhabitant.lean .lake/build/lib/lean/PvNP/RealizableHardness/ActualFiniteAppendSpectral47ExactInhabitant.olean >/tmp/cmmsa_analytic_20261001T035504Z-evidence/stage-4.pins.sha256; fi
if [ "$source_rc" -eq 0 ]; then
set +e
timeout --signal=TERM --kill-after=20s 900s lake build PvNP.RealizableHardness.ActualFiniteAppendSpectral47ExactInhabitantChecks >/tmp/cmmsa_analytic_20261001T035504Z-evidence/stage-5.stdout 2>/tmp/cmmsa_analytic_20261001T035504Z-evidence/stage-5.stderr
rc=$?
set -e
else
rc=125
printf "Skipped: corresponding source stage failed\n" >/tmp/cmmsa_analytic_20261001T035504Z-evidence/stage-5.skip
fi
printf "%s\n" "$rc" >/tmp/cmmsa_analytic_20261001T035504Z-evidence/stage-5.native-exit

if [ "$rc" -ne 0 ] && [ "$rc" -ne 125 ]; then aggregate=1; fi
if [ "$rc" -eq 0 ]; then sha256sum lean/PvNP/RealizableHardness/ActualFiniteAppendSpectral47ExactInhabitantChecks.lean .lake/build/lib/lean/PvNP/RealizableHardness/ActualFiniteAppendSpectral47ExactInhabitantChecks.olean >/tmp/cmmsa_analytic_20261001T035504Z-evidence/stage-5.pins.sha256; fi
printf "%s\n" "$aggregate" >/tmp/cmmsa_analytic_20261001T035504Z-evidence/aggregate.native-exit
exit "$aggregate"

