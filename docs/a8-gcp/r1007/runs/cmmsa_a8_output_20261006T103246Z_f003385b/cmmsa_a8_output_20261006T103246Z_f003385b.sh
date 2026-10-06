#!/usr/bin/env bash
# Rendered/uploaded by runner.py; this file is never executed on Windows.
set -Eeuo pipefail
test "$(uname -s)" = Linux
test "$HOME" = /home/dfredriksen_quantyra_org
RUN_ID='cmmsa_a8_output_20261006T103246Z_f003385b'
CMMSA_WORK="$HOME/$RUN_ID"
CMMSA_EVIDENCE="$HOME/cmmsa-evidence/$RUN_ID-evidence"
test ! -e "$CMMSA_WORK"
test ! -e "$CMMSA_EVIDENCE"
mkdir -p "$HOME/cmmsa-evidence"
mkdir "$CMMSA_EVIDENCE"
date -u +%Y-%m-%dT%H:%M:%SZ >"$CMMSA_EVIDENCE/started.utc"
printf '%s\n' "$RUN_ID" >"$CMMSA_EVIDENCE/run-id.txt"

cmmsa_finish() {
  cmmsa_exit=$?
  trap - EXIT INT TERM
  set +e
  if [ -f "$CMMSA_WORK/cloud_capture.py" ]; then
    cd "$CMMSA_WORK"
    python3 cloud_capture.py finish "$CMMSA_EVIDENCE" \
      >"$CMMSA_EVIDENCE/finish.stdout" 2>"$CMMSA_EVIDENCE/finish.stderr"
    cmmsa_finish_exit=$?
    printf '%s\n' "$cmmsa_finish_exit" >"$CMMSA_EVIDENCE/finish.native-exit"
    if [ "$cmmsa_exit" -eq 0 ] && [ "$cmmsa_finish_exit" -ne 0 ]; then cmmsa_exit=1; fi
  fi
  date -u +%Y-%m-%dT%H:%M:%SZ >"$CMMSA_EVIDENCE/terminal.utc"
  printf '%s\n' "$cmmsa_exit" >"$CMMSA_EVIDENCE/native-exit"
  tar -czf "$CMMSA_EVIDENCE.tar.gz.next" -C "$CMMSA_EVIDENCE" .
  cmmsa_archive_exit=$?
  if [ "$cmmsa_archive_exit" -eq 0 ]; then
    mv "$CMMSA_EVIDENCE.tar.gz.next" "$CMMSA_EVIDENCE.tar.gz"
  elif [ "$cmmsa_exit" -eq 0 ]; then
    cmmsa_exit=1
  fi
  exit "$cmmsa_exit"
}
trap cmmsa_finish EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

systemctl is-active --quiet quantyra-idle-shutdown.timer
systemctl is-enabled --quiet quantyra-idle-shutdown.timer
sudo systemd-run --unit="$RUN_ID-hard-stop" --on-active=70min /sbin/shutdown -h now
echo '6AD360A7C38FD415D6DF98E8CCD72C4AA23326B9ADD6C7FD5B0DE2A6D2EF8BD6  /tmp/cmmsa_a8_output_20261006T103246Z_f003385b.tar.gz' | sha256sum -c -
mkdir "$CMMSA_WORK"
tar -xzf "/tmp/$RUN_ID.tar.gz" -C "$CMMSA_WORK"
test -d "$HOME/cmmsa_a8_output_20261006T095324Z_3ea31944/.lake"
cp -al "$HOME/cmmsa_a8_output_20261006T095324Z_3ea31944/.lake" "$CMMSA_WORK/.lake"
cd "$CMMSA_WORK"
echo 'A57687E25D656555C87BF66DA5DA09DF570800795338E02C34BE0DAF9F7C059E  capture-manifest.json' | sha256sum -c -
mkdir offline-bin
printf '#!/usr/bin/env bash\ncase "$1" in clone|fetch|pull|ls-remote) echo "Network Git disabled" >&2; exit 93;; esac\nexec /usr/bin/git "$@"\n' >offline-bin/git
chmod +x offline-bin/git
export PATH="$PWD/offline-bin:$HOME/.elan/bin:$PATH"
python3 cloud_capture.py begin "$CMMSA_EVIDENCE" \
  >"$CMMSA_EVIDENCE/setup.stdout" 2>"$CMMSA_EVIDENCE/setup.stderr"
python3 cloud_capture.py compile "$CMMSA_EVIDENCE"
