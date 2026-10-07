#!/bin/bash
if [ -f /home/dfredriksen_quantyra_org/compile-halfwidth.log ]; then
  wc -l /home/dfredriksen_quantyra_org/compile-halfwidth.log
  tail -n 80 /home/dfredriksen_quantyra_org/compile-halfwidth.log
else
  echo NOLOG
fi
pgrep -af "lake|lean" || echo NOPROC
