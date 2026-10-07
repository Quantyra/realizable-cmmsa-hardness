#!/bin/bash
if [ -f /home/dfredriksen_quantyra_org/compile-overlap.log ]; then
  wc -l /home/dfredriksen_quantyra_org/compile-overlap.log
  tail -n 60 /home/dfredriksen_quantyra_org/compile-overlap.log
else
  echo NOLOG
fi
pgrep -af "lake|lean" || echo NOPROC
