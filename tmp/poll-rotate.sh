#!/bin/bash
if [ -f /home/dfredriksen_quantyra_org/compile-rotate.log ]; then
  wc -l /home/dfredriksen_quantyra_org/compile-rotate.log
  tail -n 70 /home/dfredriksen_quantyra_org/compile-rotate.log
else
  echo NOLOG
fi
pgrep -af "lake|lean" || echo NOPROC
