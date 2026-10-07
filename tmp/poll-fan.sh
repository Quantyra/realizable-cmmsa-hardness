#!/bin/bash
if [ -f /home/dfredriksen_quantyra_org/compile-fan.log ]; then
  wc -l /home/dfredriksen_quantyra_org/compile-fan.log
  tail -n 80 /home/dfredriksen_quantyra_org/compile-fan.log
else
  echo NOLOG
fi
pgrep -af "lake|lean" || echo NOPROC
