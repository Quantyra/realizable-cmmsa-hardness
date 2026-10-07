#!/usr/bin/env bash
set -u
cd /home/dfredriksen_quantyra_org/cmmsa_tagged_concrete_sampler_run
export PATH=/home/dfredriksen_quantyra_org/.elan/bin:$PATH
set +e
lake build PvNP.RealizableHardness.ActualTaggedConcreteStarLawChecks > /home/dfredriksen_quantyra_org/cmmsa_tagged_concrete_sampler_build.log 2>&1
rc=$?
printf '%s\n' "$rc" > /home/dfredriksen_quantyra_org/cmmsa_tagged_concrete_sampler.exit
exit "$rc"
