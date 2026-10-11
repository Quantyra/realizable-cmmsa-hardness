# Selected visible posterior numerical margin

E002/S3137. Implements the scalar step of the recorded 2026-10-11 Posterior loss ledger and its numerical margin argument. Uncompiled and unaccepted.

The actual block lower bound J>=4*h^4, h>=16 and r<=h imply the retained-leaf exponent 2J-2*h^4-2h-r-1>=10*h^2 and the full required window slack J+2h+1<=3J-2*h^4-r. Therefore the per-side leaf cost epsilon is at most qdecay(10,h). Zeta is also at most that quantity, so the transfer error plus two leaf errors plus four exclusion charges is at most seven qdecay(10,h).

The inequality 10*h^2>=2h+7 and 2^7>=70 imply seven qdecay(10,h)<=2^(-2h)/10. The actual original threshold e>=2^(-2h) and the single rational C>e/5 yield a strict bound below C/2. The exported weak bound supplies exactly the margin expected by ActualVisiblePosteriorLedger. The selected specialization obtains the height/rank facts from the same existing numericSourceFloor and refresh_threshold_bounds; it introduces no extra draw-dependent choice or favorable mass assumption.

This source discharges scalar comparisons only. Readiness and the completion bad-advice bound use the separately captured common-base construction. The actual pointwise canonical-table and row-frame score identities, legitimate strategy, all-window list estimates and source NO remain application obligations. Parent interfaces are exact failed/unaccepted Full114 pins and both candidate dependencies are immutable. No local Lean or Lake ran.

Remaining to-do list: kernel/axiom/warning verification, actual score and posterior integration, complete strategy/source NO, effective base/runtime, replay and independent/final certification.
