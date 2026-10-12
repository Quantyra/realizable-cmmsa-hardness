# Full119 exact rank-Gram proof repair

UNCOMPILED and UNACCEPTED.

## 2026-10-11 Full118 rank-Gram branch diagnosis and exact repair argument

Root read the frozen Full118 diagnostic packetD3CA7B240129E13CDD653C8404B82C721A627E3954D46D23EC9CCE4920A6C323 and exact input sourceFF8981B60487A904F74F58903636FC7501E804247D5FDF45A8B9737F9246E06D. There is one actual source-error header at ExactRealRankGram:142:2. The stage aggregate's two error counts overlap this single unsolved-goal diagnostic; they are not two distinct source failures. Full118 remains failed.

The cross-rank theorem already rewrites the real inner product to the exact paired Fourier-coefficient sum. For each frequency Y, if rank(Y)=i then i!=j implies rank(Y)!=j, so the second filtered coefficient is zero and the summand is zero. If rank(Y)!=i, the first coefficient is zero. This proves the entire finite sum zero without a new hypothesis or altered theorem. In the positive branch the general simplifier rewrites the rank expression using hi, leaving a condition i=j that the provided hj no longer directly closes. The exact repair uses only if_pos hi, if_neg hj and mul_zero to evaluate the two original conditionals without that intermediate rewrite. All other proof bytes, ten public theorem headers, the rankGramEigenvalue definition and Checks remain unchanged. A disjoint successor must be verified on GCP with the same dependencies, axioms and frozen warning policy; the failed source and complete logs stay immutable.

Remaining to-do list: capture the one-line proof successor, complete Full118 shutdown/audit, restore unchanged admission capacity and run the next sole compiler lifecycle. Finish the numeric original-law/source-NO, common-floor, runtime, manuscript and certification obligations.
