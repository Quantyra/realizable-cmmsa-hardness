# Checks for functional assignment acceptance

`Checks.lean` requests declarations for every public definition and theorem in the offer and asks Lean to print axioms for all four public theorems. The two assignment constructors make the distinction between the original-U input space and the visible-X-only input space explicit. The acceptance theorem assumes only H containment and the canonical RHS restriction; the actual tagged equation follows from the row indicator and H12 RHS functional. The restriction theorem states the forward and reverse assignment criterion.

Expected validation is a GCP Lean compile against the pinned Full114 closure, followed by Sol's axiom-profile and warning-baseline checks. No compile or native acceptance is claimed by this offer.