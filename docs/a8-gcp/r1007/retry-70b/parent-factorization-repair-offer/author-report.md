# Retry 70b ParentFactorization repair offer

Offer status: unaccepted source offer, awaiting Sol immutable-capture acknowledgment and GCP compilation. No local Lean/Lake/Elan execution or Git command was run. The original retry-68 files and retry-70b frozen inputs were not edited.

Source: `ActualBinaryMatrixHC46A22ParentFactorization.lean`  
Source SHA-256: `CF9A70F8A04F85C0BBFBE064F8CA8323FC4B4DC5D27BAC4BB444A70671FC6547`  
Checks: `ActualBinaryMatrixHC46A22ParentFactorizationChecks.lean`  
Checks SHA-256: `FF0B1F32E7581F0893A3D08DDEE8A0139AA59E45F12FF720B773E2915BFDB7D6`; byte-identical to retry-68: `True`  
Prior source SHA-256: `7D949C84D0C6278AC5A80C50E925E5B36FE6B5EFB80B116CF12AEFEE8C1557BE`  
Encoding: UTF-8 without BOM; LF line endings. All 42 U+21D2 occurrences in lambda bodies were replaced by ASCII `=>`; no U+21D2 remains.

Additional proof repairs, without declaration statement or premise changes:

- The quotient finrank equality in the containing-hyperplane branch is explicitly changed to the `F` alias before `omega`, aligning its atoms with the existing codimension equation.
- Replaced both unavailable `Submodule.ne_bot_iff.mp` uses with a private elementary witness lemma. It derives a nonzero member from `A ? ?` by contradiction and extensionality; it uses no caller-supplied witness or additional API assumption.

`source.diff` is the complete unified diff from the frozen retry-68 source. The 42 lambda-arrow changes occur at original source lines: 144, 195, 211, 243, 259, 287, 300, 316, 328, 330, 351, 385, 393, 408, 409, 439, 442, 449, 451, 479, 482, 489, 491, 516, 523, 562, 567, 576, 577, 587, 594, 595, 619, 627, 658, 665, 674, 676, 686, 692, 693, 718. The checks source is unchanged byte-for-byte. No declaration statements, premises, options, or heartbeats changed. No axiom or sorry was added. No mathematical acceptance is claimed.
