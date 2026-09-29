# Initial-vertex and clique-resampling joint-law gap

## Exact first missing comparison

`paper/body.tex:57` specifies the imported post-conditioning star test: uniform eligible copied `U`, transverse center `K`, independent ordered leaves, and uniform clique representatives. `ActualOriginalPostPaddingVerifier.originalLawFromTagged` formalizes that law independently of the tagged acceptance predicate. Its fixed legal-table score satisfies `originalScore_le_selected_add_collision`, with collision charge `(1/2)^J`.

The manuscript's earlier raw sampler is described at `paper/body.tex:793` only through an initial uniform vertex, uniform resampling within its equivalence class, the marginal assertion that each `U'_i` is uniform eligible, and an illegitimacy probability `a`. It does not give a joint kernel for the initial vertex, all resampled vertices, `K`, ordered leaves, and representatives, nor a map from that raw tuple to `OriginalDraw`. The projection argument at `body.tex:124-145` explicitly preserves the observed `D_i` and acceptance event while disclaiming identity of unobserved raw tuples.

The first force theorem would require a specified finite `rawLaw : FiniteLaw RawDraw`, legitimacy predicate `GoodRaw`, and `decode : {w : RawDraw // GoodRaw w} -> OriginalDraw`. For every allowed source instance, copy count, dimensions, and fixed legal predraw assignment `A`, it must prove both

```
pushforward decode (rawLaw conditioned on GoodRaw)
  = originalLawFromTagged I copies hcenter hleaf

rawAccepts A w <-> originalAccepts I copies A (decode w)
```

for every legitimate `w`. This implies equality of conditioned scores for every fixed `A`. If `a = rawLaw(not GoodRaw) < 1`, a raw failure event then has conditioned failure at most `rawFailure / (1-a)`. The available bound `a <= min(tau/100, 1/4)` gives `1/(1-a) <= 4/3`, and the manuscript conservatively charges a factor two in NO soundness. The raw-law definition, pushforward, and acceptance equivalence are absent; no numerical reduction of that remaining NO gap follows from this audit.

## Why the stated marginal is insufficient

The marginal statement at line 793 supports the honest-label union bound in equation (21), which only sums failure probabilities for the original and resampled blocks. It cannot transfer an arbitrary fixed-table acceptance conjunction. In a two-point toy class, let initial `V` be uniform on `{0,1}`. One kernel chooses `Y1,Y2` independently uniform in that class. Another chooses one uniform `Y` and sets `Y1=Y2=Y`. Both have uniform initial vertex and uniform individual resampled marginals. A fixed acceptance event `Y1=1 and Y2=1` has probability `1/4` under the first and `1/2` under the second. This is a counterexample to inference from the line-793 marginal alone, not a claim that the second kernel satisfies the independently sampled leaves of the post-conditioning contract at line 57. Even if independent clique representatives are read into that contract, the missing raw-to-conditioned coupling must still specify how the initial vertex, center, and leaves relate to those representatives.

Existing lemmas are downstream: `ActualTaggedOrderedQuestionSourceBridge.orderedGood_pushforward` starts from legitimate ordered rows, `ActualTaggedVertexPhysicalLaw.uniform_independentChoice_pushforward` starts from sampled independent presentations, and `ActualTaggedQuestionRetainedMass` handles illegitimate ordered-row mass. None establishes the raw initial-vertex joint pushforward or raw fixed-table event transport. A constant-cardinality vertex-to-`U` fiber would prove only a marginal and is not a substitute for the missing theorem.

No Lean assumption or standalone counting increment was introduced. The proved post-conditioning inequality remains `originalScore <= taggedSelectedMass + 2^-J`; extending it to the manuscript's raw initial-vertex sampler requires the joint-law theorem above.
