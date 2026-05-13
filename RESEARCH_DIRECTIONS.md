# Research Directions and Strategic Assessment

Captured 2026-05-08 from a planning conversation. Audit numbers refreshed
2026-05-13. This document is a snapshot of where the project sits
academically/professionally and what the highest-leverage next moves look
like. Reread before deciding what to do with the artifact.

---

## Where the Project Stands Today

- **Coverage:** 65 textbook statements formalized.
- **Faithfulness audit (2026-05-13):** 17 `full` + 23 `library_wrapper` =
  **40 delivery-ready**; 25 `reduced_core`; 0 `placeholder`.
  - +6 delivery-ready since 2026-05-08 (BM square + Wald exponential
    promoted; A.7 bivariate Gaussian conditional now `full` with real
    derivation via orthogonal regression; plus earlier ce/ergodic
    promotions).
  - A.2 Doob L^p (`mart-thm-2.4.6`) sketch migrated to
    `lean/HybridVerify/DoobLp.lean`; 10 helper lemmas compile, main theorem
    still `sorry` (Fubini + Hölder + truncation + eLpNorm conversion,
    ~1-3 days of focused Lean engineering).
- **Backends:** Lean 4 (Mathlib master + Degenne `brownian-motion` vendored at
  pinned commit) + Isabelle/HOL (HOL-Probability + AFP `Markov_Models`,
  `Stochastic_Matrices`, `Ergodic_Theory`).
- **Distinguishing artifact:** the hybrid backend router + the explicit
  `reduced_core / library_wrapper / full` faithfulness taxonomy in
  `FORMALIZATION_STATUS.md`.

What the artifact is *not*: a full formal proof of the textbook. Itô formula,
Girsanov, Black-Scholes, SDE existence/uniqueness, reflection principle,
nowhere differentiability, and the Poisson-process construction all remain
`reduced_core` because the supporting Lean/Isabelle infrastructure does not
yet exist (or only partially exists in Degenne's library, which itself does
not yet ship Itô).

---

## Original Strategic Question

> *Release publicly? Publish a paper? Invite Saporito? Sell?*

### Initial recommendation, by audience

- **Lean/Mathlib core community:** values upstream contributions highly.
  Values external repos that wrap Mathlib lower unless they prove something
  new or demonstrate a novel methodology. Our 1-line wrappers don't carry
  standalone prestige; the audit framing is the closest thing to a novel
  contribution.
- **Formal-methods academic community (ITP, CPP, CADE, IJCAR):** active and
  growing. Three usual paper shapes: big single formalization (Liquid
  Tensor, PFR, Cap Set, Sphere Eversion); tool/infrastructure;
  methodology/case-study. Our project plausibly fits the third.
- **Mainstream math community:** roughly 50/50 curiosity vs. indifference.
  Stochastic processes specifically has very little formalized-math culture.
- **Quantitative finance community:** very low value. They want PnL, not
  proofs.
- **Education community:** slowly increasing value. A Saporito-textbook Lean
  companion that he himself uses for teaching could compound.

### Concrete value markers to calibrate against

- Mathlib PR merged ⇒ real career capital.
- ITP/CPP paper accepted ⇒ modest paper-level credit.
- Talk at Lean Together ⇒ community visibility, not citation-grade.
- AFP entry accepted ⇒ small but durable.
- Cited in a survey of formalized probability ⇒ rare, high if it happens.
- Adopted in a course or textbook ⇒ highest non-research outcome.

### Net read on the artifact in current shape

Roughly *one solid workshop paper plus a public GitHub repo* of community
value. To clear journal-paper bar: either Saporito-as-coauthor + a real
teaching-adoption story, or close the Itô/Girsanov gap (gated on the Lean
ecosystem, not on us).

The Saporito invite is the highest-EV move because it raises the ceiling on
every other path simultaneously.

---

## Pivot Directions for Higher Impact

### Option 1 — LLM-doing-formal-proofs

Crowded but has open lanes. AlphaProof, DeepSeek-Prover, Llemma, ReProver,
ProofBridge are well-funded. Won't win on compute. Possible angles:

- **Faithfulness-aware proof generation.** Every LLM prover today
  happily emits `:= sorry` or restates the goal as a structure projection
  and calls it done. Our `reduced_core / library_wrapper / full` audit is
  *exactly* the missing evaluation layer.
- **Hybrid-backend agent.** An LLM that picks Lean vs Isabelle vs SymPy
  per goal, using our router. No major project does this.
- **Domain you'd own.** Stochastic processes is under-served in LLM-prover
  benchmarks at the *graduate / textbook* level (competition-style
  probability is already in PutnamBench/FormalMATH).

### Option 2 — Probability/Stochastic-Processes Benchmark

Build *StochasticProcessBench*: 200-500 graduate-level theorems, tiered by
faithfulness, with hybrid-backend ground truth. Why this could work:
benchmarks compound, defensible moat (textbook-grounded + Saporito-validated),
solves a real gap above competition-probability.

**Caveat from web search:** competition-style probability is *already*
benchmarked (PutnamBench has probability problems; FormalMATH covers many
domains). The opening is narrower than originally pitched — graduate
stochastic processes specifically.

### Option 3 — Auto-formalization for Probability

Translate natural-language theorem statements → Lean. We already have
parallel corpus (textbook English ↔ formalized Lean) for 65 theorems.
Extending to the full textbook → 300+ pairs. Lower ceiling than benchmark
play, cheaper to ship.

### Option 4 — Push Itô/Girsanov Upstream

Genuine mathematical contribution. **Strongly affected by web search:**
Degenne, Ledvinka, Marion, and Pfaffelhuber published their Brownian motion
formalization paper Nov 25, 2025 (arXiv 2511.20118). Itô formula is "in
progress" per their blueprint. They presented at ItaLean 2025 in Bologna.
They are *the* center of gravity in this area. Realistic move: collaborate,
not compete.

### Option 5 — Quant-finance verification

Honest take: low ceiling. Crypto + F* worked because crypto matters
financially; stochastic finance hasn't shown the same demand pull.

### Option 6 — Teaching tool

Saporito-textbook-as-Lean-companion. Niche but durable. Education venues
exist. Modest ceiling but high adoption potential among students.

### Option 7 — Hybrid orchestration as research artifact

Frame the project as: "we evaluate when Lean vs Isabelle vs SymPy each suit
a domain, and how to route." **Affected by web search:** HybridProver,
Ax-Prover, Lean-Auto are playing in nearby spaces. Multi-tool orchestration
is an active research area. Our edge isn't the architecture — it's the
audit framework.

---

## Web-Verified Corrections to the Initial Recommendation

These claims I made were *wrong or stale* and changed the picture:

1. **AlphaProof status.** Silver at IMO 2024 was right, but
   **Gemini Deep Think hit gold at IMO 2025**. The frontier moved. Nature
   paper for AlphaProof methodology came out Nov 2025.

2. **"Probability under-served in benchmarks"** — partially wrong.
   PutnamBench explicitly covers probability (1724 problems total, 672 in
   Lean 4). FormalMATH has 5,560 problems across many domains. DeepSeek's
   ProverBench has 325. Competition-style probability IS covered.
   **Graduate stochastic processes is the genuinely uncovered slice.**

3. **"MiniF2F crowded but unsaturated"** — actually nearly **saturated**:
   HILBERT 99.2%, DeepSeek-Prover-V2 88.9%. The leaderboard isn't
   "crowded," it's *solved enough to retire*.

4. **"Hybrid Lean+Isabelle harness uncommon"** — overstated. HybridProver
   (May 2025), Ax-Prover (Oct 2025), Lean-Auto all play in nearby spaces.

5. **"RemyDegenne is doing Itô/Girsanov"** — *much further along than I
   implied.* Brownian motion formalization paper published Nov 25, 2025.
   Itô formula listed as "in progress." Degenne + Wenda Li are giving an
   ICML 2026 tutorial on "Proving Theorems with Lean and Machine Learning."

6. **Coq has a comprehensive stochastic-processes library** I didn't
   mention; stochastic-approximation theorem was formalized at ITP 2022.

### Claims that held up

- Mathlib upstream contributions are highest-prestige individual path.
- ITP/CPP/AITP are the right venues. ITP 2026 is Lisbon, July 26-29.
- Saporito-as-co-author angle valid.
- LLM proof is a crowded race you can't win on compute.
- FormalMATH found "even the strongest models achieve only 16.46% success
  rate under practical sampling budgets, exhibiting pronounced domain bias"
  — confirms the LLM provers have real domain weaknesses we could expose.

---

## Final Bet Ordering (Post-Verification)

The strongest now-defensible angle, given everything web search confirmed:

### 1. Faithfulness-aware re-evaluation of frontier LLM provers (NEW TOP OPTION)

Apply our `reduced_core / library_wrapper / full` taxonomy to the *outputs*
of frontier LLM provers (DeepSeek-Prover-V2, ReProver, Goedel-Prover) on
existing benchmarks (PutnamBench, FormalMATH, MiniF2F). The likely finding:
a meaningful fraction of "passes" are shallow under audit.

Why this is the strongest:
- **Genuinely novel.** Search found nobody publishing on the *quality*
  of an LLM prover's "successes" — only on pass rates.
- **FormalMATH already showed pass rates plateau at ~16%.** The "of those
  passes, how many are honest?" question is the obvious follow-up nobody
  has asked.
- **Small enough to ship solo** in a few months.
- **Positions the harness as the audit tool the field doesn't have.**
- **One paper, ITP/CPP-bar.**

### 2. Contribute Itô/Girsanov upstream as co-author with Degenne et al.

Realistic "real math" path. Email Degenne, contribute via PR to the
Brownian-motion library, end up on the Mathlib paper. Slower individual
prestige but actually plausible given current state.

### 3. Stochastic-processes-formalizability case study with Saporito

Narrower than ProbabilityBench. Frame as "what does/doesn't formalize
cleanly from a graduate textbook, audited honestly." The Degenne paper
makes this *more* viable, not less, because it gives primitives to build on.

### What I'd avoid

- Trying to "teach an LLM to do formal proofs" as a frontal assault
  without first building the benchmark/eval infrastructure.
- Original "ProbabilityBench" pitch as standalone — it's narrower than
  initially claimed because competition-probability is already covered.
- "Hybrid prover orchestration as paper" — the HybridProver / Ax-Prover /
  Lean-Auto ecosystem already covers most of the architectural angles.
- Quant-finance verification as a sales pitch.

---

## Concrete Next-Step Menu

If picking option (1) — faithfulness audit paper:

1. Pick 100-200 problems from PutnamBench-Lean and FormalMATH where
   frontier LLMs have published "solutions."
2. Pull the published proofs (DeepSeek-Prover-V2 GitHub, ReProver outputs,
   etc.) and apply our 3-tier classifier to each. Build a small classifier
   (rules-based + LLM-judge) operationalizing `reduced_core / wrapper / full`.
3. Report: pass-rate vs. *honest*-pass-rate. Highlight the gap.
4. Publish at ITP/CPP/AITP. Open-source the audit tool as the artifact.
5. Stretch goal: extend to a "proof-quality leaderboard" alongside MiniF2F.

If picking option (2) — Degenne contribution:

1. Email Degenne with this repo's URL + the FORMALIZATION_STATUS.md table.
2. Identify which gaps in `brownian-motion` we could close. BM-as-martingale
   (`brownianMotion_isMartingale`) and the `B² − t` / Wald exponential
   identities have since been promoted to `full` against current Mathlib +
   Degenne primitives, so the remaining candidates are: Itô isometry, the
   reflection principle, BM quadratic-variation refinements, and the SDE /
   Itô-formula stack (still `reduced_core` here, "in progress" per the
   Degenne blueprint).
3. Open PRs to `RemyDegenne/brownian-motion`.
4. Co-author position on whatever paper comes next.

If picking option (3) — Saporito case study:

1. Email Saporito with the URL + the artifact summary.
2. Frame as: "I built X. Want to co-author a case study on what does and
   doesn't currently formalize from your textbook?"
3. Publish in formal-methods education venue or Lean Together proceedings.

---

## Sources Verified

All checked May 2026:

- [AI achieves silver-medal standard solving IMO problems — DeepMind](https://deepmind.google/blog/ai-solves-imo-problems-at-silver-medal-level/)
- [Olympiad-level formal mathematical reasoning with reinforcement learning — Nature](https://www.nature.com/articles/s41586-025-09833-y)
- [Gemini with Deep Think achieves gold-medal at IMO — DeepMind](https://deepmind.google/blog/advanced-version-of-gemini-with-deep-think-officially-achieves-gold-medal-standard-at-the-international-mathematical-olympiad/)
- [DeepSeek-Prover-V2 paper](https://arxiv.org/abs/2504.21801)
- [DeepSeek-Prover-V2 GitHub](https://github.com/deepseek-ai/DeepSeek-Prover-V2)
- [PutnamBench paper](https://arxiv.org/pdf/2407.11214)
- [PutnamBench site](https://trishullab.github.io/PutnamBench/)
- [FormalMATH paper](https://arxiv.org/abs/2505.02735)
- [FormalMATH-Bench GitHub](https://github.com/Sphere-AI-Lab/FormalMATH-Bench)
- [Formalization of Brownian motion in Lean — Degenne et al.](https://arxiv.org/abs/2511.20118)
- [RemyDegenne/brownian-motion repo](https://github.com/RemyDegenne/brownian-motion)
- [Brownian motion blueprint](https://remydegenne.github.io/brownian-motion/blueprint/)
- [HybridProver paper](https://arxiv.org/pdf/2505.15740)
- [ProofBridge paper](https://arxiv.org/abs/2510.15681)
- [Markov kernels in Mathlib paper](https://arxiv.org/abs/2510.04070)
- [Basic probability in Mathlib — Lean community blog](https://leanprover-community.github.io/blog/posts/basic-probability-in-mathlib/)
- [ITP 2026 conference page](https://itp-conference-2026.github.io/index.html)
- [CPP — SIGPLAN](https://sigplan.org/Conferences/CPP/)
- [AITP 2025](https://aitp-conference.org/2025/)
