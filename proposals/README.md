# proposals/

draft files for upstream submission, not part of this project's verification surface.

- `bm-martingales/Martingale.lean` — two `IsFilteredPreBrownian` martingale identities for [`RemyDegenne/brownian-motion`](https://github.com/RemyDegenne/brownian-motion):
  - `IsFilteredPreBrownian.squareSubTime_isMartingale` (`t ↦ X_t² − t`)
  - `IsFilteredPreBrownian.waldExponential_isMartingale` (`t ↦ exp(α X_t − α² t / 2)` for any `α : ℝ`)
- `mathlib-gaussian-tail/RealTail.lean` — gaussian tail + completing-the-square lemmas targeting mathlib's `Mathlib.Probability.Distributions.Gaussian.Real`.

each builds clean against the same lean/mathlib/brownian-motion pins documented in the main project's `lean/lake-manifest.json`. neither is imported by anything in `lean/`. they live here so the actual code is reviewable before a pr is open.
