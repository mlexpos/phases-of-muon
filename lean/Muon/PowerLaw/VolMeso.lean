import Muon.PowerLaw.VolBulk
import Muon.PowerLaw.VolShell

set_option linter.style.longLine false

/-!
# Appendix G: mesoscopic volatility, part-form (work package L-G.8)

Snapshot `cr-2026-10-23`. Source: `sections/06-power-law/section.tex`: `lem:app-pl-vector` (l.1939–1946),
`lem:app-pl-strip` (l.2003–2007), `lem:app-pl-meso` (l.2029–2034), part (ii) of `thm:app-pl-volatility`
(l.911–940), and the volatility half for `0 < α ≤ 1` of `thm:app-pl-triple` (l.866–872), declared as
`triple_vol_le_one`. Card: `sections/06-power-law/CARD.md` §2, §3, §5 (L-G.8), §6 #1, #7.

Representation choices:

* Standing regime `assum_app_pl_regime` (`Muon.PowerLaw.Continuum`) for every statement, plus the source's
  `0 < α ≤ 1` (`hα1`). Spectrum `plSpec α (c n) (N n)`, `γ = gammaOf (N n) (B n)`.
* Rows. `i : ∀ n, Fin (N n)` is a row sequence. The source's 1-based row `i` is `rowIdx i = i + 1`, and
  `rowFrac i = (i+1)/N` is the source's `i/N`. "`i → ∞`" is `Tendsto (rowIdx ∘ i) atTop atTop`, and
  "`i/N → 0`" is `Tendsto (rowFrac ∘ i) atTop (𝓝 0)`. These are the hypotheses that the source writes as
  "let `i → ∞`" and "along every such row sequence" (l.1926–1927).
* Objects defined here (they are not in `VolKernel`): `bCoef` is `b_{i,N}` (`eqn:app-pl-b`), `calV` is
  `𝒱_i(g)`, `calVpart` is its restriction to `δ < m < M`, `vhatApprox` is `v̂_i` (`eqn:app-pl-approx-sub`, α ≤ 1).
  `𝒥_i` is not stated separately, since `W_i = 𝒥_i ϑ_N` is already `Wpart` of `VolKernel`.
  `l2Norm` is the `L²(gaussianReal 0 1)` norm. Its `Integrable` conjuncts make the norms finite (no junk value).
* `vPart` stands for `𝔳_i(0)` and `vIJ` for `𝔳_i[I,J]` (card §2 design). The identification with the limits
  `C̄_{i,ℓ}(0)`, `𝔳_i(0)` is `prop:app-pl-vol-zero`(iii) (L-G.13), not this file.
* Hypotheses. `volHBound` (`0 ≤ C̄_{i,ℓ}(0) ≤ 1`) and `volHPSD` are explicit hypotheses (card §5), discharged
  in L-G.13. `volHPSD` is the source's `lem:app-pl-pieces` (l.1843–1846): `0 ≤ 𝔳_i[I,J] ≤ (𝔳_i[I,I]𝔳_i[J,J])^{1/2}`
  for intervals `I, J ⊆ (0,γ)`, with `Set.OrdConnected` as the Mathlib notion of interval.
* Uniformity (card §6 #1). The source's "locally uniformly" in part (ii) is stated in the uniform form:
  for each compact `K ⊆ (0,∞)` and each `ε > 0` there is `M` such that, eventually in `n`, every row with
  `M ≤ i + 1` and `i/i_cv ∈ K` satisfies the bound. The `M ≤ i + 1` clause is the source's "`i → ∞`", and it
  is chosen before the sequence, as in `lem_app_pl_upper`. The remaining clauses of (ii) are sequential.
* Integrability and summability are conjuncts (`Integrable`, `IntegrableOn`, `Summable`), eventually in `n`,
  wherever the source says "finite" or writes a sum over lags. The ℓ-sum in `lem:app-pl-strip` is `tsum`
  only under its `Summable` conjunct.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Asymptotics

noncomputable section

namespace Muon.PowerLaw

/-! ## Row objects and the flat response -/

/-! ## Mesoscopic objects -/

/-- The 1-based row `i + 1` over `N`, scaled by `1/i_{c,𝔳}`: `icvRow β α B i = (i+1)/i_{c,𝔳}`
(`eqn:app-pl-icv`, `icvIdx`). -/
def icvRow (β α : ℝ) (B : ℕ) {N : ℕ} (i : Fin N) : ℝ := rowIdx i / icvIdx β α N B

/-- The approximant `v̂_i` of the source for `0 < α ≤ 1` (`eqn:app-pl-approx-sub`, second display).
Verbatim from the `Approximants` paragraph of `sections/06-power-law/section.tex`:

\paragraph{Approximants.}
The approximating coefficients are, for $0<\alpha\le1$,
\begin{equation}\label{eqn:app-pl-approx-sub}
\sqrt2\,\widehat{\mathfrak d}_i\defeq\sqrt{\frac{\mu_i}{\gamma\sw2}}+a_N\Psi_\alpha\Big(\frac iN\Big),\qquad
\widehat{\mathfrak v}_i\defeq\frac1{\sw2}+\frac{2c_0}{\sqrt{\sw2}}\sqrt{\gamma\Gamma_\alpha\Big(\frac iN\Big)}+\gamma\Gamma_\alpha\Big(\frac iN\Big),
\end{equation}
and, for $\alpha>1$,
\begin{equation}\label{eqn:app-pl-approx-super}
\sqrt2\,\widehat{\mathfrak d}_i\defeq b_N\,\Phi_{\alpha,\bmom}\Big(\Big(\frac{i_{\mathrm c}}{i}\Big)^\alpha\Big)\,
\frac{\Psi_\alpha(i/N)}{d_\alpha\sqrt{K_\alpha}\,(i/N)^{-(\alpha-1)/2}},\qquad
\widehat{\mathfrak v}_i\defeq G_{\alpha,\bmom}\Big(\frac{i}{i_{\mathrm c}}\Big)\,
\frac{\Gamma_\alpha(i/N)}{4K_\alpha^2(i/N)/(\alpha-1)} .
\end{equation}
-/
def vhatApprox (β α : ℝ) (B : ℕ) {N : ℕ} (i : Fin N) : ℝ :=
  1 / sPow β 2 + 2 * c0 / Real.sqrt (sPow β 2) * Real.sqrt (gammaOf N B * profGamma α (rowFrac i)) +
    gammaOf N B * profGamma α (rowFrac i)

/-- The region `{M < m₁, m₂ < ηγ, R⁻¹ ≤ m₁/m₂ ≤ R}` of `lem:app-pl-strip`, as a subset of `ℝ × ℝ`. -/
def stripSet (η Rr Mc γ : ℝ) : Set (ℝ × ℝ) :=
  {p | Mc < p.1 ∧ p.1 < η * γ ∧ Mc < p.2 ∧ p.2 < η * γ ∧ Rr⁻¹ ≤ p.1 / p.2 ∧ p.1 / p.2 ≤ Rr}

/-- Hypothesis `hBound` of the part-form volatility statements: `0 ≤ C̄_{i,ℓ}(0) ≤ 1` for every row and lag
(the source's l.2260; discharged in L-G.13). -/
def volHBound (α β : ℝ) (N B : ℕ → ℕ) (c : ℕ → ℝ) : Prop :=
  ∀ n (i : Fin (N n)) (ℓ : ℤ),
    0 ≤ CbarPart β (B n) (plSpec α (c n) (N n)) i ℓ ∧ CbarPart β (B n) (plSpec α (c n) (N n)) i ℓ ≤ 1

/-- Hypothesis `hPSD` of the part-form volatility statements: the conclusion of `lem:app-pl-pieces`
(`section.tex` l.1843–1846), `0 ≤ 𝔳_i[I,J] ≤ (𝔳_i[I,I] 𝔳_i[J,J])^{1/2}` for intervals `I, J ⊆ (0,γ)`
(discharged in L-G.13). -/
def volHPSD (α β : ℝ) (N B : ℕ → ℕ) (c : ℕ → ℝ) : Prop :=
  ∀ n (i : Fin (N n)) (I J : Set ℝ), I.OrdConnected → I ⊆ Ioo 0 (gammaOf (N n) (B n)) →
    J.OrdConnected → J ⊆ Ioo 0 (gammaOf (N n) (B n)) →
    0 ≤ vIJ β (B n) (plSpec α (c n) (N n)) i I J ∧
      vIJ β (B n) (plSpec α (c n) (N n)) i I J ≤
        Real.sqrt (vIJ β (B n) (plSpec α (c n) (N n)) i I I *
          vIJ β (B n) (plSpec α (c n) (N n)) i J J)

/-- Hypothesis `volHZero` of the part-form statements: `C̄_{i,0}(0) = 1`, the `ℓ = 0` term of
`vPart = 1 + 2 ∑_{ℓ≥1} C̄_{i,ℓ}(0)` (discharged in L-G.13 via `prop:app-pl-vol-zero`(i),(iii)). -/
def volHZero (α β : ℝ) (N B : ℕ → ℕ) (c : ℕ → ℝ) : Prop :=
  ∀ n (i : Fin (N n)), CbarPart β (B n) (plSpec α (c n) (N n)) i 0 = 1

/-! ## Statements -/

/-! ### Helpers for `lem_app_pl_vector` (L² bridge) -/

private lemma vm_memLp_of_sq {f : ℝ → ℝ} (hm : AEStronglyMeasurable f (gaussianReal 0 1))
    (hf : Integrable (fun g => f g ^ 2) (gaussianReal 0 1)) : MemLp f 2 (gaussianReal 0 1) := by
  rw [memLp_two_iff_integrable_sq hm]; exact hf

private lemma vm_l2Norm_eq {f : ℝ → ℝ} (hf : MemLp f 2 (gaussianReal 0 1)) :
    l2Norm f = (eLpNorm f 2 (gaussianReal 0 1)).toReal := by
  unfold l2Norm
  have h := hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  rw [h, ENNReal.toReal_ofReal (by positivity)]
  have : ∫ g, ‖f g‖ ^ (2:ℝ) ∂(gaussianReal 0 1) = ∫ g, f g ^ 2 ∂(gaussianReal 0 1) := by
    congr 1; ext g; rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  simp only [ENNReal.toReal_ofNat] at *
  rw [this, Real.sqrt_eq_rpow, one_div]

private lemma vm_l2Norm_add_le {f h : ℝ → ℝ} (hf : MemLp f 2 (gaussianReal 0 1))
    (hh : MemLp h 2 (gaussianReal 0 1)) :
    l2Norm (fun g => f g + h g) ≤ l2Norm f + l2Norm h := by
  have hs : MemLp (fun g => f g + h g) 2 (gaussianReal 0 1) := hf.add hh
  rw [vm_l2Norm_eq hs, vm_l2Norm_eq hf, vm_l2Norm_eq hh, ← ENNReal.toReal_add hf.eLpNorm_ne_top hh.eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hf.eLpNorm_ne_top, hh.eLpNorm_ne_top⟩) (eLpNorm_add_le (p := 2) (f := f) (g := h) (by norm_num))

private lemma vm_regime_comp {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    assum_app_pl_regime α β (N ∘ φ) (B ∘ φ) (c ∘ φ) where
  hα := R.hα
  hβ0 := R.hβ0
  hβ1 := R.hβ1
  hNpos n := R.hNpos (φ n)
  hBpos n := R.hBpos (φ n)
  hcpos n := R.hcpos (φ n)
  hN := R.hN.comp hφ.tendsto_atTop
  hB := R.hB.comp hφ.tendsto_atTop
  hγ := R.hγ.comp hφ.tendsto_atTop

private lemma vm_tendsto_zero_of_subseq (u : ℕ → ℝ)
    (h : ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (u ∘ φ ∘ ψ) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_contra hn
  push Not at hn
  have hfreq : ∃ᶠ n in atTop, ¬dist (u n) 0 < ε := by
    rw [frequently_atTop]
    intro N
    obtain ⟨n, hnN, hnε⟩ := hn N
    exact ⟨n, hnN, not_lt_of_ge hnε⟩
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨ψ, hψ, hlim⟩ := h φ hφ
  have hev := (Metric.tendsto_atTop.1 hlim) ε hε
  obtain ⟨n, hn⟩ := hev
  exact hbad (ψ n) (hn n le_rfl)

private lemma vm_eventually_bounded_or_subseq_atTop (u : ℕ → ℝ) :
    (∃ L : ℝ, ∀ᶠ n in atTop, u n ≤ L) ∨
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop atTop := by
  by_cases hb : ∃ L : ℝ, ∀ᶠ n in atTop, u n ≤ L
  · exact Or.inl hb
  · right
    have hfreq : ∀ k : ℕ, ∃ᶠ n in atTop, (k : ℝ) < u n := by
      intro k
      by_contra hk
      have hev : ∀ᶠ n in atTop, ¬(k : ℝ) < u n := not_frequently.1 hk
      apply hb
      exact ⟨k, hev.mono fun n hn => le_of_not_gt hn⟩
    obtain ⟨φ, hφ, hlarge⟩ := extraction_forall_of_frequently hfreq
    refine ⟨φ, hφ, ?_⟩
    exact tendsto_atTop_mono' atTop (Eventually.of_forall fun n => (hlarge n).le)
      tendsto_natCast_atTop_atTop

private lemma vm_unif_of_seq {ι : ℕ → Type} {cond : ∀ n, ι n → Prop} {F : ∀ n, ι n → ℝ}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ z : ∀ k, ι (φ k), (∀ k, cond (φ k) (z k)) →
      Tendsto (fun k => |F (φ k) (z k)|) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ i : ι n, cond n i → |F n i| ≤ ε := by
  intro ε hε
  by_contra hcon
  have hfreq : ∃ᶠ n in atTop, ∃ i : ι n, cond n i ∧ ε < |F n i| := by
    refine (Filter.not_eventually.1 hcon).mono ?_
    intro n hn
    push_neg at hn
    exact hn
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_of_frequently_atTop hfreq
  choose z hz1 hz2 using hφP
  have hT := h φ hφ z hz1
  have hev : ∀ᶠ k in atTop, |F (φ k) (z k)| < ε :=
    (Metric.tendsto_nhds.1 hT ε hε).mono (fun k hk => by simpa [abs_abs] using hk)
  obtain ⟨k, hk⟩ := hev.exists
  linarith [hz2 k]

private lemma vm_compact_uniform {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {ι : ℕ → Type} (K : Set X) (hK : IsCompact K) (u : ∀ n, ι n → X)
    (A : ∀ n, ι n → ℝ) (f : X → ℝ) (hf : ContinuousOn f K)
    (hseq : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ z : ∀ k, ι (φ k),
      (∀ k, u (φ k) (z k) ∈ K) → ∀ x ∈ K,
      Tendsto (fun k => u (φ k) (z k)) atTop (𝓝 x) →
      Tendsto (fun k => A (φ k) (z k)) atTop (𝓝 (f x))) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ z : ι n, u n z ∈ K → |A n z - f (u n z)| ≤ ε := by
  intro ε hε
  by_contra hcon
  have hfreq : ∃ᶠ n in atTop, ∃ z : ι n, u n z ∈ K ∧ ε < |A n z - f (u n z)| := by
    refine (Filter.not_eventually.1 hcon).mono ?_
    intro n hn
    push Not at hn
    exact hn
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_of_frequently_atTop hfreq
  choose z hzK hzerr using hφP
  obtain ⟨x, hxK, ψ, hψ, hψx⟩ := hK.tendsto_subseq hzK
  have hlim := hseq (φ ∘ ψ) (hφ.comp hψ) (fun k => z (ψ k))
    (fun k => hzK (ψ k)) x hxK hψx
  have hprof : Tendsto (fun k => f (u (φ (ψ k)) (z (ψ k)))) atTop (𝓝 (f x)) :=
    (hf x hxK).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hψx, Filter.Eventually.of_forall (fun k => hzK (ψ k))⟩)
  have herr : Tendsto (fun k => |A (φ (ψ k)) (z (ψ k)) -
      f (u (φ (ψ k)) (z (ψ k)))|) atTop (𝓝 0) := by
    simpa using (hlim.sub hprof).abs
  have hev : ∀ᶠ k in atTop, |A (φ (ψ k)) (z (ψ k)) -
      f (u (φ (ψ k)) (z (ψ k)))| < ε :=
    (Metric.tendsto_nhds.1 herr ε hε).mono (fun k hk => by simpa [abs_abs] using hk)
  obtain ⟨k, hk⟩ := hev.exists
  exact (not_lt_of_ge hk.le) (hzerr (ψ k))

private lemma vm_Zg_sq {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (q : ℝ) :
    Integrable (fun g : ℝ => Zg β g q ^ 2) (gaussianReal 0 1) ∧
      ∫ g : ℝ, Zg β g q ^ 2 ∂(gaussianReal 0 1) ≤ (Real.sqrt q) ^ 2 := by
  rcases lt_or_ge 0 q with hq | hq
  · obtain ⟨h1, h2⟩ := (lem_app_pl_age_i hβ0 hβ1).2 q hq
    refine ⟨h1, ?_⟩
    rwa [Real.sq_sqrt hq.le]
  · have hz : ∀ g, Zg β g q = 0 := fun g => by
      unfold Zg; rw [Real.sqrt_eq_zero_of_nonpos hq, zero_mul]
    simp [hz]

private lemma vm_mink {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (W Q : ℝ → ℝ) (γ : ℝ)
    (hI : IntegrableOn (fun m => |W m| * Real.sqrt (Q m)) (Ioo 0 γ))
    (hF : AEStronglyMeasurable (fun q : ℝ × ℝ => W q.1 * Zg β q.2 (Q q.1))
      ((volume.restrict (Ioo 0 γ)).prod (gaussianReal 0 1))) :
    (∀ᵐ g ∂(gaussianReal 0 1), IntegrableOn (fun m => W m * Zg β g (Q m)) (Ioo 0 γ)) ∧
    Integrable (fun g => (∫ m in Ioo 0 γ, W m * Zg β g (Q m)) ^ 2) (gaussianReal 0 1) := by
  have hbound : ∀ m, l2Norm (fun g => W m * Zg β g (Q m)) ≤ |W m| * Real.sqrt (Q m) := by
    intro m
    unfold l2Norm
    have h1 : ∫ g, (W m * Zg β g (Q m)) ^ 2 ∂(gaussianReal 0 1) =
        W m ^ 2 * ∫ g, Zg β g (Q m) ^ 2 ∂(gaussianReal 0 1) := by
      simp_rw [mul_pow]; exact integral_const_mul _ _
    rw [h1]
    calc _ ≤ Real.sqrt (W m ^ 2 * (Real.sqrt (Q m)) ^ 2) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (vm_Zg_sq hβ0 hβ1 (Q m)).2 (sq_nonneg _))
      _ = |W m| * Real.sqrt (Q m) := by
          rw [← mul_pow, Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hmeas : AEStronglyMeasurable (fun m => l2Norm (fun g => W m * Zg β g (Q m)))
      (volume.restrict (Ioo 0 γ)) := by
    have h := (hF.mul hF).integral_prod_right'
    have h2 := Real.continuous_sqrt.comp_aestronglyMeasurable h
    refine h2.congr (Eventually.of_forall fun m => ?_)
    simp only [l2Norm, sq, Pi.mul_apply]
  have hint : IntegrableOn (fun m => l2Norm (fun g => W m * Zg β g (Q m))) (Ioo 0 γ) := by
    refine Integrable.mono' hI hmeas (Eventually.of_forall fun m => ?_)
    rw [Real.norm_of_nonneg (by unfold l2Norm; exact Real.sqrt_nonneg _)]
    exact hbound m
  have hsq : ∀ᵐ m ∂(volume.restrict (Ioo 0 γ)),
      Integrable (fun g => (W m * Zg β g (Q m)) ^ 2) (gaussianReal 0 1) :=
    Eventually.of_forall fun m => by
      simp_rw [mul_pow]; exact (vm_Zg_sq hβ0 hβ1 (Q m)).1.const_mul _
  obtain ⟨h1, h2, -⟩ := l2_minkowski_integral (Ioo 0 γ) measurableSet_Ioo
    (fun m g => W m * Zg β g (Q m)) hF hsq hint
  exact ⟨h1, h2⟩

private lemma vm_sign_meas : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
      measurable_const)

private lemma vm_part_meas (F : ℝ → ℝ → ℝ) (γ : ℝ) {S : Set ℝ} (hS : S ⊆ Ioo 0 γ)
    (hF : AEStronglyMeasurable (fun q : ℝ × ℝ => F q.1 q.2)
      ((volume.restrict (Ioo 0 γ)).prod (gaussianReal 0 1))) :
    AEStronglyMeasurable (fun g => ∫ m in S, F m g) (gaussianReal 0 1) := by
  have hle : (volume.restrict S) ≪ volume.restrict (Ioo 0 γ) :=
    (Measure.restrict_mono hS le_rfl).absolutelyContinuous
  have hF' : AEStronglyMeasurable (fun q : ℝ × ℝ => F q.1 q.2)
      ((volume.restrict S).prod (gaussianReal 0 1)) :=
    hF.mono_ac (hle.prod (Measure.AbsolutelyContinuous.refl _))
  exact hF'.prod_swap.integral_prod_right'

private lemma vm_split_integral (F : ℝ → ℝ → ℝ) {γ M : ℝ} (hM0 : 0 < M) (hMγ : M < γ) (g : ℝ)
    (hg : IntegrableOn (fun m => F m g) (Ioo 0 γ)) :
    ∫ m in Ioo 0 γ, F m g = (∫ m in Ioo 0 M, F m g) + ∫ m in Ioo M γ, F m g := by
  have h1 : IntegrableOn (fun m => F m g) (Ioc 0 M) :=
    ((integrableOn_Ioc_iff_integrableOn_Ioo enorm_ne_top).2 (hg.mono_set (Ioo_subset_Ioo le_rfl hMγ.le)))
  have h2 : IntegrableOn (fun m => F m g) (Ioc M γ) :=
    ((integrableOn_Ioc_iff_integrableOn_Ioo enorm_ne_top).2 (hg.mono_set (Ioo_subset_Ioo hM0.le le_rfl)))
  have := intervalIntegral.integral_add_adjacent_intervals
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hM0.le).2 h1)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hMγ.le).2 h2)
  rw [intervalIntegral.integral_of_le hM0.le, intervalIntegral.integral_of_le hMγ.le,
    intervalIntegral.integral_of_le (hM0.trans hMγ).le] at this
  rw [integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at this
  exact this.symm

private lemma vm_sign_sq_le (g : ℝ) : Real.sign g ^ 2 ≤ 1 := by
  rcases Real.sign_apply_eq g with h | h | h <;> simp [h]

private lemma vm_l2Norm_congr {f h : ℝ → ℝ} (hfh : f =ᵐ[gaussianReal 0 1] h) : l2Norm f = l2Norm h := by
  unfold l2Norm
  congr 1
  exact integral_congr_ae (hfh.mono fun g hg => by simp [hg])

private lemma vm_decomp (F : ℝ → ℝ → ℝ) (γ M s b tm : ℝ) (hM0 : 0 < M) (hMγ : M < γ)
    (hF : AEStronglyMeasurable (fun q : ℝ × ℝ => F q.1 q.2)
      ((volume.restrict (Ioo 0 γ)).prod (gaussianReal 0 1)))
    (hae : ∀ᵐ g ∂(gaussianReal 0 1), IntegrableOn (fun m => F m g) (Ioo 0 γ))
    (hH : Integrable (fun g => (Real.pi⁻¹ * (∫ m in Ioo 0 M, F m g) - g / s) ^ 2) (gaussianReal 0 1))
    (hT : Integrable (fun g => (Real.pi⁻¹ * (∫ m in Ioo M γ, F m g) - tm * Real.sign g) ^ 2)
      (gaussianReal 0 1)) :
    l2Norm (fun g => Real.pi⁻¹ * (∫ m in Ioo 0 γ, F m g) - (g / s + b * Real.sign g)) ≤
      l2Norm (fun g => Real.pi⁻¹ * (∫ m in Ioo 0 M, F m g) - g / s) +
      l2Norm (fun g => Real.pi⁻¹ * (∫ m in Ioo M γ, F m g) - tm * Real.sign g) + |tm - b| := by
  have hHm : AEStronglyMeasurable (fun g => Real.pi⁻¹ * (∫ m in Ioo 0 M, F m g) - g / s)
      (gaussianReal 0 1) :=
    ((vm_part_meas F γ (Ioo_subset_Ioo le_rfl hMγ.le) hF).const_mul _).sub
      (measurable_id.div_const s).aestronglyMeasurable
  have hTm : AEStronglyMeasurable (fun g => Real.pi⁻¹ * (∫ m in Ioo M γ, F m g) - tm * Real.sign g)
      (gaussianReal 0 1) :=
    ((vm_part_meas F γ (Ioo_subset_Ioo hM0.le le_rfl) hF).const_mul _).sub
      ((vm_sign_meas.const_mul tm).aestronglyMeasurable)
  have h1 := vm_memLp_of_sq hHm hH
  have h2 := vm_memLp_of_sq hTm hT
  have h3 : MemLp (fun g => (tm - b) * Real.sign g) 2 (gaussianReal 0 1) := by
    refine vm_memLp_of_sq ((vm_sign_meas.const_mul _).aestronglyMeasurable) ?_
    refine Integrable.mono' (integrable_const ((tm - b) ^ 2))
      ((vm_sign_meas.const_mul _).pow_const 2).aestronglyMeasurable (Eventually.of_forall fun g => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), mul_pow]
    nlinarith [vm_sign_sq_le g, sq_nonneg (tm - b)]
  have h3n : l2Norm (fun g => (tm - b) * Real.sign g) ≤ |tm - b| := by
    unfold l2Norm
    have hi := h3.integrable_sq
    calc Real.sqrt (∫ g, ((tm - b) * Real.sign g) ^ 2 ∂(gaussianReal 0 1))
        ≤ Real.sqrt ((tm - b) ^ 2) := by
          refine Real.sqrt_le_sqrt ?_
          have := integral_mono hi (integrable_const ((tm - b) ^ 2)) (fun g => by
            simp only [mul_pow]
            nlinarith [vm_sign_sq_le g, sq_nonneg (tm - b)])
          simpa using this
      _ = |tm - b| := Real.sqrt_sq_eq_abs _
  have hae2 : (fun g => Real.pi⁻¹ * (∫ m in Ioo 0 γ, F m g) - (g / s + b * Real.sign g)) =ᵐ[gaussianReal 0 1]
      (fun g => ((Real.pi⁻¹ * (∫ m in Ioo 0 M, F m g) - g / s) +
        (Real.pi⁻¹ * (∫ m in Ioo M γ, F m g) - tm * Real.sign g)) + (tm - b) * Real.sign g) := by
    filter_upwards [hae] with g hg
    rw [vm_split_integral F hM0 hMγ g hg]
    ring
  rw [vm_l2Norm_congr hae2]
  calc _ ≤ l2Norm (fun g => (Real.pi⁻¹ * (∫ m in Ioo 0 M, F m g) - g / s) +
        (Real.pi⁻¹ * (∫ m in Ioo M γ, F m g) - tm * Real.sign g)) +
        l2Norm (fun g => (tm - b) * Real.sign g) := vm_l2Norm_add_le (h1.add h2) h3
    _ ≤ _ := by
        have := vm_l2Norm_add_le h1 h2
        linarith

private lemma vm_memLp_gdiv (s : ℝ) : MemLp (fun g : ℝ => g / s) 2 (gaussianReal 0 1) := by
  have h : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1) := memLp_id_gaussianReal 2
  simpa [div_eq_inv_mul] using h.const_mul (s⁻¹)

private lemma vm_l2Norm_sub_le {f h : ℝ → ℝ} (hf : MemLp f 2 (gaussianReal 0 1))
    (hh : MemLp h 2 (gaussianReal 0 1)) :
    l2Norm (fun g => f g - h g) ≤ l2Norm f + l2Norm h := by
  have := vm_l2Norm_add_le hf hh.neg
  have e : l2Norm (-h) = l2Norm h := by
    unfold l2Norm; simp
  simpa [sub_eq_add_neg, e] using this

private lemma vm_head_facts (F : ℝ → ℝ → ℝ) (γ M s : ℝ) (hMγ : M ≤ γ)
    (hF : AEStronglyMeasurable (fun q : ℝ × ℝ => F q.1 q.2)
      ((volume.restrict (Ioo 0 γ)).prod (gaussianReal 0 1)))
    (hH : Integrable (fun g => (Real.pi⁻¹ * (∫ m in Ioo 0 M, F m g)) ^ 2) (gaussianReal 0 1)) :
    Integrable (fun g => (Real.pi⁻¹ * (∫ m in Ioo 0 M, F m g) - g / s) ^ 2) (gaussianReal 0 1) ∧
    l2Norm (fun g => Real.pi⁻¹ * (∫ m in Ioo 0 M, F m g) - g / s) ≤
      l2Norm (fun g => Real.pi⁻¹ * (∫ m in Ioo 0 M, F m g)) + l2Norm (fun g => g / s) := by
  have hHm : AEStronglyMeasurable (fun g => Real.pi⁻¹ * (∫ m in Ioo 0 M, F m g)) (gaussianReal 0 1) :=
    (vm_part_meas F γ (Ioo_subset_Ioo le_rfl hMγ) hF).const_mul _
  have h1 := vm_memLp_of_sq hHm hH
  exact ⟨(h1.sub (vm_memLp_gdiv s)).integrable_sq, vm_l2Norm_sub_le h1 (vm_memLp_gdiv s)⟩

private lemma vm_tendsto_zero_of_le {X : ℕ → ℝ} (h0 : ∀ n, 0 ≤ X n)
    (h : ∀ ε > 0, ∀ᶠ n in atTop, X n ≤ ε) : Tendsto X atTop (𝓝 0) := by
  rw [tendsto_order]
  exact ⟨fun a ha => Eventually.of_forall fun n => lt_of_lt_of_le ha (h0 n),
    fun a ha => (h (a / 2) (by linarith)).mono fun n hn => by linarith⟩

private lemma vm_rowFrac_bounds' {N : ℕ} (i : Fin N) : 0 < rowFrac i ∧ rowFrac i ≤ 1 := by
  have hN : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hi : (0:ℝ) < rowIdx i := by unfold rowIdx; positivity
  refine ⟨by unfold rowFrac; positivity, ?_⟩
  unfold rowFrac
  rw [div_le_one hNr]
  unfold rowIdx
  have : (i : ℕ) + 1 ≤ N := i.isLt
  exact_mod_cast this

private lemma vm_bCoef_nonneg' {α : ℝ} (hα : 0 < α) {N B : ℕ} (i : Fin N) :
    0 ≤ bCoef α B i := by
  have hx := vm_rowFrac_bounds' i
  have hPsi := lem_app_pl_Psi_i_pos hα (rowFrac i) hx
  have hc0 : 0 < c0 := by unfold c0; exact Real.sqrt_pos.2 (by positivity)
  unfold bCoef
  exact div_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hx.1.le _))
    hPsi.le) hc0.le

private lemma vm_vector_main {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) :
    (∀ᶠ n in atTop,
        Integrable (fun g => calV β (B n) (plSpec α (c n) (N n)) (i n) g ^ 2) (gaussianReal 0 1)) ∧
    Tendsto (fun n => l2Norm (fun g =>
        calV β (B n) (plSpec α (c n) (N n)) (i n) g -
          (g / Real.sqrt (sPow β 2) + bCoef α (B n) (i n) * Real.sign g)) /
          (1 + bCoef α (B n) (i n)))
      atTop (𝓝 0) ∧
    ∀ δ M : ℝ, 0 < δ → δ < M →
      (∀ᶠ n in atTop,
        Integrable (fun g => calVpart β (B n) (plSpec α (c n) (N n)) (i n) δ M g ^ 2)
          (gaussianReal 0 1)) ∧
      Tendsto (fun n => l2Norm (fun g => calVpart β (B n) (plSpec α (c n) (N n)) (i n) δ M g) /
        (1 + bCoef α (B n) (i n))) atTop (𝓝 0) := by
  have hβ0 := R.hβ0
  have hβ1 := R.hβ1
  have hb0 : ∀ n, 0 ≤ bCoef α (B n) (i n) := fun n => vm_bCoef_nonneg' R.hα (i n)
  have hpos : ∀ n, 0 < 1 + bCoef α (B n) (i n) := fun n => by linarith [hb0 n]
  have hWi := Wpart_integrable_measurable R
  have hmink : ∀ᶠ n in atTop,
      (∀ᵐ g ∂(gaussianReal 0 1), IntegrableOn (fun m => Wpart β (B n) (plSpec α (c n) (N n)) (i n) m *
        Zg β g (Qm β m)) (Ioo 0 (gammaOf (N n) (B n)))) ∧
      Integrable (fun g => calV β (B n) (plSpec α (c n) (N n)) (i n) g ^ 2) (gaussianReal 0 1) := by
    filter_upwards [hWi] with n hn
    obtain ⟨hI, -, hF⟩ := hn (i n)
    obtain ⟨h1, h2⟩ := vm_mink hβ0 hβ1 _ (Qm β) _ hI hF
    refine ⟨h1, ?_⟩
    have := h2.const_mul (Real.pi⁻¹ ^ 2)
    refine this.congr (Eventually.of_forall fun g => ?_)
    simp only [calV, mul_pow]
  refine ⟨hmink.mono fun n h => h.2, ?_, ?_⟩
  · obtain ⟨Ct, M₀, hM₀, hT⟩ := tail_L2_averaging (α := α) (β := β)
    set ς : ℝ := Real.sqrt (sPow β 2) with hς
    set Kg : ℝ := l2Norm (fun g : ℝ => g / ς) with hKg
    have hhead_ev : ∀ M : ℝ, 0 < M → ∃ Ch : ℝ, ∀ᶠ n in atTop,
        Integrable (fun g => (calVpart β (B n) (plSpec α (c n) (N n)) (i n) 0 M g - g / ς) ^ 2)
          (gaussianReal 0 1) ∧
        l2Norm (fun g => calVpart β (B n) (plSpec α (c n) (N n)) (i n) 0 M g - g / ς) ≤ Ch + Kg := by
      intro M hM
      obtain ⟨Ch, hCh⟩ := head_norm_bound (α := α) (β := β) M hM
      refine ⟨Ch, ?_⟩
      filter_upwards [hCh N B c R, hWi, R.hγ.eventually_gt_atTop M] with n h1 h2 h3
      obtain ⟨-, -, hF⟩ := h2 (i n)
      obtain ⟨hint, hnorm⟩ := h1 (i n)
      obtain ⟨f1, f2⟩ := vm_head_facts
        (fun m g => Wpart β (B n) (plSpec α (c n) (N n)) (i n) m * Zg β g (Qm β m))
        (gammaOf (N n) (B n)) M ς h3.le hF hint
      exact ⟨f1, f2.trans (add_le_add hnorm le_rfl)⟩
    have hhead : ∀ M : ℝ, 0 < M → Tendsto (fun n => l2Norm (fun g =>
        calVpart β (B n) (plSpec α (c n) (N n)) (i n) 0 M g - g / ς) /
          (1 + bCoef α (B n) (i n))) atTop (𝓝 0) := by
      intro M hM
      obtain ⟨Ch, hCh⟩ := hhead_ev M hM
      refine vm_tendsto_zero_of_subseq _ ?_
      intro φ hφ
      rcases vm_eventually_bounded_or_subseq_atTop (fun n => bCoef α (B (φ n)) (i (φ n))) with
        ⟨L, hL⟩ | ⟨ψ, hψ, hψt⟩
      · refine ⟨id, strictMono_id, ?_⟩
        have R' := vm_regime_comp R hφ
        have hi' : Tendsto (fun k => rowIdx (i (φ k))) atTop atTop := hi.comp hφ.tendsto_atTop
        have hx' : Tendsto (fun k => rowFrac (i (φ k))) atTop (𝓝 0) := hx.comp hφ.tendsto_atTop
        have ha := aRow_tendsto_zero_of_b_bounded R' hα1 (fun k => i (φ k)) hi' hx' L hL
        obtain ⟨-, hlim⟩ := head_limit R' (fun k => i (φ k)) hi' ha M hM
        refine squeeze_zero (fun k => div_nonneg (Real.sqrt_nonneg _) (hpos (φ k)).le)
          (fun k => ?_) hlim
        exact div_le_self (Real.sqrt_nonneg _) (by have := hb0 (φ k); show 1 ≤ 1 + bCoef α (B (φ k)) (i (φ k)); linarith)
      · refine ⟨ψ, hψ, ?_⟩
        have hten : Tendsto (fun k => (Ch + Kg) / (1 + bCoef α (B (φ (ψ k))) (i (φ (ψ k)))))
            atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ 1 hψt)
        refine squeeze_zero' (Eventually.of_forall fun k =>
          div_nonneg (Real.sqrt_nonneg _) (hpos (φ (ψ k))).le) ?_ hten
        have hcomp : Tendsto (fun k => φ (ψ k)) atTop atTop :=
          hφ.tendsto_atTop.comp hψ.tendsto_atTop
        filter_upwards [hcomp.eventually hCh] with k hk
        exact div_le_div_of_nonneg_right hk.2 (hpos (φ (ψ k))).le
    refine vm_tendsto_zero_of_le (fun n => div_nonneg (Real.sqrt_nonneg _) (by linarith [hb0 n])) ?_
    intro η hη
    set ε : ℝ := η / 12 with hε
    have hε0 : 0 < ε := by positivity
    set M : ℝ := max (max M₀ 1) (|Ct| / ε + 1) with hMdef
    have hMM₀ : M₀ ≤ M := (le_max_left _ _).trans (le_max_left _ _)
    have hM0 : 0 < M := lt_of_lt_of_le hM₀ hMM₀
    have hCM : |Ct| / ε < M := by
      have : |Ct| / ε + 1 ≤ M := le_max_right _ _
      linarith
    have habs : |Ct / M| ≤ ε := by
      rw [abs_div, abs_of_pos hM0, div_le_iff₀ hM0]
      have := (div_lt_iff₀ hε0).1 hCM
      linarith
    have hκ0 : 0 ≤ Ct / M + ε := by linarith [(abs_le.1 habs).1]
    have hκ2 : Ct / M + ε ≤ 2 * ε := by linarith [(abs_le.1 habs).2]
    obtain ⟨Ch, hCh⟩ := hhead_ev M hM0
    have e1 := hT N B c R M hMM₀ ε hε0
    have e6 := (Metric.tendsto_nhds.1 (tailMass_sub_b R hα1 i hi hx M hM0
      (by rw [hMdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)))) (min 1 (η / 3))
      (lt_min one_pos (by positivity))
    have e7 := (Metric.tendsto_nhds.1 (hhead M hM0)) (η / 3) (by positivity)
    filter_upwards [e1, hWi, hmink, hCh, e6, e7, R.hγ.eventually_gt_atTop M] with n h1 h2 h3 h4 h6 h7 h8
    obtain ⟨-, hTint, hTnorm⟩ := h1 (i n)
    obtain ⟨-, -, hF⟩ := h2 (i n)
    obtain ⟨hae, -⟩ := h3
    obtain ⟨hHint, -⟩ := h4
    have dec := vm_decomp
      (fun m g => Wpart β (B n) (plSpec α (c n) (N n)) (i n) m * Zg β g (Qm β m))
      (gammaOf (N n) (B n)) M ς (bCoef α (B n) (i n))
      (tailMass (B n) (plSpec α (c n) (N n)) (i n) M) hM0 h8 hF hae hHint hTint
    have hb1 := hb0 n
    set bb : ℝ := 1 + bCoef α (B n) (i n) with hbb
    have hbb0 : 0 < bb := by linarith
    set tm : ℝ := tailMass (B n) (plSpec α (c n) (N n)) (i n) M with htm
    set nA := l2Norm (fun g => calVpart β (B n) (plSpec α (c n) (N n)) (i n) 0 M g - g / ς) with hnA
    set nT := l2Norm (fun g => calVpart β (B n) (plSpec α (c n) (N n)) (i n) M (gammaOf (N n) (B n)) g -
      tm * Real.sign g) with hnT
    rw [Real.dist_eq, sub_zero] at h6 h7
    have hd : |tm - bCoef α (B n) (i n)| / bb < min 1 (η / 3) := by
      rwa [abs_div, abs_of_pos hbb0] at h6
    have hd1 : |tm - bCoef α (B n) (i n)| < bb := by
      have := lt_of_lt_of_le hd (min_le_left _ _)
      rwa [div_lt_one hbb0] at this
    have hd2 : |tm - bCoef α (B n) (i n)| / bb < η / 3 := lt_of_lt_of_le hd (min_le_right _ _)
    have hA : nA / bb < η / 3 := by
      have hnA0 : 0 ≤ nA := Real.sqrt_nonneg _
      rwa [abs_of_nonneg (div_nonneg hnA0 hbb0.le)] at h7
    have htm : tm ≤ 2 * bb := by
      have := (abs_lt.1 hd1).2
      linarith
    have hnT2 : nT / bb ≤ 2 * (Ct / M + ε) := by
      rw [div_le_iff₀ hbb0]
      calc nT ≤ (Ct / M + ε) * tm := hTnorm
        _ ≤ (Ct / M + ε) * (2 * bb) := mul_le_mul_of_nonneg_left htm hκ0
        _ = 2 * (Ct / M + ε) * bb := by ring
    calc _ ≤ (nA + nT + |tm - bCoef α (B n) (i n)|) / bb := div_le_div_of_nonneg_right dec hbb0.le
      _ = nA / bb + nT / bb + |tm - bCoef α (B n) (i n)| / bb := by ring
      _ ≤ η := by
        have : 2 * (Ct / M + ε) ≤ η / 3 := by rw [hε] at hκ2 ⊢; linarith
        linarith
  · intro δ M hδ hδM
    obtain ⟨Cm, hCm⟩ := middle_norm_bound (α := α) (β := β) δ M hδ hδM
    have hev := hCm N B c R
    refine ⟨hev.mono fun n h => (h (i n)).1, ?_⟩
    refine vm_tendsto_zero_of_le (fun n => div_nonneg (Real.sqrt_nonneg _) (by linarith [hb0 n])) ?_
    intro ε hε
    set K : ℝ := |Cm| with hK
    have hK0 : 0 ≤ K := abs_nonneg _
    set θ : ℝ := (ε / (K + 1)) ^ 2 with hθ
    have hθ0 : 0 < θ := by positivity
    have hsθ : Real.sqrt θ = ε / (K + 1) := by
      rw [hθ, Real.sqrt_sq (by positivity)]
    have hbl := b_large_of_y_compact R hα1 i hi hx (y₀ := θ) (y₁ := θ⁻¹) hθ0 (K / ε)
    filter_upwards [hev, hbl] with n hn hbn
    set y : ℝ := plSpec α (c n) (N n) (i n) * partLam (B n) (plSpec α (c n) (N n)) 1 with hy
    obtain ⟨-, hnorm⟩ := hn (i n)
    have hn0 : 0 ≤ l2Norm (fun g => calVpart β (B n) (plSpec α (c n) (N n)) (i n) δ M g) :=
      Real.sqrt_nonneg _
    have hb1 : 0 ≤ bCoef α (B n) (i n) := hb0 n
    have hmin_nonneg : 0 ≤ min (Real.sqrt y) (Real.sqrt y)⁻¹ :=
      le_min (Real.sqrt_nonneg _) (inv_nonneg.2 (Real.sqrt_nonneg _))
    have hnorm' : l2Norm (fun g => calVpart β (B n) (plSpec α (c n) (N n)) (i n) δ M g) ≤
        K * min (Real.sqrt y) (Real.sqrt y)⁻¹ :=
      hnorm.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hmin_nonneg)
    have hKε : K * (ε / (K + 1)) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
      nlinarith
    have hdiv : l2Norm (fun g => calVpart β (B n) (plSpec α (c n) (N n)) (i n) δ M g) /
        (1 + bCoef α (B n) (i n)) ≤ l2Norm (fun g => calVpart β (B n) (plSpec α (c n) (N n)) (i n) δ M g) :=
      div_le_self hn0 (by linarith)
    by_cases h1 : y ≤ θ
    · have : min (Real.sqrt y) (Real.sqrt y)⁻¹ ≤ Real.sqrt θ :=
        (min_le_left _ _).trans (Real.sqrt_le_sqrt h1)
      rw [hsθ] at this
      calc _ ≤ _ := hdiv
        _ ≤ _ := hnorm'
        _ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left this hK0
        _ ≤ ε := hKε
    · by_cases h2 : θ⁻¹ ≤ y
      · have hs : (Real.sqrt θ)⁻¹ ≤ Real.sqrt y := by
          rw [← Real.sqrt_inv]; exact Real.sqrt_le_sqrt h2
        have hspos : 0 < Real.sqrt θ := Real.sqrt_pos.2 hθ0
        have : (Real.sqrt y)⁻¹ ≤ Real.sqrt θ := by
          have := inv_anti₀ (inv_pos.2 hspos) hs
          simpa using this
        have h3 : min (Real.sqrt y) (Real.sqrt y)⁻¹ ≤ Real.sqrt θ := (min_le_right _ _).trans this
        rw [hsθ] at h3
        calc _ ≤ _ := hdiv
          _ ≤ _ := hnorm'
          _ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left h3 hK0
          _ ≤ ε := hKε
      · have hmem : y ∈ Icc θ θ⁻¹ := ⟨(not_le.1 h1).le, (not_le.1 h2).le⟩
        have hL := hbn hmem
        have hm1 : min (Real.sqrt y) (Real.sqrt y)⁻¹ ≤ 1 := by
          rcases le_total (Real.sqrt y) 1 with h | h
          · exact (min_le_left _ _).trans h
          · refine (min_le_right _ _).trans ?_
            exact inv_le_one_of_one_le₀ h
        have hKb : K ≤ ε * (1 + bCoef α (B n) (i n)) := by
          have := (div_le_iff₀ hε).1 hL
          nlinarith
        calc _ ≤ K * min (Real.sqrt y) (Real.sqrt y)⁻¹ / (1 + bCoef α (B n) (i n)) :=
              div_le_div_of_nonneg_right hnorm' (by linarith)
          _ ≤ K * 1 / (1 + bCoef α (B n) (i n)) :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm1 hK0) (by linarith)
          _ ≤ ε := by
              rw [mul_one, div_le_iff₀ (by linarith)]
              exact hKb

/-- `lem:app-pl-vector` (snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[The flat response]\label{lem:app-pl-vector}
Along every such row sequence,
\[
\Big\|\mathcal V_i(g)-\frac{g}{\sqrt{\sw2}}-b\sign(g)\Big\|_{L^2(g)}=o(1+b),
\]
and for fixed $0<\delta<M$ the $L^2(g)$ norm of the part of $\mathcal V_i$ over
$\delta<m<M$ is $o(1+b)$.
\end{lemma}
-/
theorem lem_app_pl_vector {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) :
    (∀ᶠ n in atTop,
        Integrable (fun g => calV β (B n) (plSpec α (c n) (N n)) (i n) g ^ 2) (gaussianReal 0 1)) ∧
    Tendsto (fun n => l2Norm (fun g =>
        calV β (B n) (plSpec α (c n) (N n)) (i n) g -
          (g / Real.sqrt (sPow β 2) + bCoef α (B n) (i n) * Real.sign g)) /
          (1 + bCoef α (B n) (i n)))
      atTop (𝓝 0) ∧
    ∀ δ M : ℝ, 0 < δ → δ < M →
      (∀ᶠ n in atTop,
        Integrable (fun g => calVpart β (B n) (plSpec α (c n) (N n)) (i n) δ M g ^ 2)
          (gaussianReal 0 1)) ∧
      Tendsto (fun n => l2Norm (fun g => calVpart β (B n) (plSpec α (c n) (N n)) (i n) δ M g) /
        (1 + bCoef α (B n) (i n))) atTop (𝓝 0) := by
  exact vm_vector_main R hα1 i hi hx

/-! ### Helpers for `lem_app_pl_strip` -/


private lemma vm_int_min_split {m₀ a b T : ℝ} (hm₀ : 0 < m₀) (ha : 0 < a) (haT : a ≤ T) (hTb : T ≤ b) :
    ∫ m in a..b, min (m / m₀) (m₀ / m) ≤ (T ^ 2 - a ^ 2) / (2 * m₀) + m₀ * Real.log (b / T) := by
  have hT : 0 < T := lt_of_lt_of_le ha haT
  have hab : a ≤ b := haT.trans hTb
  have hcont : ContinuousOn (fun m : ℝ => min (m / m₀) (m₀ / m)) (Set.Icc a b) := by
    refine ContinuousOn.inf (continuousOn_id.div_const _) (continuousOn_const.div continuousOn_id ?_)
    intro x hx; exact (lt_of_lt_of_le ha hx.1).ne'
  have hi1 : IntervalIntegrable (fun m : ℝ => min (m / m₀) (m₀ / m)) volume a T :=
    (hcont.mono (by rw [Set.uIcc_of_le haT]; exact Set.Icc_subset_Icc_right hTb)).intervalIntegrable
  have hi2 : IntervalIntegrable (fun m : ℝ => min (m / m₀) (m₀ / m)) volume T b :=
    (hcont.mono (by rw [Set.uIcc_of_le hTb]; exact Set.Icc_subset_Icc_left haT)).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have h1 : ∫ m in a..T, min (m / m₀) (m₀ / m) ≤ ∫ m in a..T, m / m₀ := by
    refine intervalIntegral.integral_mono_on haT hi1 ?_ (fun x _ => min_le_left _ _)
    exact (continuous_id.div_const _).intervalIntegrable _ _
  have h2 : ∫ m in T..b, min (m / m₀) (m₀ / m) ≤ ∫ m in T..b, m₀ * m⁻¹ := by
    refine intervalIntegral.integral_mono_on hTb hi2 ?_ (fun x _ => by
      have := min_le_right (x / m₀) (m₀ / x); rwa [div_eq_mul_inv] at this)
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul (continuousOn_inv₀.mono ?_)
    intro x hx
    rw [Set.uIcc_of_le hTb] at hx
    exact (lt_of_lt_of_le hT hx.1).ne'
  have e1 : ∫ m in a..T, m / m₀ = (T ^ 2 - a ^ 2) / (2 * m₀) := by
    rw [intervalIntegral.integral_div, integral_id]
    field_simp
  have e2 : ∫ m in T..b, m₀ * m⁻¹ = m₀ * Real.log (b / T) := by
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hT (lt_of_lt_of_le hT hTb)]
  linarith

private lemma vm_int_min {m₀ a b γ : ℝ} (hm₀ : 0 < m₀) (hmγ : m₀ ≤ γ) (ha : 0 < a) (hab : a ≤ b)
    (hbγ : b ≤ γ) :
    ∫ m in a..b, min (m / m₀) (m₀ / m) ≤ m₀ * (1 / 2 + Real.log (γ / m₀)) := by
  have hγ : 0 < γ := lt_of_lt_of_le hm₀ hmγ
  have hlog0 : 0 ≤ Real.log (γ / m₀) := Real.log_nonneg ((one_le_div hm₀).2 hmγ)
  rcases le_total m₀ a with h1 | h1
  · have := vm_int_min_split hm₀ ha le_rfl hab
    refine this.trans ?_
    have : Real.log (b / a) ≤ Real.log (γ / m₀) := by
      apply Real.log_le_log (div_pos (lt_of_lt_of_le ha hab) ha)
      rw [div_le_div_iff₀ ha hm₀]
      nlinarith [mul_le_mul hbγ h1 hm₀.le hγ.le]
    rw [sub_self, zero_div, zero_add]
    nlinarith [mul_le_mul_of_nonneg_left this hm₀.le]
  · rcases le_total m₀ b with h2 | h2
    · have := vm_int_min_split hm₀ ha h1 h2
      refine this.trans ?_
      have hlog : Real.log (b / m₀) ≤ Real.log (γ / m₀) :=
        Real.log_le_log (div_pos (lt_of_lt_of_le hm₀ h2) hm₀) (div_le_div_of_nonneg_right hbγ hm₀.le)
      have e : (m₀ ^ 2 - a ^ 2) / (2 * m₀) ≤ m₀ / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [sq_nonneg a, sq_nonneg m₀]
      nlinarith [mul_le_mul_of_nonneg_left hlog hm₀.le]
    · have := vm_int_min_split hm₀ ha (hab) le_rfl
      refine this.trans ?_
      rw [div_self (lt_of_lt_of_le ha hab).ne', Real.log_one]
      have e : (b ^ 2 - a ^ 2) / (2 * m₀) ≤ m₀ / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [sq_nonneg a, mul_le_mul h2 h2 (lt_of_lt_of_le ha hab).le hm₀.le]
      nlinarith [mul_nonneg hm₀.le hlog0]



private lemma vm_phi_mono {s s' : ℝ} (hs : 0 < s) (hss' : s ≤ s') (hs' : s' ≤ Real.exp (-1 / 2)) :
    s * (1 / 2 + Real.log (1 / s)) ≤ s' * (1 / 2 + Real.log (1 / s')) := by
  have key : MonotoneOn (fun t : ℝ => t * (1 / 2 + Real.log (1 / t))) (Set.Ioc 0 (Real.exp (-1 / 2))) := by
    have hform : ∀ t : ℝ, 0 < t → t * (1 / 2 + Real.log (1 / t)) = t / 2 - t * Real.log t := by
      intro t ht
      rw [Real.log_div one_ne_zero ht.ne', Real.log_one]; ring
    have hc : ContinuousOn (fun t : ℝ => t / 2 - t * Real.log t) (Set.Ioc 0 (Real.exp (-1 / 2))) := by
      refine ((continuousOn_id.div_const _)).sub ?_
      exact Real.continuous_mul_log.continuousOn
    have hmono : MonotoneOn (fun t : ℝ => t / 2 - t * Real.log t) (Set.Ioc 0 (Real.exp (-1 / 2))) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ioc _ _) hc ?_ ?_
      · intro t ht
        rw [interior_Ioc] at ht
        have ht0 : t ≠ 0 := ht.1.ne'
        exact (((differentiableAt_id.div_const _)).sub (differentiableAt_id.mul (Real.differentiableAt_log ht0))).differentiableWithinAt
      · intro t ht
        rw [interior_Ioc] at ht
        have ht0 : t ≠ 0 := ht.1.ne'
        have hd : HasDerivAt (fun t : ℝ => t / 2 - t * Real.log t) (1 / 2 - (Real.log t + t * t⁻¹)) t := by
          have h1 : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) t := by
            simpa using (hasDerivAt_id t).div_const 2
          have h2 := (hasDerivAt_id t).mul (Real.hasDerivAt_log ht0)
          simp only [id] at h2
          have h3 := h1.sub h2
          convert h3 using 1
          · funext x; simp
          · simp
        rw [hd.deriv]
        have : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0
        have hl : Real.log t ≤ -1 / 2 := by
          have := Real.log_le_log ht.1 ht.2.le
          rwa [Real.log_exp] at this
        linarith
    intro a ha b hb hab
    simp only
    rw [hform a ha.1, hform b hb.1]
    exact hmono ha hb hab
  exact key ⟨hs, hss'.trans hs'⟩ ⟨hs.trans_le hss', hs'⟩ hss'



private lemma vm_pos_plSpec {α c : ℝ} (hc : 0 < c) (N : ℕ) (i : Fin N) : 0 < plSpec α c N i := by
  unfold plSpec
  exact mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)

/-- `Λ_N(m)/m` is nondecreasing on `(0,γ)`. -/
private lemma vm_lam_div_mono {α : ℝ} (hα : 0 < α) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) :
    MonotoneOn (fun m : ℝ => partLam B (plSpec α c N) m / m) (Ioo 0 (gammaOf N B)) := by
  obtain ⟨cα, hcα, hel⟩ := lem_app_pl_elasticity_i hα
  obtain ⟨-, -, -, hcd⟩ := def_app_pl_participation_bij (plSpec α c N) hB hN (vm_pos_plSpec hc N)
  obtain ⟨-, hbL, -, -⟩ := def_app_pl_participation_bij (plSpec α c N) hB hN (vm_pos_plSpec hc N)
  have hdiff : ∀ m ∈ Ioo 0 (gammaOf N B), DifferentiableAt ℝ (partLam B (plSpec α c N)) m := by
    intro m hm
    exact ((hcd.contDiffAt (Ioo_mem_nhds hm.1 hm.2)).differentiableAt (by simp))
  have hpos : ∀ m ∈ Ioo 0 (gammaOf N B), 0 < partLam B (plSpec α c N) m :=
    fun m hm => hbL.mapsTo hm
  refine monotoneOn_of_deriv_nonneg (convex_Ioo _ _) ?_ ?_ ?_
  · intro m hm
    exact ((hdiff m hm).div differentiableAt_id hm.1.ne').continuousAt.continuousWithinAt
  · intro m hm
    rw [interior_Ioo] at hm
    exact ((hdiff m hm).div differentiableAt_id hm.1.ne').differentiableWithinAt
  · intro m hm
    rw [interior_Ioo] at hm
    have hd := (hdiff m hm).hasDerivAt.div (hasDerivAt_id' m) hm.1.ne'
    have hderiv : deriv (fun m : ℝ => partLam B (plSpec α c N) m / m) m =
        (deriv (partLam B (plSpec α c N)) m * m - partLam B (plSpec α c N) m * 1) / m ^ 2 := by
      have hd' : HasDerivAt (fun m : ℝ => partLam B (plSpec α c N) m / m)
          ((deriv (partLam B (plSpec α c N)) m * m - partLam B (plSpec α c N) m * 1) / m ^ 2) m := hd
      exact hd'.deriv
    rw [hderiv]
    apply div_nonneg _ (sq_nonneg _)
    have h1 := ((hel N B c hN hB hc).2 m hm).1
    have hL := hpos m hm
    rw [le_div_iff₀ hL] at h1
    have : 1 / m * partLam B (plSpec α c N) m ≤ deriv (partLam B (plSpec α c N)) m := h1
    have h2 : partLam B (plSpec α c N) m ≤ deriv (partLam B (plSpec α c N)) m * m := by
      have := mul_le_mul_of_nonneg_right this hm.1.le
      rw [show 1 / m * partLam B (plSpec α c N) m * m = partLam B (plSpec α c N) m by have := hm.1.ne'; field_simp] at this
      exact this
    linarith


/-- The scale `m₀ = m_N(1/μ_i)`. -/
private lemma vm_m0_facts {α : ℝ} {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) (i : Fin N) :
    partMN B (plSpec α c N) (1 / plSpec α c N i) ∈ Ioo 0 (gammaOf N B) ∧
      partLam B (plSpec α c N) (partMN B (plSpec α c N) (1 / plSpec α c N i)) = 1 / plSpec α c N i := by
  have hp := vm_pos_plSpec (α := α) hc N
  obtain ⟨hbM, -, -, -⟩ := def_app_pl_participation_bij (plSpec α c N) hB hN hp
  have hx : (1 / plSpec α c N i) ∈ Ioi (0:ℝ) := by
    have := hp i; exact one_div_pos.2 this
  refine ⟨hbM.mapsTo hx, ?_⟩
  exact hbM.invOn_invFunOn.1 hx

private lemma vm_h_bound {α : ℝ} (hα : 0 < α) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B) (hc : 0 < c)
    (i : Fin N) {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    plSpec α c N i * partLam B (plSpec α c N) m / (1 + plSpec α c N i * partLam B (plSpec α c N) m) ^ 2 ≤
      min (m / partMN B (plSpec α c N) (1 / plSpec α c N i))
        (partMN B (plSpec α c N) (1 / plSpec α c N i) / m) := by
  obtain ⟨hm0, hL0⟩ := vm_m0_facts (α := α) hN hB hc i
  set m₀ := partMN B (plSpec α c N) (1 / plSpec α c N i) with hm₀
  have hμ := vm_pos_plSpec (α := α) hc N i
  obtain ⟨-, hbL, -, -⟩ := def_app_pl_participation_bij (plSpec α c N) hB hN (vm_pos_plSpec hc N)
  have hLpos : 0 < partLam B (plSpec α c N) m := hbL.mapsTo hm
  set u := plSpec α c N i * partLam B (plSpec α c N) m with hu
  have hu0 : 0 < u := mul_pos hμ hLpos
  have hmono := vm_lam_div_mono hα hN hB hc
  have hm₀pos := hm0.1
  have hlt : u / (1 + u) ^ 2 ≤ u := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg u]
  have hlt2 : u / (1 + u) ^ 2 ≤ 1 / u := by
    rw [div_le_div_iff₀ (by positivity) hu0]; nlinarith [sq_nonneg u]
  have hLm : partLam B (plSpec α c N) m₀ / m₀ = 1 / plSpec α c N i / m₀ := by rw [hL0]
  rcases le_total m m₀ with h | h
  · have := hmono hm hm0 h
    simp only at this
    rw [hLm] at this
    have h1 : u / m ≤ 1 / m₀ := by
      have : plSpec α c N i * (partLam B (plSpec α c N) m / m) ≤ plSpec α c N i * (1 / plSpec α c N i / m₀) :=
        mul_le_mul_of_nonneg_left this hμ.le
      calc u / m = plSpec α c N i * (partLam B (plSpec α c N) m / m) := by rw [hu]; ring
        _ ≤ _ := this
        _ = 1 / m₀ := by field_simp
    have h2 : u ≤ m / m₀ := by
      rw [div_le_iff₀ hm.1] at h1
      calc u ≤ 1 / m₀ * m := h1
        _ = m / m₀ := by ring
    have h3 : m / m₀ ≤ m₀ / m := by
      rw [div_le_div_iff₀ hm₀pos hm.1]; nlinarith [mul_le_mul h h hm.1.le hm₀pos.le]
    exact le_min (hlt.trans h2) ((hlt.trans h2).trans h3)
  · have := hmono hm0 hm h
    simp only at this
    rw [hLm] at this
    have h1 : 1 / m₀ ≤ u / m := by
      have : plSpec α c N i * (1 / plSpec α c N i / m₀) ≤ plSpec α c N i * (partLam B (plSpec α c N) m / m) :=
        mul_le_mul_of_nonneg_left this hμ.le
      calc 1 / m₀ = plSpec α c N i * (1 / plSpec α c N i / m₀) := by field_simp
        _ ≤ _ := this
        _ = u / m := by rw [hu]; ring
    have h2 : m / m₀ ≤ u := by
      rw [le_div_iff₀ hm.1] at h1
      calc m / m₀ = 1 / m₀ * m := by ring
        _ ≤ u := h1
    have h4 : 1 / u ≤ m₀ / m := by
      rw [div_le_div_iff₀ hu0 hm.1]
      rw [div_le_iff₀ hm₀pos] at h2
      nlinarith
    have h5 : m₀ / m ≤ m / m₀ := by
      rw [div_le_div_iff₀ hm.1 hm₀pos]; nlinarith [mul_le_mul h h hm₀pos.le hm.1.le]
    exact le_min ((hlt2.trans h4).trans h5) (hlt2.trans h4)



private lemma vm_emaW_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (a : ℕ) : 0 < emaW β a := by
  unfold emaW
  exact mul_pos (by linarith) (pow_pos hβ0 a)

open Muon.DetEquiv in
private lemma vm_weightSeq {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : WeightSeq (emaW β) := by
  refine ⟨fun j => (vm_emaW_pos hβ0 hβ1 j).le, ?_, ⟨0, (vm_emaW_pos hβ0 hβ1 0).ne'⟩⟩
  have key : emaW β = fun j => (1 - β) * β ^ j := by
    funext j; rfl
  rw [key]
  exact (summable_geometric_of_lt_one hβ0.le hβ1).mul_left _

open Muon.DetEquiv in
private lemma vm_range {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    ∃ a ∈ Ioi (0:ℝ), rW (emaW β) a = m := by
  have hcont : ContinuousOn (rW (emaW β)) (Ici 0) :=
    continuousOn_id.mul (lem_app_de_scalar_ii (vm_weightSeq hβ0 hβ1)).2.2.1
  have hr0 := (lem_app_de_scalar_iii (vm_weightSeq hβ0 hβ1)).2.2.1
  have hT := (lem_app_de_scalar_iii (vm_weightSeq hβ0 hβ1)).2.2.2.2.2.2
  have hinf : {j : ℕ | 0 < emaW β j} = Set.univ := by
    ext j
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact vm_emaW_pos hβ0 hβ1 j
  have hTop : (Set.encard {j : ℕ | 0 < emaW β j}).toENNReal = ⊤ := by
    rw [hinf, Set.encard_univ, ENat.card_eq_top_of_infinite]
    rfl
  rw [hTop] at hT
  have hev : ∀ᶠ q in atTop, ENNReal.ofReal m < ENNReal.ofReal (rW (emaW β) q) :=
    hT.eventually (Ioi_mem_nhds ENNReal.ofReal_lt_top)
  obtain ⟨Q0, hQ0⟩ := (hev.and (eventually_ge_atTop (1:ℝ))).exists
  have hlt : ENNReal.ofReal m < ENNReal.ofReal (rW (emaW β) Q0) := hQ0.1
  have hmQ : m < rW (emaW β) Q0 := (ENNReal.ofReal_lt_ofReal_iff'.1 hlt).1
  have hmem : m ∈ Icc (rW (emaW β) 0) (rW (emaW β) Q0) :=
    ⟨by rw [hr0]; exact hm.le, hmQ.le⟩
  obtain ⟨q, hq, hqe⟩ := intermediate_value_Icc (by linarith [hQ0.2] : (0:ℝ) ≤ Q0)
    (hcont.mono Icc_subset_Ici_self) hmem
  have hqpos : 0 < q := by
    rcases hq.1.eq_or_lt with h | h
    · rw [← h, hr0] at hqe
      linarith
    · exact h
  exact ⟨q, hqpos, hqe⟩

open Muon.DetEquiv in
private lemma vm_Qm_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    0 < Qm β m := by
  have hex : ∃ a ∈ Ioi (0:ℝ), rW (emaW β) a = m := vm_range hβ0 hβ1 hm
  exact Function.invFunOn_mem hex

private lemma vm_DNat_nonneg {β : ℝ} (hβ0 : 0 < β) {q1 q2 : ℝ} (hq1 : 0 ≤ q1)
    (hq2 : 0 ≤ q2) (ℓ : ℕ) : 0 ≤ DLagNat β q1 q2 ℓ := by
  unfold DLagNat
  refine tsum_nonneg fun a => integral_nonneg fun g => ?_
  have := hq1; have := hq2; have : 0 ≤ β ^ ℓ := pow_nonneg hβ0.le ℓ
  have : 0 ≤ β ^ (2 * ℓ) := pow_nonneg hβ0.le _
  positivity

private lemma vm_DLag_nonneg {β : ℝ} (hβ0 : 0 < β) {q1 q2 : ℝ} (hq1 : 0 ≤ q1)
    (hq2 : 0 ≤ q2) (ℓ : ℤ) : 0 ≤ DLag β q1 q2 ℓ := by
  unfold DLag
  split_ifs
  · exact vm_DNat_nonneg hβ0 hq1 hq2 _
  · exact vm_DNat_nonneg hβ0 hq2 hq1 _


/-- The majorant `g(m) = min(1/m₀, m₀/m²)`. -/
private def vmG (m₀ m : ℝ) : ℝ := min (1 / m₀) (m₀ / m ^ 2)

private lemma vm_G_mul {m₀ m : ℝ} (hm₀ : 0 < m₀) (hm : 0 < m) :
    vmG m₀ m * m = min (m / m₀) (m₀ / m) := by
  unfold vmG
  rw [min_mul_of_nonneg (1 / m₀) (m₀ / m ^ 2) hm.le]
  congr 1
  · field_simp
  · field_simp

private lemma vm_G_nonneg {m₀ m : ℝ} (hm₀ : 0 < m₀) : 0 ≤ vmG m₀ m := by
  unfold vmG
  exact le_min (by positivity) (by positivity)

private lemma vm_G_ratio {m₀ m₁ m₂ R : ℝ} (hm₀ : 0 < m₀) (h1 : 0 < m₁) (hR : 1 ≤ R)
    (h2 : m₁ / R ≤ m₂) :
    vmG m₀ m₂ ≤ R ^ 2 * vmG m₀ m₁ := by
  have hR0 : 0 < R := by linarith
  have h2p : 0 < m₁ / R := div_pos h1 hR0
  have hm2 : 0 < m₂ := lt_of_lt_of_le h2p h2
  unfold vmG
  rw [mul_min_of_nonneg (1 / m₀) (m₀ / m₁ ^ 2) (sq_nonneg R)]
  refine le_min ?_ ?_
  · calc min (1 / m₀) (m₀ / m₂ ^ 2) ≤ 1 / m₀ := min_le_left _ _
      _ ≤ R ^ 2 * (1 / m₀) := by
        have : (1:ℝ) ≤ R ^ 2 := by nlinarith
        have h0 : 0 ≤ 1 / m₀ := by positivity
        nlinarith
  · calc min (1 / m₀) (m₀ / m₂ ^ 2) ≤ m₀ / m₂ ^ 2 := min_le_right _ _
      _ ≤ R ^ 2 * (m₀ / m₁ ^ 2) := by
        have : m₁ ≤ R * m₂ := by rwa [div_le_iff₀ hR0, mul_comm] at h2
        rw [div_le_iff₀ (by positivity)]
        have h3 : m₁ ^ 2 ≤ (R * m₂) ^ 2 := by nlinarith
        have h4 : m₀ = m₀ / m₁ ^ 2 * m₁ ^ 2 := by field_simp
        have h5 : m₀ / m₁ ^ 2 * m₁ ^ 2 ≤ m₀ / m₁ ^ 2 * (R * m₂) ^ 2 :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
        calc m₀ = m₀ / m₁ ^ 2 * m₁ ^ 2 := h4
          _ ≤ m₀ / m₁ ^ 2 * (R * m₂) ^ 2 := h5
          _ = R ^ 2 * (m₀ / m₁ ^ 2) * m₂ ^ 2 := by ring

private lemma vm_J_le {α : ℝ} (hα : 0 < α) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B) (hc : 0 < c)
    (i : Fin N) {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    0 ≤ Jrow B (plSpec α c N) i m ∧
    Jrow B (plSpec α c N) i m ≤
      Real.sqrt (vmG (partMN B (plSpec α c N) (1 / plSpec α c N i)) m) := by
  obtain ⟨hm0, -⟩ := vm_m0_facts (α := α) hN hB hc i
  set m₀ := partMN B (plSpec α c N) (1 / plSpec α c N i) with hm₀
  have hμ := vm_pos_plSpec (α := α) hc N i
  obtain ⟨-, hbL, -, -⟩ := def_app_pl_participation_bij (plSpec α c N) hB hN (vm_pos_plSpec hc N)
  have hLpos : 0 < partLam B (plSpec α c N) m := hbL.mapsTo hm
  set u := plSpec α c N i * partLam B (plSpec α c N) m with hu
  have hu0 : 0 < u := mul_pos hμ hLpos
  have hh := vm_h_bound hα hN hB hc i hm
  rw [← hu, ← hm₀] at hh
  have hγm : 0 < 1 - m / gammaOf N B := by
    have hγ : 0 < gammaOf N B := lt_trans hm.1 hm.2
    rw [sub_pos, div_lt_one hγ]; exact hm.2
  have hmpos : 0 < m := hm.1
  have hJ0 : 0 ≤ Jrow B (plSpec α c N) i m := by
    unfold Jrow; positivity
  refine ⟨hJ0, ?_⟩
  apply Real.le_sqrt_of_sq_le
  have hsq : Jrow B (plSpec α c N) i m ^ 2 = u / (1 + u) ^ 2 / m * (1 - m / gammaOf N B) := by
    unfold Jrow
    rw [← hu]
    rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hu0.le, Real.sq_sqrt hm.1.le, Real.sq_sqrt hγm.le]
    field_simp
  rw [hsq]
  have hle1 : 1 - m / gammaOf N B ≤ 1 := by
    have : 0 ≤ m / gammaOf N B := div_nonneg hm.1.le (lt_trans hm.1 hm.2).le
    linarith
  have hmpos : 0 < m := hm.1
  have hnn : 0 ≤ u / (1 + u) ^ 2 / m := by positivity
  calc u / (1 + u) ^ 2 / m * (1 - m / gammaOf N B) ≤ u / (1 + u) ^ 2 / m * 1 :=
        mul_le_mul_of_nonneg_left hle1 hnn
    _ = u / (1 + u) ^ 2 / m := mul_one _
    _ ≤ vmG m₀ m := by
        unfold vmG
        refine le_min ?_ ?_
        · rw [div_le_iff₀ hm.1]
          have := (hh.trans (min_le_left _ _))
          calc u / (1 + u) ^ 2 ≤ m / m₀ := this
            _ = 1 / m₀ * m := by ring
        · rw [div_le_iff₀ hm.1]
          have := (hh.trans (min_le_right _ _))
          calc u / (1 + u) ^ 2 ≤ m₀ / m := this
            _ = m₀ / m ^ 2 * m := by field_simp

set_option maxHeartbeats 800000 in
private lemma vm_pointwise {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) (η Rr Mc : ℝ)
    (hRr : 1 < Rr) (hMc : 1 ≤ Mc) (hη0 : 0 < η) (hη1 : η < 1 / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c → 2 ≤ gammaOf N B →
      ∀ (i : Fin N) (ℓ : ℤ) (p : ℝ × ℝ), p ∈ stripSet η Rr Mc (gammaOf N B) →
        0 ≤ DLag β (Qm β p.1) (Qm β p.2) ℓ ∧
        0 ≤ lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 ∧
        lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 ≤
          K * vmG (partMN B (plSpec α c N) (1 / plSpec α c N i)) p.1 *
            DLag β (Qm β p.1) (Qm β p.2) ℓ := by
  obtain ⟨cα, hcα, hchain⟩ := lem_app_pl_determinant_ii_chain hα
  obtain ⟨C0, hC0⟩ := lem_app_pl_elasticity_ii hα hβ0 hβ1
  obtain ⟨cE, CE, hcE, -, hE⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  set Cθ : ℝ := 3 * max C0 1 with hCθ
  have hCθ0 : 0 < Cθ := by
    have : (1:ℝ) ≤ max C0 1 := le_max_right _ _
    rw [hCθ]; linarith
  refine ⟨4 * Cθ ^ 2 * Rr / cα, by positivity, ?_⟩
  intro N B c hN hB hc hγ2 i ℓ p hp
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ := hp
  set γ := gammaOf N B with hγdef
  have hγ0 : 0 < γ := by linarith
  have hηγ : η * γ < γ / 2 := by nlinarith
  have hm1 : p.1 ∈ Ioo 0 γ := ⟨by linarith, by linarith⟩
  have hm2 : p.2 ∈ Ioo 0 γ := ⟨by linarith, by linarith⟩
  have hQ1 := vm_Qm_pos hβ0 hβ1 hm1.1
  have hQ2 := vm_Qm_pos hβ0 hβ1 hm2.1
  have hD0 : 0 ≤ DLag β (Qm β p.1) (Qm β p.2) ℓ := vm_DLag_nonneg hβ0 hQ1.le hQ2.le ℓ
  -- theta bounds
  have hθ : ∀ m ∈ Ioo 0 γ, Mc < m → m < η * γ →
      0 ≤ thetaN β B (plSpec α c N) m ∧ thetaN β B (plSpec α c N) m ≤ Cθ := by
    intro m hm hMm hmη
    obtain ⟨hθup, hθlow⟩ := hC0 N B c hN hB hc m hm
    have hEpos : 0 < Efun β m := by
      have := (hE m hm.1).1
      have : 0 < cE * min m 1 := mul_pos hcE (lt_min hm.1 one_pos)
      linarith [(hE m hm.1).1]
    have hθ0 : 0 ≤ thetaN β B (plSpec α c N) m := by
      by_contra hneg
      push_neg at hneg
      have : Efun β m * thetaN β B (plSpec α c N) m < 0 := mul_neg_of_pos_of_neg hEpos hneg
      linarith
    refine ⟨hθ0, ?_⟩
    have h1 : 1 / m ≤ 1 := by rw [div_le_one hm.1]; linarith
    have h2 : 1 / (γ - m) ≤ 1 := by rw [div_le_one (by linarith [hm.2])]; linarith
    have h3 : 0 ≤ 1 + 1 / m + 1 / (γ - m) := by
      have : 0 < 1 / m := by have := hm.1; positivity
      have : 0 < 1 / (γ - m) := by have : 0 < γ - m := by linarith [hm.2]
                                   positivity
      linarith
    have h4 : C0 * (1 + 1 / m + 1 / (γ - m)) ≤ max C0 1 * (1 + 1 / m + 1 / (γ - m)) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) h3
    have h5 : max C0 1 * (1 + 1 / m + 1 / (γ - m)) ≤ max C0 1 * 3 :=
      mul_le_mul_of_nonneg_left (by linarith) (le_trans zero_le_one (le_max_right _ _))
    rw [hCθ]; linarith
  obtain ⟨hθ1a, hθ1b⟩ := hθ p.1 hm1 hp1 hp2
  obtain ⟨hθ2a, hθ2b⟩ := hθ p.2 hm2 hp3 hp4
  set m₀ := partMN B (plSpec α c N) (1 / plSpec α c N i) with hm₀
  obtain ⟨hm0, -⟩ := vm_m0_facts (α := α) hN hB hc i
  obtain ⟨hJ1a, hJ1b⟩ := vm_J_le hα hN hB hc i hm1
  obtain ⟨hJ2a, hJ2b⟩ := vm_J_le hα hN hB hc i hm2
  rw [← hm₀] at hJ1b hJ2b
  have hW : ∀ (m : ℝ), Wpart β B (plSpec α c N) i m = Jrow B (plSpec α c N) i m * thetaN β B (plSpec α c N) m :=
    fun m => rfl
  -- g ratio
  have hratio : vmG m₀ p.2 ≤ Rr ^ 2 * vmG m₀ p.1 := by
    apply vm_G_ratio hm0.1 hm1.1 hRr.le
    have hm2pos := hm2.1
    have : p.1 ≤ Rr * p.2 := by
      have := (div_le_iff₀ hm2pos).1 hp6
      linarith
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hsq2 : Real.sqrt (vmG m₀ p.2) ≤ Rr * Real.sqrt (vmG m₀ p.1) := by
    calc Real.sqrt (vmG m₀ p.2) ≤ Real.sqrt (Rr ^ 2 * vmG m₀ p.1) := Real.sqrt_le_sqrt hratio
      _ = Rr * Real.sqrt (vmG m₀ p.1) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]
  have hg1 : 0 ≤ Real.sqrt (vmG m₀ p.1) := Real.sqrt_nonneg _
  have hW1a : 0 ≤ Wpart β B (plSpec α c N) i p.1 := by rw [hW]; exact mul_nonneg hJ1a hθ1a
  have hW2a : 0 ≤ Wpart β B (plSpec α c N) i p.2 := by rw [hW]; exact mul_nonneg hJ2a hθ2a
  have hW1b : Wpart β B (plSpec α c N) i p.1 ≤ Cθ * Real.sqrt (vmG m₀ p.1) := by
    rw [hW]
    calc _ ≤ Real.sqrt (vmG m₀ p.1) * Cθ := mul_le_mul hJ1b hθ1b hθ1a (by positivity)
      _ = _ := by ring
  have hW2b : Wpart β B (plSpec α c N) i p.2 ≤ Cθ * (Rr * Real.sqrt (vmG m₀ p.1)) := by
    rw [hW]
    calc _ ≤ (Rr * Real.sqrt (vmG m₀ p.1)) * Cθ :=
          mul_le_mul (hJ2b.trans hsq2) hθ2b hθ2a (by positivity)
      _ = _ := by ring
  have hWW : Wpart β B (plSpec α c N) i p.1 * Wpart β B (plSpec α c N) i p.2 ≤
      Cθ ^ 2 * Rr * vmG m₀ p.1 := by
    calc _ ≤ (Cθ * Real.sqrt (vmG m₀ p.1)) * (Cθ * (Rr * Real.sqrt (vmG m₀ p.1))) :=
          mul_le_mul hW1b hW2b hW2a (by positivity)
      _ = Cθ ^ 2 * Rr * (Real.sqrt (vmG m₀ p.1)) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (vm_G_nonneg hm0.1)]
  -- Delta bound
  have hΔ : cα / 4 ≤ deltaN β B (plSpec α c N) ℓ p.1 p.2 := by
    have h1 := lem_app_pl_determinant_ii hα hβ0 hβ1 N B c hN hB hc ℓ p.1 p.2 hm1 hm2
    have h2 := hchain N B c hN hB hc p.1 p.2 hm1 hm2
    have e1 : 1 / 2 ≤ 1 - p.1 / γ := by
      have : p.1 / γ ≤ 1 / 2 := by rw [div_le_iff₀ hγ0]; linarith
      linarith
    have e2 : 1 / 2 ≤ 1 - p.2 / γ := by
      have : p.2 / γ ≤ 1 / 2 := by rw [div_le_iff₀ hγ0]; linarith
      linarith
    have : (1/4 : ℝ) ≤ (1 - p.1 / γ) * (1 - p.2 / γ) := by nlinarith
    nlinarith
  have hΔpos : 0 < deltaN β B (plSpec α c N) ℓ p.1 p.2 := by linarith
  have hlag : lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 =
      Wpart β B (plSpec α c N) i p.1 * Wpart β B (plSpec α c N) i p.2 *
        DLag β (Qm β p.1) (Qm β p.2) ℓ / deltaN β B (plSpec α c N) ℓ p.1 p.2 := rfl
  refine ⟨hD0, ?_, ?_⟩
  · rw [hlag]; positivity
  · rw [hlag, div_le_iff₀ hΔpos]
    have hnum : Wpart β B (plSpec α c N) i p.1 * Wpart β B (plSpec α c N) i p.2 *
        DLag β (Qm β p.1) (Qm β p.2) ℓ ≤ Cθ ^ 2 * Rr * vmG m₀ p.1 * DLag β (Qm β p.1) (Qm β p.2) ℓ :=
      mul_le_mul_of_nonneg_right hWW hD0
    have hGD : 0 ≤ Cθ ^ 2 * Rr * vmG m₀ p.1 * DLag β (Qm β p.1) (Qm β p.2) ℓ := by
      have := vm_G_nonneg (m := p.1) hm0.1
      positivity
    calc _ ≤ Cθ ^ 2 * Rr * vmG m₀ p.1 * DLag β (Qm β p.1) (Qm β p.2) ℓ := hnum
      _ = 4 * Cθ ^ 2 * Rr / cα * vmG m₀ p.1 * DLag β (Qm β p.1) (Qm β p.2) ℓ * (cα / 4) := by
          field_simp
      _ ≤ 4 * Cθ ^ 2 * Rr / cα * vmG m₀ p.1 * DLag β (Qm β p.1) (Qm β p.2) ℓ *
            deltaN β B (plSpec α c N) ℓ p.1 p.2 := by
          refine mul_le_mul_of_nonneg_left hΔ ?_
          have := vm_G_nonneg (m := p.1) hm0.1
          positivity

private lemma vm_strip_meas (η Rr Mc γ : ℝ) : MeasurableSet (stripSet η Rr Mc γ) := by
  unfold stripSet
  simp only [Set.setOf_and]
  refine MeasurableSet.inter (measurableSet_lt (by fun_prop) (by fun_prop)) ?_
  refine MeasurableSet.inter (measurableSet_lt (by fun_prop) (by fun_prop)) ?_
  refine MeasurableSet.inter (measurableSet_lt (by fun_prop) (by fun_prop)) ?_
  refine MeasurableSet.inter (measurableSet_lt (by fun_prop) (by fun_prop)) ?_
  refine MeasurableSet.inter (measurableSet_le (by fun_prop) (by fun_prop)) ?_
  exact measurableSet_le (by fun_prop) (by fun_prop)

private lemma vm_slice {η Rr Mc γ : ℝ} (hRr : 1 < Rr) (hMc : 0 < Mc) {g : ℝ → ℝ} (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) :
    ∫⁻ p in stripSet η Rr Mc γ, ENNReal.ofReal (g p.1) ≤
      ∫⁻ m in Ioo Mc (η * γ), ENNReal.ofReal (g m * (Rr * m)) := by
  have hS := vm_strip_meas η Rr Mc γ
  rw [← lintegral_indicator hS, ← lintegral_indicator measurableSet_Ioo, Measure.volume_eq_prod,
    lintegral_prod _ (by
      refine Measurable.aemeasurable ?_
      exact (ENNReal.measurable_ofReal.comp (hg.comp measurable_fst)).indicator hS)]
  refine lintegral_mono (fun x => ?_)
  by_cases hx : x ∈ Ioo Mc (η * γ)
  · rw [Set.indicator_of_mem hx]
    have hx0 : 0 < x := lt_trans hMc hx.1
    have hRr0 : 0 < Rr := by linarith
    calc ∫⁻ y, (stripSet η Rr Mc γ).indicator (fun p : ℝ × ℝ => ENNReal.ofReal (g p.1)) (x, y)
        ≤ ∫⁻ y, (Icc (x / Rr) (Rr * x)).indicator (fun _ => ENNReal.ofReal (g x)) y := by
          refine lintegral_mono (fun y => ?_)
          by_cases hy : (x, y) ∈ stripSet η Rr Mc γ
          · rw [Set.indicator_of_mem hy]
            obtain ⟨-, -, hy1, -, h5, h6⟩ := hy
            have hy0 : 0 < y := lt_trans hMc hy1
            have hyin : y ∈ Icc (x / Rr) (Rr * x) := by
              constructor
              · rw [div_le_iff₀ hRr0]
                have := (div_le_iff₀ hy0).1 h6
                linarith
              · have := (le_div_iff₀ hy0).1 h5
                rw [inv_mul_le_iff₀ hRr0] at this
                linarith
            rw [Set.indicator_of_mem hyin]
          · rw [Set.indicator_of_notMem hy]; exact bot_le
      _ = ENNReal.ofReal (g x) * volume (Icc (x / Rr) (Rr * x)) := by
          rw [lintegral_indicator_const measurableSet_Icc]
      _ ≤ ENNReal.ofReal (g x * (Rr * x)) := by
          rw [Real.volume_Icc, ← ENNReal.ofReal_mul (hg0 x)]
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_left _ (hg0 x)
          have : 0 ≤ x / Rr := by positivity
          linarith
  · rw [Set.indicator_of_notMem hx]
    have : ∀ y, (stripSet η Rr Mc γ).indicator (fun p : ℝ × ℝ => ENNReal.ofReal (g p.1)) (x, y) = 0 := by
      intro y
      apply Set.indicator_of_notMem
      intro hp
      exact hx ⟨hp.1, hp.2.1⟩
    simp [this]


private lemma vm_Dsum {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ CD : ℝ, 0 ≤ CD ∧ ∀ m₁ m₂ : ℝ, 0 < m₁ → 0 < m₂ →
      ∑' ℓ : ℤ, ENNReal.ofReal (DLag β (Qm β m₁) (Qm β m₂) ℓ) ≤ ENNReal.ofReal CD := by
  obtain ⟨C, hC⟩ := (lem_app_pl_age_i hβ0 hβ1).1
  refine ⟨C ^ 2, sq_nonneg _, fun m₁ m₂ h1 h2 => ?_⟩
  obtain ⟨-, hs⟩ := lem_app_pl_age_iii hβ0 hβ1 m₁ m₂ h1 h2
  have hnn : ∀ ℓ : ℤ, 0 ≤ DLag β (Qm β m₁) (Qm β m₂) ℓ := fun ℓ =>
    vm_DLag_nonneg hβ0 (vm_Qm_pos hβ0 hβ1 h1).le (vm_Qm_pos hβ0 hβ1 h2).le ℓ
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hs.summable, hs.tsum_eq]
  apply ENNReal.ofReal_le_ofReal
  have hb : ‖∫ g : ℝ, Zg β g (Qm β m₁) * Zg β g (Qm β m₂) ∂(gaussianReal 0 1)‖ ≤ C ^ 2 := by
    have := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 1)
      (f := fun g : ℝ => Zg β g (Qm β m₁) * Zg β g (Qm β m₂)) (C := C ^ 2)
      (Filter.Eventually.of_forall (fun g => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        have a1 := hC (Qm β m₁) g (vm_Qm_pos hβ0 hβ1 h1)
        have a2 := hC (Qm β m₂) g (vm_Qm_pos hβ0 hβ1 h2)
        calc |Zg β g (Qm β m₁)| * |Zg β g (Qm β m₂)| ≤ C * C :=
              mul_le_mul a1 a2 (abs_nonneg _) ((abs_nonneg _).trans a1)
          _ = C ^ 2 := by ring))
    simpa using this
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hb)


private lemma vm_strip_bound {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) (η Rr Mc : ℝ)
    (hRr : 1 < Rr) (hMc : 1 ≤ Mc) (hη0 : 0 < η) (hη1 : η < 1 / 2) :
    ∃ Kt : ℝ, 0 ≤ Kt ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c → 2 ≤ gammaOf N B →
      Mc ≤ η * gammaOf N B → ∀ i : Fin N,
        (∀ ℓ : ℤ, IntegrableOn (fun p : ℝ × ℝ => lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2)
          (stripSet η Rr Mc (gammaOf N B))) ∧
        Summable (fun ℓ : ℤ => ∫ p in stripSet η Rr Mc (gammaOf N B),
          lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2) ∧
        0 ≤ ∑' ℓ : ℤ, ∫ p in stripSet η Rr Mc (gammaOf N B),
          lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 ∧
        ∑' ℓ : ℤ, ∫ p in stripSet η Rr Mc (gammaOf N B),
          lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 ≤
          Kt * (partMN B (plSpec α c N) (1 / plSpec α c N i) *
            (1 / 2 + Real.log (gammaOf N B / partMN B (plSpec α c N) (1 / plSpec α c N i)))) := by
  obtain ⟨K, hK0, hK⟩ := vm_pointwise hα hβ0 hβ1 η Rr Mc hRr hMc hη0 hη1
  obtain ⟨CD, hCD0, hCD⟩ := vm_Dsum hβ0 hβ1
  refine ⟨K * CD * Rr, by positivity, ?_⟩
  intro N B c hN hB hc hγ2 hMη i
  set γ := gammaOf N B with hγdef
  set S := stripSet η Rr Mc γ with hSdef
  have hγ0 : 0 < γ := by linarith
  have hMc0 : 0 < Mc := by linarith
  have hS := vm_strip_meas η Rr Mc γ
  set m₀ := partMN B (plSpec α c N) (1 / plSpec α c N i) with hm₀
  obtain ⟨hm0, -⟩ := vm_m0_facts (α := α) hN hB hc i
  set F : ℤ → ℝ × ℝ → ℝ := fun ℓ p => lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 with hF
  -- integrability
  have hsub : S ⊆ Ioo 0 γ ×ˢ Ioo 0 γ := by
    intro p hp
    obtain ⟨h1, h2, h3, h4, -, -⟩ := hp
    have : η * γ < γ := by nlinarith
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hint : ∀ ℓ : ℤ, IntegrableOn (F ℓ) S := fun ℓ =>
    ((lem_app_pl_age_iv hα hβ0 hβ1 N B c hN hB hc i).2.2.1 ℓ).mono_set hsub
  have hnn : ∀ ℓ : ℤ, ∀ p ∈ S, 0 ≤ F ℓ p := fun ℓ p hp => (hK N B c hN hB hc hγ2 i ℓ p hp).2.1
  -- the ENNReal quantities
  set a : ℤ → ENNReal := fun ℓ => ∫⁻ p in S, ENNReal.ofReal (F ℓ p) with ha
  have ha_eq : ∀ ℓ, a ℓ = ENNReal.ofReal (∫ p in S, F ℓ p) := fun ℓ => by
    rw [ofReal_integral_eq_lintegral_ofReal (hint ℓ) (ae_restrict_of_forall_mem hS (hnn ℓ))]
  -- pointwise bound
  set g : ℝ → ℝ := fun x => vmG m₀ x with hg
  have hgm : Measurable g := by
    show Measurable (fun x => vmG m₀ x)
    unfold vmG; fun_prop
  have hg0 : ∀ x, 0 ≤ g x := fun x => vm_G_nonneg hm0.1
  have hpt : ∀ p ∈ S, ∑' ℓ : ℤ, ENNReal.ofReal (F ℓ p) ≤
      ENNReal.ofReal (K * g p.1) * ENNReal.ofReal CD := by
    intro p hp
    have hp1 : 0 < p.1 := lt_trans hMc0 hp.1
    have hp2 : 0 < p.2 := lt_trans hMc0 hp.2.2.1
    calc ∑' ℓ : ℤ, ENNReal.ofReal (F ℓ p)
        ≤ ∑' ℓ : ℤ, ENNReal.ofReal (K * g p.1) * ENNReal.ofReal (DLag β (Qm β p.1) (Qm β p.2) ℓ) := by
          refine ENNReal.tsum_le_tsum (fun ℓ => ?_)
          rw [← ENNReal.ofReal_mul (by have := hg0 p.1; positivity)]
          apply ENNReal.ofReal_le_ofReal
          have := (hK N B c hN hB hc hγ2 i ℓ p hp).2.2
          calc F ℓ p ≤ _ := this
            _ = _ := by simp only [hg, hm₀]
      _ = ENNReal.ofReal (K * g p.1) * ∑' ℓ : ℤ, ENNReal.ofReal (DLag β (Qm β p.1) (Qm β p.2) ℓ) :=
          ENNReal.tsum_mul_left
      _ ≤ _ := mul_le_mul' (le_refl _) (hCD p.1 p.2 hp1 hp2)
  have hlin : ∑' ℓ, a ℓ = ∫⁻ p in S, ∑' ℓ : ℤ, ENNReal.ofReal (F ℓ p) := by
    rw [lintegral_tsum (fun ℓ => (hint ℓ).aemeasurable.ennreal_ofReal)]
  have hbig : ∑' ℓ, a ℓ ≤ ENNReal.ofReal (K * CD * Rr * (m₀ * (1 / 2 + Real.log (γ / m₀)))) := by
    rw [hlin]
    calc ∫⁻ p in S, ∑' ℓ : ℤ, ENNReal.ofReal (F ℓ p)
        ≤ ∫⁻ p in S, ENNReal.ofReal (K * g p.1) * ENNReal.ofReal CD :=
          setLIntegral_mono' hS hpt
      _ = ENNReal.ofReal K * (∫⁻ p in S, ENNReal.ofReal (g p.1)) * ENNReal.ofReal CD := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
          congr 1
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr (fun p => ?_)
          rw [ENNReal.ofReal_mul hK0.le]
      _ ≤ ENNReal.ofReal K * (∫⁻ m in Ioo Mc (η * γ), ENNReal.ofReal (g m * (Rr * m))) *
            ENNReal.ofReal CD := by
          gcongr
          exact vm_slice hRr hMc0 hgm hg0
      _ = ENNReal.ofReal K * ENNReal.ofReal (Rr * ∫ m in Mc..(η * γ), min (m / m₀) (m₀ / m)) *
            ENNReal.ofReal CD := by
          congr 2
          have hcongr : ∫⁻ m in Ioo Mc (η * γ), ENNReal.ofReal (g m * (Rr * m)) =
              ∫⁻ m in Ioo Mc (η * γ), ENNReal.ofReal (Rr * min (m / m₀) (m₀ / m)) := by
            refine setLIntegral_congr_fun measurableSet_Ioo (fun m hm => ?_)
            have hmp : 0 < m := lt_trans hMc0 hm.1
            have := vm_G_mul hm0.1 hmp
            show ENNReal.ofReal (vmG m₀ m * (Rr * m)) = _
            congr 1
            calc vmG m₀ m * (Rr * m) = Rr * (vmG m₀ m * m) := by ring
              _ = _ := by rw [this]
          rw [hcongr]
          have hcont : ContinuousOn (fun m : ℝ => Rr * min (m / m₀) (m₀ / m)) (Icc Mc (η * γ)) := by
            refine continuousOn_const.mul (ContinuousOn.inf (continuousOn_id.div_const _)
              (continuousOn_const.div continuousOn_id ?_))
            intro x hx; exact (lt_of_lt_of_le hMc0 hx.1).ne'
          have hiOo : IntegrableOn (fun m : ℝ => Rr * min (m / m₀) (m₀ / m)) (Ioo Mc (η * γ)) :=
            (hcont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
          rw [← ofReal_integral_eq_lintegral_ofReal hiOo
            (ae_restrict_of_forall_mem measurableSet_Ioo (fun m hm => by
              have hmp : 0 < m := lt_trans hMc0 hm.1
              have : 0 ≤ min (m / m₀) (m₀ / m) := le_min (by have := hm0.1; positivity) (by have := hm0.1; positivity)
              positivity))]
          congr 1
          rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hMη,
            intervalIntegral.integral_const_mul]
      _ ≤ ENNReal.ofReal K * ENNReal.ofReal (Rr * (m₀ * (1 / 2 + Real.log (γ / m₀)))) *
            ENNReal.ofReal CD := by
          have hmin := vm_int_min hm0.1 hm0.2.le hMc0 hMη (show η * γ ≤ γ by nlinarith)
          gcongr
      _ = _ := by
          rw [← ENNReal.ofReal_mul hK0.le, ← ENNReal.ofReal_mul (by
            have := hm0.1
            have : 0 ≤ Real.log (γ / m₀) := Real.log_nonneg ((one_le_div hm0.1).2 hm0.2.le)
            positivity)]
          congr 1; ring
  have hfin : ∑' ℓ, a ℓ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbig
  have hne : ∀ ℓ, a ℓ ≠ ⊤ := fun ℓ => ne_top_of_le_ne_top hfin (ENNReal.le_tsum ℓ)
  have hreal : ∀ ℓ, (a ℓ).toReal = ∫ p in S, F ℓ p := fun ℓ => by
    rw [ha_eq, ENNReal.toReal_ofReal]
    exact integral_nonneg_of_ae (ae_restrict_of_forall_mem hS (hnn ℓ))
  have hsum : Summable (fun ℓ => ∫ p in S, F ℓ p) := by
    have := ENNReal.summable_toReal hfin
    simpa [hreal] using this
  have htsum : ∑' ℓ, ∫ p in S, F ℓ p = (∑' ℓ, a ℓ).toReal := by
    rw [ENNReal.tsum_toReal_eq hne]; simp [hreal]
  refine ⟨hint, hsum, ?_, ?_⟩
  · rw [htsum]; exact ENNReal.toReal_nonneg
  · rw [htsum]
    refine ENNReal.toReal_le_of_le_ofReal ?_ hbig
    have := hm0.1
    have : 0 ≤ Real.log (γ / m₀) := Real.log_nonneg ((one_le_div hm0.1).2 hm0.2.le)
    positivity

private lemma vm_contS_cont_int {α : ℝ} (hα : 0 < α) {V : ℝ} (hV : 0 < V) :
    IntervalIntegrable (fun t : ℝ => V / (V + t ^ α)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuousOn_const
    (continuousOn_const.add ((Real.continuous_rpow_const hα.le).continuousOn))
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  have := Real.rpow_nonneg ht.1 α
  show V + t ^ α ≠ 0
  exact (by linarith : 0 < V + t ^ α).ne'

private lemma vm_contS_lt {α : ℝ} (hα : 0 < α) (hα1 : α < 1) {V : ℝ} (hV : 0 < V) :
    contS α V ≤ V / (1 - α) := by
  unfold contS
  have hint : IntervalIntegrable (fun t : ℝ => V * t ^ (-α)) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < -α)).const_mul V
  have hle : ∫ t in (0:ℝ)..1, V / (V + t ^ α) ≤ ∫ t in (0:ℝ)..1, V * t ^ (-α) := by
    refine intervalIntegral.integral_mono_ae_restrict zero_le_one (vm_contS_cont_int hα hV) hint ?_
    have h0 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by
      simp [ae_iff]
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [h0] with t ht htI
    have htpos : 0 < t := lt_of_le_of_ne htI.1 (Ne.symm ht)
    have hp : 0 < t ^ α := Real.rpow_pos_of_pos htpos α
    rw [Real.rpow_neg htpos.le, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hV.le hp (by linarith)
  have hval : ∫ t in (0:ℝ)..1, V * t ^ (-α) = V / (1 - α) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
    have : (0:ℝ) ^ (-α + 1) = 0 := Real.zero_rpow (by linarith)
    rw [this, Real.one_rpow]
    have : -α + 1 = 1 - α := by ring
    rw [this]; ring
  linarith

private lemma vm_contS_one {V : ℝ} (hV : 0 < V) (hV1 : V ≤ 1) :
    contS 1 V ≤ V * (Real.log 2 + Real.log (1 / V)) := by
  unfold contS
  have e1 : ∀ t : ℝ, V / (V + t ^ (1:ℝ)) = V * (V + t)⁻¹ := fun t => by
    rw [Real.rpow_one, div_eq_mul_inv]
  simp_rw [e1]
  rw [intervalIntegral.integral_const_mul]
  have : ∫ t in (0:ℝ)..1, (V + t)⁻¹ = Real.log ((V + 1) / V) := by
    have := intervalIntegral.integral_comp_add_left (a := 0) (b := 1) (fun x : ℝ => x⁻¹) V
    rw [this, integral_inv_of_pos (by linarith) (by linarith)]
    simp
  rw [this]
  apply mul_le_mul_of_nonneg_left _ hV.le
  rw [← Real.log_mul (by norm_num) (by positivity)]
  apply Real.log_le_log (by positivity)
  rw [div_le_iff₀ hV]
  field_simp
  linarith

private lemma vm_m0_eq {α : ℝ} {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) (i : Fin N) :
    partMN B (plSpec α c N) (1 / plSpec α c N i) =
      gammaOf N B * finS α N (rowFrac i ^ α) := by
  have hμ := vm_pos_plSpec (α := α) hc N i
  rw [eqn_app_pl_SN_mN α c hN hB hc (one_div_pos.2 hμ)]
  congr 2
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hi : (0:ℝ) < rowIdx i := by unfold rowIdx; positivity
  unfold rowFrac plSpec
  show c * (1 / (c * (rowIdx i) ^ (-α))) * (N:ℝ) ^ (-α) = _
  rw [Real.div_rpow hi.le hNr.le, Real.rpow_neg hi.le, Real.rpow_neg hNr.le]
  have : 0 < rowIdx i ^ α := Real.rpow_pos_of_pos hi α
  have : 0 < (N:ℝ) ^ α := Real.rpow_pos_of_pos hNr α
  field_simp

private lemma vm_finS_pos {α : ℝ} {N : ℕ} (hN : 0 < N) {V : ℝ} (hV : 0 < V) : 0 < finS α N V := by
  unfold finS
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  refine mul_pos (inv_pos.2 hNr) (Finset.sum_pos (fun j hj => ?_) ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hN⟩⟩)
  have hj0 : (0:ℝ) < j := by exact_mod_cast (Finset.mem_Icc.1 hj).1
  have : 0 < ((j:ℝ) / N) ^ α := Real.rpow_pos_of_pos (div_pos hj0 hNr) α
  positivity

private lemma vm_c0_pos : 0 < c0 := by
  unfold c0; exact Real.sqrt_pos.2 (by positivity)

private lemma vm_equiv_lower {u v : ℕ → ℝ} (h : IsEquivalent atTop u v) (hv : ∀ᶠ n in atTop, 0 < v n) :
    ∀ᶠ n in atTop, v n / 2 ≤ u n := by
  filter_upwards [h.isLittleO.def (by norm_num : (0:ℝ) < 1 / 2), hv] with n h1 h2
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos h2] at h1
  have := (abs_le.1 h1).1
  simp only [Pi.sub_apply] at this
  linarith

private lemma vm_bsq {α : ℝ} {γ x : ℝ} (hγ : 0 ≤ γ) (hx : 0 < x) :
    (Real.sqrt γ * x ^ (α / 2) * profPsi α x / c0) ^ 2 = γ * x ^ α * profPsi α x ^ 2 / c0 ^ 2 := by
  have h1 : (x ^ (α / 2)) ^ 2 = x ^ α := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hγ, h1]

private lemma vm_squeeze {Num b P : ℕ → ℝ} (hN : ∀ᶠ n in atTop, 0 ≤ Num n)
    (hb : ∀ᶠ n in atTop, 0 ≤ b n) (hP : ∀ᶠ n in atTop, 0 < P n ∧ P n ≤ b n ^ 2)
    (hlim : Tendsto (fun n => Num n / P n) atTop (𝓝 0)) :
    Tendsto (fun n => Num n / (1 + b n) ^ 2) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [hN, hb] with n h1 h2
    positivity
  · filter_upwards [hN, hb, hP] with n h1 h2 h3
    apply div_le_div_of_nonneg_left h1 h3.1
    nlinarith [h3.2]

private lemma vm_L_tendsto {α : ℝ} (hα : 0 < α) {x : ℕ → ℝ} (hx0 : ∀ n, 0 < x n)
    (hx : Tendsto x atTop (𝓝 0)) :
    Tendsto (fun n => Real.log (x n ^ (-α))) atTop atTop := by
  have hx' : Tendsto x atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hx, Eventually.of_forall hx0⟩
  have hT : Tendsto (fun n => -α * Real.log (x n)) atTop atTop :=
    (Real.tendsto_log_nhdsGT_zero.comp hx').const_mul_atBot_of_neg (neg_neg_of_pos hα)
  refine hT.congr (fun n => ?_)
  rw [Real.log_rpow (hx0 n)]

private lemma vm_pull {x : ℕ → ℝ} (hx0 : ∀ n, 0 < x n) (hx : Tendsto x atTop (𝓝 0)) :
    Tendsto x atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hx, Eventually.of_forall hx0⟩

private lemma vm_lim_lt {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {γ x : ℕ → ℝ} (hγ : ∀ n, 0 < γ n)
    (hx0 : ∀ n, 0 < x n) (hx : Tendsto x atTop (𝓝 0)) :
    Tendsto (fun n => (γ n * x n ^ α / (1 - α) *
        (1 / 2 + Real.log (1 - α) + Real.log (x n ^ (-α)))) /
      (1 + Real.sqrt (γ n) * x n ^ (α / 2) * profPsi α (x n) / c0) ^ 2) atTop (𝓝 0) := by
  have hm : 0 < 1 - α := by linarith
  have hsm : 0 < Real.sqrt (1 - α) := Real.sqrt_pos.2 hm
  have hc0 := vm_c0_pos
  set L : ℕ → ℝ := fun n => Real.log (x n ^ (-α)) with hL
  have hLt : Tendsto L atTop atTop := vm_L_tendsto hα0 hx0 hx
  have hLpos : ∀ᶠ n in atTop, 0 < L n := hLt.eventually_gt_atTop 0
  set cc : ℝ := 1 / 2 + Real.log (1 - α) with hcc
  have hLcc : ∀ᶠ n in atTop, 0 ≤ cc + L n := (hLt.eventually_ge_atTop (-cc)).mono (fun n h => by linarith)
  have hPsi : IsEquivalent atTop (fun n => profPsi α (x n))
      (fun n => c0 / Real.sqrt (1 - α) * L n) :=
    (lem_app_pl_Psi_ii_lt hα0 hα1).comp_tendsto (vm_pull hx0 hx)
  have hlow := vm_equiv_lower hPsi (hLpos.mono (fun n h => by positivity))
  refine (vm_squeeze (Num := fun n => γ n * x n ^ α / (1 - α) * (1 / 2 + Real.log (1 - α) + L n))
    (b := fun n => Real.sqrt (γ n) * x n ^ (α / 2) * profPsi α (x n) / c0)
    (P := fun n => γ n * x n ^ α * L n ^ 2 / (4 * (1 - α))) ?_ ?_ ?_ ?_)
  · filter_upwards [hLcc] with n h
    have := hγ n; have := Real.rpow_pos_of_pos (hx0 n) α
    have e : (1:ℝ) / 2 + Real.log (1 - α) + L n = cc + L n := by rw [hcc]
    rw [e]; positivity
  · filter_upwards [hlow, hLpos] with n h1 h2
    have hp : 0 < profPsi α (x n) := lt_of_lt_of_le (by positivity) h1
    have := hγ n; have := Real.rpow_pos_of_pos (hx0 n) (α / 2)
    positivity
  · filter_upwards [hlow, hLpos] with n h1 h2
    have hg := hγ n
    have hxa := Real.rpow_pos_of_pos (hx0 n) α
    refine ⟨by positivity, ?_⟩
    rw [vm_bsq hg.le (hx0 n)]
    have hw : 0 < c0 / Real.sqrt (1 - α) * L n / 2 := by positivity
    have hsq : (c0 / Real.sqrt (1 - α) * L n / 2) ^ 2 ≤ profPsi α (x n) ^ 2 := by
      apply pow_le_pow_left₀ hw.le h1
    have e : (c0 / Real.sqrt (1 - α) * L n / 2) ^ 2 = c0 ^ 2 * L n ^ 2 / (4 * (1 - α)) := by
      rw [div_pow, mul_pow, div_pow, Real.sq_sqrt hm.le]
      have := hm.ne'
      field_simp
      ring
    rw [e] at hsq
    rw [le_div_iff₀ (by positivity)]
    calc γ n * x n ^ α * L n ^ 2 / (4 * (1 - α)) * c0 ^ 2
        = γ n * x n ^ α * (c0 ^ 2 * L n ^ 2 / (4 * (1 - α))) := by ring
      _ ≤ γ n * x n ^ α * profPsi α (x n) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
  · have hLi : Tendsto (fun n => (L n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hLt
    have h4 : Tendsto (fun n => 4 * (cc * ((L n)⁻¹) ^ 2 + (L n)⁻¹)) atTop (𝓝 (4 * (cc * 0 ^ 2 + 0))) :=
      (((hLi.pow 2).const_mul cc).add hLi).const_mul 4
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at h4
    refine h4.congr' ?_
    filter_upwards [hLpos] with n hn
    have hg := hγ n
    have hxa := Real.rpow_pos_of_pos (hx0 n) α
    field_simp
    ring

private lemma vm_lim_one {γ x : ℕ → ℝ} (hγ : ∀ n, 0 < γ n)
    (hx0 : ∀ n, 0 < x n) (hx : Tendsto x atTop (𝓝 0)) :
    Tendsto (fun n => (γ n * x n ^ (1:ℝ) * (Real.log 2 + Real.log (1 / x n)) *
        (1 / 2 + Real.log (1 / x n))) /
      (1 + Real.sqrt (γ n) * x n ^ ((1:ℝ) / 2) * profPsi 1 (x n) / c0) ^ 2) atTop (𝓝 0) := by
  have hc0 := vm_c0_pos
  set L : ℕ → ℝ := fun n => Real.log (1 / x n) with hL
  have hLt : Tendsto L atTop atTop := by
    have hT := Real.tendsto_log_nhdsGT_zero.comp (vm_pull hx0 hx)
    have := tendsto_neg_atBot_atTop.comp hT
    refine this.congr (fun n => ?_)
    simp [hL, Real.log_inv]
  have hLpos : ∀ᶠ n in atTop, 0 < L n := hLt.eventually_gt_atTop 0
  have hPsi : IsEquivalent atTop (fun n => profPsi 1 (x n))
      (fun n => 2 / 3 * c0 * L n ^ (3 / 2 : ℝ)) :=
    (lem_app_pl_Psi_ii_one rfl).comp_tendsto (vm_pull hx0 hx)
  have hlow := vm_equiv_lower hPsi (hLpos.mono (fun n h => by
    have := Real.rpow_pos_of_pos h (3 / 2 : ℝ); positivity))
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine (vm_squeeze (Num := fun n => γ n * x n ^ (1:ℝ) * (Real.log 2 + L n) * (1 / 2 + L n))
    (b := fun n => Real.sqrt (γ n) * x n ^ ((1:ℝ) / 2) * profPsi 1 (x n) / c0)
    (P := fun n => γ n * x n ^ (1:ℝ) * L n ^ 3 / 9) ?_ ?_ ?_ ?_)
  · filter_upwards [hLpos] with n h
    have := hγ n; have := Real.rpow_pos_of_pos (hx0 n) (1:ℝ)
    positivity
  · filter_upwards [hlow, hLpos] with n h1 h2
    have hLr := Real.rpow_pos_of_pos h2 (3 / 2 : ℝ)
    have hp : 0 < profPsi 1 (x n) := lt_of_lt_of_le (by positivity) h1
    have := hγ n; have := Real.rpow_pos_of_pos (hx0 n) ((1:ℝ) / 2)
    positivity
  · filter_upwards [hlow, hLpos] with n h1 h2
    have hg := hγ n
    have hxa := Real.rpow_pos_of_pos (hx0 n) (1:ℝ)
    have hLr := Real.rpow_pos_of_pos h2 (3 / 2 : ℝ)
    refine ⟨by positivity, ?_⟩
    rw [vm_bsq hg.le (hx0 n)]
    have hw : 0 < 2 / 3 * c0 * L n ^ (3 / 2 : ℝ) / 2 := by positivity
    have hsq : (2 / 3 * c0 * L n ^ (3 / 2 : ℝ) / 2) ^ 2 ≤ profPsi 1 (x n) ^ 2 :=
      pow_le_pow_left₀ hw.le h1 2
    have e : (2 / 3 * c0 * L n ^ (3 / 2 : ℝ) / 2) ^ 2 = c0 ^ 2 * L n ^ 3 / 9 := by
      have : (L n ^ (3 / 2 : ℝ)) ^ 2 = L n ^ 3 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul h2.le]; norm_num
      calc (2 / 3 * c0 * L n ^ (3 / 2 : ℝ) / 2) ^ 2 = c0 ^ 2 / 9 * (L n ^ (3 / 2 : ℝ)) ^ 2 := by ring
        _ = _ := by rw [this]; ring
    rw [e] at hsq
    rw [le_div_iff₀ (by positivity)]
    calc γ n * x n ^ (1:ℝ) * L n ^ 3 / 9 * c0 ^ 2
        = γ n * x n ^ (1:ℝ) * (c0 ^ 2 * L n ^ 3 / 9) := by ring
      _ ≤ γ n * x n ^ (1:ℝ) * profPsi 1 (x n) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
  · have hLi : Tendsto (fun n => (L n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hLt
    have h4 : Tendsto (fun n => 9 * ((Real.log 2 * (L n)⁻¹ + 1) * ((1 / 2) * (L n)⁻¹ + 1) * (L n)⁻¹))
        atTop (𝓝 (9 * ((Real.log 2 * 0 + 1) * ((1 / 2) * 0 + 1) * 0))) :=
      ((((hLi.const_mul (Real.log 2)).add_const 1).mul ((hLi.const_mul (1 / 2)).add_const 1)).mul hLi).const_mul 9
    simp only [mul_zero, zero_add, mul_one] at h4
    refine h4.congr' ?_
    filter_upwards [hLpos] with n hn
    have hg := hγ n
    have hxa := Real.rpow_pos_of_pos (hx0 n) (1:ℝ)
    field_simp

private lemma vm_Jb_gen {α : ℝ} (hα : 0 < α) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B) (hc : 0 < c)
    (i : Fin N) (hγ : 0 < gammaOf N B) {s' : ℝ}
    (hs' : contS α (rowFrac i ^ α) ≤ s') (hs'e : s' ≤ Real.exp (-1 / 2)) :
    partMN B (plSpec α c N) (1 / plSpec α c N i) *
      (1 / 2 + Real.log (gammaOf N B / partMN B (plSpec α c N) (1 / plSpec α c N i))) ≤
    gammaOf N B * (s' * (1 / 2 + Real.log (1 / s'))) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hi : (0:ℝ) < rowIdx i := by unfold rowIdx; positivity
  have hx : 0 < rowFrac i := by unfold rowFrac; positivity
  have hV : 0 < rowFrac i ^ α := Real.rpow_pos_of_pos hx α
  rw [vm_m0_eq hN hB hc i]
  set s := finS α N (rowFrac i ^ α) with hs
  have hspos : 0 < s := vm_finS_pos hN hV
  have hsle : s ≤ s' := by
    have := (lem_app_pl_finite_inverse_i_a hα hN (rowFrac i ^ α) hV).1
    linarith
  have hlog : Real.log (gammaOf N B / (gammaOf N B * s)) = Real.log (1 / s) := by
    congr 1; field_simp
  rw [hlog]
  have := vm_phi_mono hspos hsle hs'e
  calc gammaOf N B * s * (1 / 2 + Real.log (1 / s)) = gammaOf N B * (s * (1 / 2 + Real.log (1 / s))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left this hγ.le

private lemma vm_Jb_lt {α : ℝ} (hα : 0 < α) (hα1 : α < 1) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) (i : Fin N) (hγ : 0 < gammaOf N B)
    (hs'e : rowFrac i ^ α / (1 - α) ≤ Real.exp (-1 / 2)) :
    partMN B (plSpec α c N) (1 / plSpec α c N i) *
      (1 / 2 + Real.log (gammaOf N B / partMN B (plSpec α c N) (1 / plSpec α c N i))) ≤
    gammaOf N B * rowFrac i ^ α / (1 - α) *
      (1 / 2 + Real.log (1 - α) + Real.log (rowFrac i ^ (-α))) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hi : (0:ℝ) < rowIdx i := by unfold rowIdx; positivity
  have hx : 0 < rowFrac i := by unfold rowFrac; positivity
  have hV : 0 < rowFrac i ^ α := Real.rpow_pos_of_pos hx α
  have hm : 0 < 1 - α := by linarith
  have := vm_Jb_gen hα hN hB hc i hγ (vm_contS_lt hα hα1 hV) hs'e
  refine this.trans (le_of_eq ?_)
  have e1 : Real.log (1 / (rowFrac i ^ α / (1 - α))) = Real.log (1 - α) + Real.log (rowFrac i ^ (-α)) := by
    rw [Real.rpow_neg hx.le, one_div_div, Real.log_div hm.ne' hV.ne', Real.log_inv]
    ring
  rw [e1]; ring

private lemma vm_Jb_one {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) (i : Fin N) (hγ : 0 < gammaOf N B) (hx1 : rowFrac i ≤ 1)
    (hL1 : 1 ≤ Real.log 2 + Real.log (1 / rowFrac i))
    (hs'e : rowFrac i * (Real.log 2 + Real.log (1 / rowFrac i)) ≤ Real.exp (-1 / 2)) :
    partMN B (plSpec 1 c N) (1 / plSpec 1 c N i) *
      (1 / 2 + Real.log (gammaOf N B / partMN B (plSpec 1 c N) (1 / plSpec 1 c N i))) ≤
    gammaOf N B * rowFrac i ^ (1:ℝ) * (Real.log 2 + Real.log (1 / rowFrac i)) *
      (1 / 2 + Real.log (1 / rowFrac i)) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hi : (0:ℝ) < rowIdx i := by unfold rowIdx; positivity
  have hx : 0 < rowFrac i := by unfold rowFrac; positivity
  have hc1 : contS 1 (rowFrac i ^ (1:ℝ)) ≤ rowFrac i * (Real.log 2 + Real.log (1 / rowFrac i)) := by
    rw [Real.rpow_one]; exact vm_contS_one hx hx1
  have := vm_Jb_gen (by norm_num : (0:ℝ) < 1) hN hB hc i hγ hc1 hs'e
  refine this.trans ?_
  set L := Real.log (1 / rowFrac i) with hL
  set s' := rowFrac i * (Real.log 2 + L) with hs'
  have hs'pos : 0 < s' := by
    have : 0 < Real.log 2 + L := by linarith
    positivity
  have hne : Real.log 2 + L ≠ 0 := by linarith
  have hlog : Real.log (1 / s') ≤ L := by
    have e : 1 / s' = (1 / rowFrac i) * (1 / (Real.log 2 + L)) := by
      rw [hs']; field_simp
    rw [e, Real.log_mul (one_div_ne_zero hx.ne') (one_div_ne_zero hne), ← hL]
    have : Real.log (1 / (Real.log 2 + L)) ≤ 0 :=
      Real.log_nonpos (by apply div_nonneg zero_le_one; linarith) (by rw [div_le_one (by linarith)]; exact hL1)
    linarith
  have h1 : 0 < s' := hs'pos
  have h2 : s' * (1 / 2 + Real.log (1 / s')) ≤ s' * (1 / 2 + L) :=
    mul_le_mul_of_nonneg_left (by linarith) h1.le
  calc gammaOf N B * (s' * (1 / 2 + Real.log (1 / s'))) ≤ gammaOf N B * (s' * (1 / 2 + L)) :=
        mul_le_mul_of_nonneg_left h2 hγ.le
    _ = _ := by rw [hs', Real.rpow_one]; ring

private lemma vm_rowFrac_bounds {N : ℕ} (i : Fin N) : 0 < rowFrac i ∧ rowFrac i ≤ 1 := by
  have hN : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hi : (0:ℝ) < rowIdx i := by unfold rowIdx; positivity
  refine ⟨by unfold rowFrac; positivity, ?_⟩
  unfold rowFrac
  rw [div_le_one hNr]
  unfold rowIdx
  have : (i : ℕ) + 1 ≤ N := i.isLt
  exact_mod_cast this


/-- `lem:app-pl-strip` (snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Multiplicative diagonal strip]\label{lem:app-pl-strip}
For fixed $R>1$, $M\ge1$ and $0<\eta<1/2$, let
$\mathcal D\defeq\{M<m_1,m_2<\eta\gamma,\ R^{-1}\le m_1/m_2\le R\}$. Along the row sequences above, the
lag-summed integral of \cref{eqn:app-pl-vol-zero} over $\mathcal D$ is $o((1+b)^2)$.
\end{lemma}
-/
theorem lem_app_pl_strip {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (Rr Mc η : ℝ) (hRr : 1 < Rr) (hMc : 1 ≤ Mc) (hη0 : 0 < η) (hη1 : η < 1 / 2)
    (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) :
    (∀ᶠ n in atTop, ∀ ℓ : ℤ,
        IntegrableOn
          (fun p : ℝ × ℝ => lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ p.1 p.2)
          (stripSet η Rr Mc (gammaOf (N n) (B n)))) ∧
    (∀ᶠ n in atTop,
        Summable (fun ℓ : ℤ =>
          ∫ p in stripSet η Rr Mc (gammaOf (N n) (B n)),
            lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ p.1 p.2)) ∧
    Tendsto (fun n => (Real.pi ^ 2)⁻¹ *
        (∑' ℓ : ℤ, ∫ p in stripSet η Rr Mc (gammaOf (N n) (B n)),
          lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ p.1 p.2) /
        (1 + bCoef α (B n) (i n)) ^ 2)
      atTop (𝓝 0) := by
  obtain ⟨Kt, hKt0, hKt⟩ := vm_strip_bound R.hα R.hβ0 R.hβ1 η Rr Mc hRr hMc hη0 hη1
  have hγt : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop := R.hγ
  have hγ2 : ∀ᶠ n in atTop, 2 ≤ gammaOf (N n) (B n) := hγt.eventually_ge_atTop 2
  have hγMc : ∀ᶠ n in atTop, Mc ≤ η * gammaOf (N n) (B n) :=
    (hγt.const_mul_atTop hη0).eventually_ge_atTop Mc
  have hall : ∀ᶠ n in atTop, 2 ≤ gammaOf (N n) (B n) ∧ Mc ≤ η * gammaOf (N n) (B n) :=
    hγ2.and hγMc
  have hB := fun n => hKt (N n) (B n) (c n) (R.hNpos n) (R.hBpos n) (R.hcpos n)
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hall] with n hn
    exact (hB n hn.1 hn.2 (i n)).1
  · filter_upwards [hall] with n hn
    exact (hB n hn.1 hn.2 (i n)).2.1
  · have hxb := fun n => vm_rowFrac_bounds (i n)
    have hγpos : ∀ n, 0 < gammaOf (N n) (B n) := fun n => by
      unfold gammaOf
      exact div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n)
    have hb0 : ∀ n, 0 ≤ bCoef α (B n) (i n) := fun n => by
      unfold bCoef
      have := lem_app_pl_Psi_i_pos R.hα (rowFrac (i n)) ⟨(hxb n).1, (hxb n).2⟩
      have := Real.rpow_pos_of_pos (hxb n).1 (α / 2)
      have := vm_c0_pos
      have := hγpos n
      positivity
    obtain ⟨U, hU, hJU⟩ : ∃ U : ℕ → ℝ,
        Tendsto (fun n => U n / (1 + bCoef α (B n) (i n)) ^ 2) atTop (𝓝 0) ∧
        ∀ᶠ n in atTop, partMN (B n) (plSpec α (c n) (N n)) (1 / plSpec α (c n) (N n) (i n)) *
          (1 / 2 + Real.log (gammaOf (N n) (B n) / partMN (B n) (plSpec α (c n) (N n))
            (1 / plSpec α (c n) (N n) (i n)))) ≤ U n := by
      rcases hα1.lt_or_eq with h | h
      · refine ⟨fun n => gammaOf (N n) (B n) * rowFrac (i n) ^ α / (1 - α) *
          (1 / 2 + Real.log (1 - α) + Real.log (rowFrac (i n) ^ (-α))), ?_, ?_⟩
        · exact vm_lim_lt R.hα h hγpos (fun n => (hxb n).1) hx
        · have hV : Tendsto (fun n => rowFrac (i n) ^ α / (1 - α)) atTop (𝓝 0) := by
            have := (hx.rpow_const (Or.inr R.hα.le)).div_const (1 - α)
            rwa [Real.zero_rpow R.hα.ne', zero_div] at this
          filter_upwards [hV.eventually (gt_mem_nhds (Real.exp_pos (-1 / 2)))] with n hn
          exact vm_Jb_lt R.hα h (R.hNpos n) (R.hBpos n) (R.hcpos n) (i n) (hγpos n) hn.le
      · subst h
        refine ⟨fun n => gammaOf (N n) (B n) * rowFrac (i n) ^ (1:ℝ) *
          (Real.log 2 + Real.log (1 / rowFrac (i n))) * (1 / 2 + Real.log (1 / rowFrac (i n))), ?_, ?_⟩
        · exact vm_lim_one hγpos (fun n => (hxb n).1) hx
        · have hLt : Tendsto (fun n => Real.log (1 / rowFrac (i n))) atTop atTop := by
            have hT := Real.tendsto_log_nhdsGT_zero.comp (vm_pull (fun n => (hxb n).1) hx)
            have := tendsto_neg_atBot_atTop.comp hT
            refine this.congr (fun n => ?_)
            simp [Real.log_inv]
          have hxl : Tendsto (fun n => rowFrac (i n) * (Real.log 2 + Real.log (1 / rowFrac (i n))))
              atTop (𝓝 0) := by
            have h1 : Tendsto (fun n => rowFrac (i n) * Real.log (rowFrac (i n))) atTop (𝓝 0) := by
              have := Real.continuous_mul_log.tendsto 0
              simp only [Real.log_zero, mul_zero] at this
              exact this.comp hx
            have h2 : Tendsto (fun n => rowFrac (i n) * Real.log 2) atTop (𝓝 0) := by
              simpa using hx.mul_const (Real.log 2)
            have := h2.sub h1
            simp only [sub_zero] at this
            refine this.congr (fun n => ?_)
            simp [Real.log_inv]; ring
          filter_upwards [hxl.eventually (gt_mem_nhds (Real.exp_pos (-1 / 2))),
            hLt.eventually_ge_atTop 1] with n hn hn2
          have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
          exact vm_Jb_one (R.hNpos n) (R.hBpos n) (R.hcpos n) (i n) (hγpos n) (hxb n).2
            (by linarith) hn.le
    have hup : Tendsto (fun n => (Real.pi ^ 2)⁻¹ * Kt *
        (U n / (1 + bCoef α (B n) (i n)) ^ 2)) atTop (𝓝 0) := by
      simpa using hU.const_mul ((Real.pi ^ 2)⁻¹ * Kt)
    refine squeeze_zero' ?_ ?_ hup
    · filter_upwards [hall] with n hn
      have := (hB n hn.1 hn.2 (i n)).2.2.1
      have := sq_nonneg (1 + bCoef α (B n) (i n))
      positivity
    · filter_upwards [hall, hJU] with n hn hJ
      have hS := (hB n hn.1 hn.2 (i n)).2.2.2
      have hD : 0 < (1 + bCoef α (B n) (i n)) ^ 2 := by
        have := hb0 n; positivity
      have hpi : 0 ≤ (Real.pi ^ 2)⁻¹ := by positivity
      have hS' : (∑' ℓ : ℤ, ∫ p in stripSet η Rr Mc (gammaOf (N n) (B n)),
          lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ p.1 p.2) ≤ Kt * U n :=
        hS.trans (mul_le_mul_of_nonneg_left hJ hKt0)
      calc (Real.pi ^ 2)⁻¹ * (∑' ℓ : ℤ, ∫ p in stripSet η Rr Mc (gammaOf (N n) (B n)),
          lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ p.1 p.2) /
            (1 + bCoef α (B n) (i n)) ^ 2
          ≤ (Real.pi ^ 2)⁻¹ * (Kt * U n) / (1 + bCoef α (B n) (i n)) ^ 2 := by
            apply div_le_div_of_nonneg_right _ hD.le
            exact mul_le_mul_of_nonneg_left hS' hpi
        _ = (Real.pi ^ 2)⁻¹ * Kt * (U n / (1 + bCoef α (B n) (i n)) ^ 2) := by ring

/-! ### Helpers for the mesoscopic comparison -/

private lemma vm_lagNumer_nonneg {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β)
    (hβ1 : β < 1) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) (i : Fin N) (ℓ : ℤ) {x y : ℝ}
    (hx : x ∈ Ioo 0 (gammaOf N B)) (hy : y ∈ Ioo 0 (gammaOf N B)) :
    0 ≤ lagNumer β B (plSpec α c N) i ℓ x y := by
  obtain ⟨C, hC⟩ := lem_app_pl_elasticity_ii hα hβ0 hβ1
  obtain ⟨cE, CE, hcE, _, hE⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  have hW : ∀ m ∈ Ioo 0 (gammaOf N B), 0 ≤ Wpart β B (plSpec α c N) i m := by
    intro m hm
    have hEp : 0 < Efun β m :=
      lt_of_lt_of_le (mul_pos hcE (lt_min hm.1 one_pos)) (hE m hm.1).1
    have hθ : 0 ≤ thetaN β B (plSpec α c N) m := by
      have := (hC N B c hN hB hc m hm).2
      nlinarith
    have hJ := (vm_J_le hα hN hB hc i hm).1
    exact mul_nonneg hJ hθ
  exact mul_nonneg (mul_nonneg (hW x hx) (hW y hy))
    (vm_DLag_nonneg hβ0 (vm_Qm_pos hβ0 hβ1 hx.1).le
      (vm_Qm_pos hβ0 hβ1 hy.1).le ℓ)

private lemma vm_kernel_error {a d t : ℝ} (ha : 0 ≤ a) (ht : t < 1 / 2)
    (hd0 : 0 ≤ 1 - d) (hd : 1 - d ≤ t) :
    0 ≤ a / d - a ∧ a / d - a ≤ 2 * t * a := by
  have hdp : 0 < d := by linarith
  have ht0 : 0 ≤ t := hd0.trans hd
  constructor
  · rw [sub_nonneg, le_div_iff₀ hdp]
    nlinarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hdp]
    have h1 : 0 ≤ t * (2 * d - 1) := mul_nonneg ht0 (by linarith)
    have h2 : 0 ≤ a * (d - (1 - t)) := mul_nonneg ha (by linarith)
    have h3 := mul_nonneg ha h1
    nlinarith

private lemma vm_head_kernel_error {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β)
    (hβ1 : β < 1) :
    ∃ C : ℝ, ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c →
      ∀ (i : Fin N) (ℓ : ℤ) (x y δ : ℝ),
        x ∈ Ioo 0 (gammaOf N B) → y ∈ Ioo 0 (gammaOf N B) →
        x ≤ δ → y ≤ δ → δ ≤ 1 → C * δ + 2 * δ / gammaOf N B < 1 / 2 →
        0 ≤ lagIntegrand β B (plSpec α c N) i ℓ x y -
          lagNumer β B (plSpec α c N) i ℓ x y ∧
        lagIntegrand β B (plSpec α c N) i ℓ x y -
          lagNumer β B (plSpec α c N) i ℓ x y ≤
          2 * (C * δ + 2 * δ / gammaOf N B) * lagNumer β B (plSpec α c N) i ℓ x y := by
  obtain ⟨C, hC⟩ := lem_app_pl_determinant_iv hβ0 hβ1
  refine ⟨C, ?_⟩
  intro N B c hN hB hc i ℓ x y δ hx hy hxδ hyδ hδ ht
  exact vm_kernel_error (vm_lagNumer_nonneg hα hβ0 hβ1 hN hB hc i ℓ hx hy) ht
    (lem_app_pl_determinant_iii hα hβ0 hβ1 N B c hN hB hc ℓ x y hx hy).1
    (hC α hα N B c hN hB hc ℓ x y δ hx hy hxδ hyδ hδ)

private lemma vm_head_tail_kernel_error {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β)
    (hβ1 : β < 1) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) (i : Fin N) (ℓ : ℤ) {x y δ M : ℝ}
    (hx : x ∈ Ioo 0 (gammaOf N B)) (hy : y ∈ Ioo 0 (gammaOf N B))
    (hxδ : x ≤ δ) (hδM : δ < M) (hMy : M ≤ y)
    (ht : δ / M + 2 * δ / gammaOf N B < 1 / 2) :
    0 ≤ lagIntegrand β B (plSpec α c N) i ℓ x y -
      lagNumer β B (plSpec α c N) i ℓ x y ∧
    lagIntegrand β B (plSpec α c N) i ℓ x y -
      lagNumer β B (plSpec α c N) i ℓ x y ≤
      2 * (δ / M + 2 * δ / gammaOf N B) * lagNumer β B (plSpec α c N) i ℓ x y := by
  have hγ : 0 < gammaOf N B := hx.1.trans hx.2
  have hδ : 0 ≤ δ := hx.1.le.trans hxδ
  have hM : 0 < M := lt_of_lt_of_le hx.1 (hxδ.trans hδM.le)
  have hxy : x ≤ y := hxδ.trans (hδM.le.trans hMy)
  obtain ⟨hd0, hd⟩ := lem_app_pl_determinant_iii hα hβ0 hβ1 N B c hN hB hc ℓ x y hx hy
  rw [min_eq_left hxy, max_eq_right hxy] at hd
  have hratio : x / y ≤ δ / M :=
    (div_le_div_of_nonneg_right hxδ hy.1.le).trans (div_le_div_of_nonneg_left hδ hM hMy)
  apply vm_kernel_error (vm_lagNumer_nonneg hα hβ0 hβ1 hN hB hc i ℓ hx hy) ht hd0
  exact hd.trans (add_le_add hratio (div_le_div_of_nonneg_right (by linarith) hγ.le))

private lemma vm_off_strip_ratio {x y Rr : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hR : 1 < Rr) (hout : ¬ (Rr⁻¹ ≤ x / y ∧ x / y ≤ Rr)) :
    min x y / max x y ≤ Rr⁻¹ := by
  have hR0 : 0 < Rr := by linarith
  by_cases hxy : x ≤ y
  · rw [min_eq_left hxy, max_eq_right hxy]
    by_contra hn
    apply hout
    exact ⟨le_of_not_ge hn, (div_le_one hy).2 hxy |>.trans hR.le⟩
  · have hyx : y ≤ x := le_of_not_ge hxy
    rw [min_eq_right hyx, max_eq_left hyx]
    have hratio : Rr < x / y := by
      by_contra hn
      apply hout
      refine ⟨?_, le_of_not_gt hn⟩
      have h1 : Rr⁻¹ ≤ 1 := (inv_le_one₀ hR0).2 hR.le
      exact h1.trans ((one_le_div hy).2 hyx)
    rw [div_le_iff₀ hx]
    have hmul : Rr * y < x := (lt_div_iff₀ hy).1 hratio
    have := mul_le_mul_of_nonneg_left hmul.le (inv_pos.2 hR0).le
    simpa only [← mul_assoc, inv_mul_cancel₀ hR0.ne', one_mul] using this

private lemma vm_far_kernel_error {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β)
    (hβ1 : β < 1) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) (i : Fin N) (ℓ : ℤ) {x y Rr η : ℝ}
    (hx : x ∈ Ioo 0 (gammaOf N B)) (hy : y ∈ Ioo 0 (gammaOf N B))
    (hxη : x ≤ η * gammaOf N B) (hR : 1 < Rr)
    (hout : ¬ (Rr⁻¹ ≤ x / y ∧ x / y ≤ Rr)) (ht : Rr⁻¹ + 2 * η < 1 / 2) :
    0 ≤ lagIntegrand β B (plSpec α c N) i ℓ x y -
      lagNumer β B (plSpec α c N) i ℓ x y ∧
    lagIntegrand β B (plSpec α c N) i ℓ x y -
      lagNumer β B (plSpec α c N) i ℓ x y ≤
      2 * (Rr⁻¹ + 2 * η) * lagNumer β B (plSpec α c N) i ℓ x y := by
  have hγ : 0 < gammaOf N B := hx.1.trans hx.2
  obtain ⟨hd0, hd⟩ := lem_app_pl_determinant_iii hα hβ0 hβ1 N B c hN hB hc ℓ x y hx hy
  have hmin : 2 * min x y / gammaOf N B ≤ 2 * η := by
    rw [div_le_iff₀ hγ]
    nlinarith [min_le_left x y]
  exact vm_kernel_error (vm_lagNumer_nonneg hα hβ0 hβ1 hN hB hc i ℓ hx hy) ht hd0
    (hd.trans (add_le_add (vm_off_strip_ratio hx.1 hy.1 hR hout) hmin))

private lemma vm_good_determinant_bound {α β : ℝ} (hα : 0 < α)
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c →
      ∀ (ℓ : ℤ) (δ η Rr x y : ℝ), 0 < δ → δ ≤ 1 → 0 < η → η < 1 → 1 < Rr →
      1 ≤ gammaOf N B → x ∈ Ioo 0 (η * gammaOf N B) →
      y ∈ Ioo 0 (η * gammaOf N B) → x ∉ Ioo δ 2 → y ∉ Ioo δ 2 →
      (x, y) ∉ stripSet η Rr 1 (gammaOf N B) →
      1 - deltaN β B (plSpec α c N) ℓ x y ≤ C * δ + Rr⁻¹ + 2 * η := by
  obtain ⟨C, hC⟩ := lem_app_pl_determinant_iv hβ0 hβ1
  refine ⟨|C| + 3, by positivity, ?_⟩
  intro N B c hN hB hc ℓ δ η Rr x y hδ hδ1 hη hη1 hR hγ hx hy hxm hym hout
  have hγ0 : 0 < gammaOf N B := by linarith
  have hx' : x ∈ Ioo 0 (gammaOf N B) := ⟨hx.1, hx.2.trans (by nlinarith)⟩
  have hy' : y ∈ Ioo 0 (gammaOf N B) := ⟨hy.1, hy.2.trans (by nlinarith)⟩
  have hR0 : 0 ≤ Rr⁻¹ := (inv_pos.2 (by linarith : 0 < Rr)).le
  by_cases hxd : x ≤ δ
  · by_cases hyd : y ≤ δ
    · have hh := hC α hα N B c hN hB hc ℓ x y δ hx' hy' hxd hyd hδ1
      have hd : 2 * δ / gammaOf N B ≤ 2 * δ := div_le_self (by positivity) hγ
      have hCd : C * δ ≤ |C| * δ := mul_le_mul_of_nonneg_right (le_abs_self C) hδ.le
      linarith
    · have hy2 : 2 ≤ y := le_of_not_gt fun hh => hym ⟨lt_of_not_ge hyd, hh⟩
      have hm : min x y ≤ δ := (min_le_left x y).trans hxd
      have hmax : 1 ≤ max x y := by linarith [le_max_right x y]
      have hmax0 : 0 < max x y := by linarith
      have hr : min x y / max x y ≤ δ := by
        rw [div_le_iff₀ hmax0]
        nlinarith
      have ht : 2 * min x y / gammaOf N B ≤ 2 * δ :=
        (div_le_div_of_nonneg_right (by linarith) hγ0.le).trans (div_le_self (by positivity) hγ)
      have hd := (lem_app_pl_determinant_iii hα hβ0 hβ1 N B c hN hB hc ℓ x y hx' hy').2
      have := mul_nonneg (abs_nonneg C) hδ.le
      linarith
  · have hx2 : 2 ≤ x := le_of_not_gt fun hh => hxm ⟨lt_of_not_ge hxd, hh⟩
    by_cases hyd : y ≤ δ
    · have hm : min x y ≤ δ := (min_le_right x y).trans hyd
      have hmax : 1 ≤ max x y := by linarith [le_max_left x y]
      have hmax0 : 0 < max x y := by linarith
      have hr : min x y / max x y ≤ δ := by
        rw [div_le_iff₀ hmax0]
        nlinarith
      have ht : 2 * min x y / gammaOf N B ≤ 2 * δ :=
        (div_le_div_of_nonneg_right (by linarith) hγ0.le).trans (div_le_self (by positivity) hγ)
      have hd := (lem_app_pl_determinant_iii hα hβ0 hβ1 N B c hN hB hc ℓ x y hx' hy').2
      have := mul_nonneg (abs_nonneg C) hδ.le
      linarith
    · have hy2 : 2 ≤ y := le_of_not_gt fun hh => hym ⟨lt_of_not_ge hyd, hh⟩
      have hr : ¬ (Rr⁻¹ ≤ x / y ∧ x / y ≤ Rr) := by
        intro hh
        exact hout ⟨by linarith, hx.2, by linarith, hy.2, hh.1, hh.2⟩
      have hratio := vm_off_strip_ratio hx.1 hy.1 hR hr
      have ht : 2 * min x y / gammaOf N B ≤ 2 * η := by
        rw [div_le_iff₀ hγ0]
        nlinarith [min_le_left x y, hx.2]
      have hd := (lem_app_pl_determinant_iii hα hβ0 hβ1 N B c hN hB hc ℓ x y hx' hy').2
      have := mul_pos (by positivity : 0 < |C| + 3) hδ
      linarith

private lemma vm_region_bound {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β)
    (hβ1 : β < 1) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) (i : Fin N) {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hsub : S ⊆ Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B))
    {F : ℤ → ℝ × ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hF : ∀ ℓ, IntegrableOn (F ℓ) S)
    (hpoint : ∀ ℓ p, p ∈ S → 0 ≤ F ℓ p ∧
      F ℓ p ≤ K * lagNumer β B (plSpec α c N) i ℓ p.1 p.2) :
    Summable (fun ℓ => ∫ p in S, F ℓ p) ∧
      0 ≤ (Real.pi ^ 2)⁻¹ * ∑' ℓ, ∫ p in S, F ℓ p ∧
      (Real.pi ^ 2)⁻¹ * (∑' ℓ, ∫ p in S, F ℓ p) ≤ K * vFlat β B (plSpec α c N) i := by
  let Ω := Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B)
  let A : ℤ → ℝ × ℝ → ℝ := fun ℓ p => lagNumer β B (plSpec α c N) i ℓ p.1 p.2
  have hΩ : MeasurableSet Ω := measurableSet_Ioo.prod measurableSet_Ioo
  have hage := lem_app_pl_age_iv hα hβ0 hβ1 N B c hN hB hc i
  have hA : ∀ ℓ, IntegrableOn (A ℓ) Ω := hage.1
  have hA0 : ∀ ℓ p, p ∈ Ω → 0 ≤ A ℓ p := fun ℓ p hp =>
    vm_lagNumer_nonneg hα hβ0 hβ1 hN hB hc i ℓ hp.1 hp.2
  have hsum : HasSum (fun ℓ => ∫ p in Ω, A ℓ p)
      (Real.pi ^ 2 * vFlat β B (plSpec α c N) i) := by
    convert hage.2.1 using 1
    ext ℓ
    dsimp only [Ω]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact integral_prod _ (by rw [Measure.prod_restrict]; exact hA ℓ)
  have hnn : ∀ ℓ, 0 ≤ ∫ p in S, F ℓ p := fun ℓ =>
    setIntegral_nonneg hS fun p hp => (hpoint ℓ p hp).1
  have hle : ∀ ℓ, (∫ p in S, F ℓ p) ≤ K * ∫ p in Ω, A ℓ p := by
    intro ℓ
    calc (∫ p in S, F ℓ p) ≤ ∫ p in S, K * A ℓ p :=
        setIntegral_mono_on (hF ℓ) ((hA ℓ).mono_set hsub |>.const_mul K) hS
          (fun p hp => (hpoint ℓ p hp).2)
      _ ≤ ∫ p in Ω, K * A ℓ p :=
        setIntegral_mono_set ((hA ℓ).const_mul K)
          (ae_restrict_of_forall_mem hΩ fun p hp => mul_nonneg hK (hA0 ℓ p hp))
          (Eventually.of_forall hsub)
      _ = K * ∫ p in Ω, A ℓ p := integral_const_mul _ _
  have hs := Summable.of_nonneg_of_le hnn hle (hsum.summable.mul_left K)
  refine ⟨hs, mul_nonneg (by positivity) (tsum_nonneg hnn), ?_⟩
  have hbound := hasSum_le hle hs.hasSum (hsum.mul_left K)
  calc (Real.pi ^ 2)⁻¹ * (∑' ℓ, ∫ p in S, F ℓ p)
      ≤ (Real.pi ^ 2)⁻¹ * (K * (Real.pi ^ 2 * vFlat β B (plSpec α c N) i)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = K * vFlat β B (plSpec α c N) i := by
      have hp : Real.pi ^ 2 ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
      field_simp

private lemma vm_region_error_bound {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β)
    (hβ1 : β < 1) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) (i : Fin N) {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hsub : S ⊆ Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B))
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 1 / 2)
    (hclose : ∀ ℓ p, p ∈ S → 1 - deltaN β B (plSpec α c N) ℓ p.1 p.2 ≤ t) :
    Summable (fun ℓ => ∫ p in S,
      (lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 -
        lagNumer β B (plSpec α c N) i ℓ p.1 p.2)) ∧
      0 ≤ (Real.pi ^ 2)⁻¹ * ∑' ℓ, ∫ p in S,
        (lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 -
          lagNumer β B (plSpec α c N) i ℓ p.1 p.2) ∧
      (Real.pi ^ 2)⁻¹ * (∑' ℓ, ∫ p in S,
        (lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 -
          lagNumer β B (plSpec α c N) i ℓ p.1 p.2)) ≤
        2 * t * vFlat β B (plSpec α c N) i := by
  have hage := lem_app_pl_age_iv hα hβ0 hβ1 N B c hN hB hc i
  apply vm_region_bound hα hβ0 hβ1 hN hB hc i hS hsub (mul_nonneg (by norm_num) ht0)
  · intro ℓ
    exact ((hage.2.2.1 ℓ).mono_set hsub).sub ((hage.1 ℓ).mono_set hsub)
  · intro ℓ p hp
    have hm := hsub hp
    exact vm_kernel_error (vm_lagNumer_nonneg hα hβ0 hβ1 hN hB hc i ℓ hm.1 hm.2)
      ht (lem_app_pl_determinant_iii hα hβ0 hβ1 N B c hN hB hc ℓ p.1 p.2 hm.1 hm.2).1
      (hclose ℓ p hp)

private lemma vm_good_region_bound {α β : ℝ} (hα : 0 < α)
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c →
      ∀ (i : Fin N) (δ η Rr : ℝ), 0 < δ → δ ≤ 1 → 0 < η → η < 1 → 1 < Rr →
      1 ≤ gammaOf N B → C * δ + Rr⁻¹ + 2 * η < 1 / 2 →
      let L := Ioo 0 (η * gammaOf N B)
      let J := Ioo δ 2
      let G := (L ×ˢ L) \ ((J ×ˢ L) ∪ (L ×ˢ J) ∪ stripSet η Rr 1 (gammaOf N B))
      (Real.pi ^ 2)⁻¹ * (∑' ℓ : ℤ, ∫ p in G,
        (lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 -
          lagNumer β B (plSpec α c N) i ℓ p.1 p.2)) ≤
        2 * (C * δ + Rr⁻¹ + 2 * η) * vFlat β B (plSpec α c N) i := by
  obtain ⟨C, hC, hgood⟩ := vm_good_determinant_bound hα hβ0 hβ1
  refine ⟨C, hC, ?_⟩
  intro N B c hN hB hc i δ η Rr hδ hδ1 hη hη1 hR hγ ht L J G
  have hγ0 : 0 < gammaOf N B := by linarith
  have hL : L ⊆ Ioo 0 (gammaOf N B) := fun m hm => ⟨hm.1, hm.2.trans (by nlinarith)⟩
  have hG : MeasurableSet G :=
    (measurableSet_Ioo.prod measurableSet_Ioo).diff
      (((measurableSet_Ioo.prod measurableSet_Ioo).union
        (measurableSet_Ioo.prod measurableSet_Ioo)).union (vm_strip_meas η Rr 1 (gammaOf N B)))
  have hsub : G ⊆ Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B) :=
    fun _ hp => ⟨hL hp.1.1, hL hp.1.2⟩
  have hclose : ∀ ℓ p, p ∈ G →
      1 - deltaN β B (plSpec α c N) ℓ p.1 p.2 ≤ C * δ + Rr⁻¹ + 2 * η := by
    intro ℓ p hp
    have hxmid : p.1 ∉ J := fun hh => hp.2 (Or.inl (Or.inl ⟨hh, hp.1.2⟩))
    have hymid : p.2 ∉ J := fun hh => hp.2 (Or.inl (Or.inr ⟨hp.1.1, hh⟩))
    have hout : p ∉ stripSet η Rr 1 (gammaOf N B) := fun hh => hp.2 (Or.inr hh)
    exact hgood N B c hN hB hc ℓ δ η Rr p.1 p.2 hδ hδ1 hη hη1 hR hγ
      hp.1.1 hp.1.2 hxmid hymid hout
  exact (vm_region_error_bound hα hβ0 hβ1 hN hB hc i hG hsub
    (by positivity) ht hclose).2.2

private lemma vm_interior_kernel_bound {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β)
    (hβ1 : β < 1) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c →
      ∀ (i : Fin N) (ℓ : ℤ) (x y : ℝ),
        x ∈ Ioo 0 (η * gammaOf N B) → y ∈ Ioo 0 (η * gammaOf N B) →
        0 ≤ lagIntegrand β B (plSpec α c N) i ℓ x y ∧
          lagIntegrand β B (plSpec α c N) i ℓ x y ≤
            K * lagNumer β B (plSpec α c N) i ℓ x y := by
  obtain ⟨cα, hcα, hchain⟩ := lem_app_pl_determinant_ii_chain hα
  let k := cα * (1 - η) ^ 2
  have hk : 0 < k := mul_pos hcα (sq_pos_of_pos (by linarith))
  refine ⟨k⁻¹, inv_pos.2 hk, ?_⟩
  intro N B c hN hB hc i ℓ x y hx hy
  have hγ : 0 < gammaOf N B := by
    unfold gammaOf
    exact div_pos (by exact_mod_cast hN) (by exact_mod_cast hB)
  have hηγ : η * gammaOf N B < gammaOf N B := by nlinarith
  have hx' : x ∈ Ioo 0 (gammaOf N B) := ⟨hx.1, hx.2.trans hηγ⟩
  have hy' : y ∈ Ioo 0 (gammaOf N B) := ⟨hy.1, hy.2.trans hηγ⟩
  have h1 : 1 - η ≤ 1 - x / gammaOf N B := by
    have := (div_lt_iff₀ hγ).2 hx.2
    linarith
  have h2 : 1 - η ≤ 1 - y / gammaOf N B := by
    have := (div_lt_iff₀ hγ).2 hy.2
    linarith
  have hprod : (1 - η) ^ 2 ≤ (1 - x / gammaOf N B) * (1 - y / gammaOf N B) := by
    simpa only [pow_two] using mul_le_mul h1 h2 (by linarith : 0 ≤ 1 - η) (by linarith)
  have hd : k ≤ deltaN β B (plSpec α c N) ℓ x y :=
    (mul_le_mul_of_nonneg_left hprod hcα.le).trans
      ((hchain N B c hN hB hc x y hx' hy').trans
        (lem_app_pl_determinant_ii hα hβ0 hβ1 N B c hN hB hc ℓ x y hx' hy'))
  have ha := vm_lagNumer_nonneg hα hβ0 hβ1 hN hB hc i ℓ hx' hy'
  refine ⟨div_nonneg ha (hk.le.trans hd), ?_⟩
  change lagNumer β B (plSpec α c N) i ℓ x y / deltaN β B (plSpec α c N) ℓ x y ≤ _
  calc _ ≤ lagNumer β B (plSpec α c N) i ℓ x y / k :=
      div_le_div_of_nonneg_left ha hk hd
    _ = _ := by ring

private lemma vm_interior_square_bound {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β)
    (hβ1 : β < 1) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c →
      ∀ i : Fin N, 0 ≤ vIJ β B (plSpec α c N) i
          (Ioo 0 (η * gammaOf N B)) (Ioo 0 (η * gammaOf N B)) ∧
        vIJ β B (plSpec α c N) i
          (Ioo 0 (η * gammaOf N B)) (Ioo 0 (η * gammaOf N B)) ≤
            K * vFlat β B (plSpec α c N) i := by
  obtain ⟨K, hK, hpoint⟩ := vm_interior_kernel_bound hα hβ0 hβ1 η hη0 hη1
  refine ⟨K, hK, ?_⟩
  intro N B c hN hB hc i
  let I := Ioo 0 (η * gammaOf N B)
  have hγ : 0 < gammaOf N B := by
    unfold gammaOf
    exact div_pos (by exact_mod_cast hN) (by exact_mod_cast hB)
  have hsub : I ×ˢ I ⊆ Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B) := by
    have hh : I ⊆ Ioo 0 (gammaOf N B) := fun m hm =>
      ⟨hm.1, hm.2.trans (by nlinarith)⟩
    exact Set.prod_mono hh hh
  have hi := fun ℓ => ((lem_app_pl_age_iv hα hβ0 hβ1 N B c hN hB hc i).2.2.1 ℓ).mono_set hsub
  have hb := vm_region_bound hα hβ0 hβ1 hN hB hc i
    (measurableSet_Ioo.prod measurableSet_Ioo) hsub hK.le hi
    (fun ℓ p hp => hpoint N B c hN hB hc i ℓ p.1 p.2 hp.1 hp.2)
  have heq : (Real.pi ^ 2)⁻¹ * (∑' ℓ : ℤ, ∫ p in I ×ˢ I,
      lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2) =
      vIJ β B (plSpec α c N) i I I := by
    unfold vIJ lagTerm
    congr 1
    apply tsum_congr
    intro ℓ
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact integral_prod _ (by rw [Measure.prod_restrict]; exact hi ℓ)
  rw [heq] at hb
  exact hb.2

private lemma vm_compact_kernel_bound {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β)
    (hβ1 : β < 1) {δ M : ℝ} (hδ : 0 < δ) (hδM : δ < M) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c →
      2 * M + 2 ≤ gammaOf N B → ∀ (i : Fin N) (ℓ : ℤ) (x y : ℝ),
        x ∈ Ioo δ M → y ∈ Ioo δ M →
        0 ≤ lagIntegrand β B (plSpec α c N) i ℓ x y ∧
          lagIntegrand β B (plSpec α c N) i ℓ x y ≤
            K * partMN B (plSpec α c N) (1 / plSpec α c N i) *
              DLag β (Qm β x) (Qm β y) ℓ := by
  obtain ⟨K0, hK0, hkernel⟩ := vm_interior_kernel_bound hα hβ0 hβ1 (1 / 2)
    (by norm_num) (by norm_num)
  obtain ⟨C0, hC0⟩ := lem_app_pl_elasticity_ii hα hβ0 hβ1
  obtain ⟨cE, CE, hcE, _, hE⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  let Cθ := max C0 1 * (2 + 1 / δ)
  have hCθ : 0 < Cθ := mul_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) (by positivity)
  refine ⟨K0 * Cθ ^ 2 / δ ^ 2, by positivity, ?_⟩
  intro N B c hN hB hc hγ i ℓ x y hx hy
  let m0 := partMN B (plSpec α c N) (1 / plSpec α c N i)
  have hm0 : 0 < m0 := (vm_m0_facts (α := α) hN hB hc i).1.1
  have hM : 0 < M := hδ.trans hδM
  have hsmall : ∀ m ∈ Ioo δ M, m ∈ Ioo 0 ((1 / 2) * gammaOf N B) :=
    fun m hm => ⟨hδ.trans hm.1, by linarith [hm.2]⟩
  have hW : ∀ m ∈ Ioo δ M,
      0 ≤ Wpart β B (plSpec α c N) i m ∧
        Wpart β B (plSpec α c N) i m ≤ Cθ * Real.sqrt m0 / δ := by
    intro m hm
    have hm' : m ∈ Ioo 0 (gammaOf N B) := ⟨hδ.trans hm.1, by linarith [hm.2]⟩
    have hEpos : 0 < Efun β m :=
      lt_of_lt_of_le (mul_pos hcE (lt_min hm'.1 one_pos)) (hE m hm'.1).1
    have hθ0 : 0 ≤ thetaN β B (plSpec α c N) m := by
      have := (hC0 N B c hN hB hc m hm').2
      nlinarith
    have hθ : thetaN β B (plSpec α c N) m ≤ Cθ := by
      have hγm : 0 < gammaOf N B - m := by linarith [hm.2]
      have hmp := hm'.1
      have h1 : 1 / m ≤ 1 / δ := one_div_le_one_div_of_le hδ hm.1.le
      have h2 : 1 / (gammaOf N B - m) ≤ 1 := by
        rw [div_le_one (by linarith [hm.2] : 0 < gammaOf N B - m)]
        linarith [hm.2]
      have h3 : 0 ≤ 1 + 1 / m + 1 / (gammaOf N B - m) := by positivity
      calc _ ≤ C0 * (1 + 1 / m + 1 / (gammaOf N B - m)) :=
          (hC0 N B c hN hB hc m hm').1
        _ ≤ max C0 1 * (1 + 1 / m + 1 / (gammaOf N B - m)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) h3
        _ ≤ Cθ := mul_le_mul_of_nonneg_left (by linarith) (by linarith [le_max_right C0 1])
    have hJ := vm_J_le hα hN hB hc i hm'
    have hJup : Jrow B (plSpec α c N) i m ≤ Real.sqrt m0 / δ := by
      calc _ ≤ Real.sqrt (vmG m0 m) := hJ.2
        _ ≤ Real.sqrt (m0 / m ^ 2) := Real.sqrt_le_sqrt (min_le_right _ _)
        _ = Real.sqrt m0 / m := by
          rw [Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hm'.1.le]
        _ ≤ Real.sqrt m0 / δ := div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hδ hm.1.le
    constructor
    · exact mul_nonneg hJ.1 hθ0
    · change Jrow B (plSpec α c N) i m * thetaN β B (plSpec α c N) m ≤ _
      calc _ ≤ (Real.sqrt m0 / δ) * Cθ :=
          mul_le_mul hJup hθ hθ0 (by positivity)
        _ = _ := by ring
  obtain ⟨hx0, hxW⟩ := hW x hx
  obtain ⟨hy0, hyW⟩ := hW y hy
  have hWW : Wpart β B (plSpec α c N) i x * Wpart β B (plSpec α c N) i y ≤
      Cθ ^ 2 * m0 / δ ^ 2 := by
    calc _ ≤ (Cθ * Real.sqrt m0 / δ) * (Cθ * Real.sqrt m0 / δ) :=
        mul_le_mul hxW hyW hy0 (by positivity)
      _ = Cθ ^ 2 * (Real.sqrt m0) ^ 2 / δ ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hm0.le]
  have hD := vm_DLag_nonneg hβ0 (vm_Qm_pos hβ0 hβ1 (hsmall x hx).1).le
    (vm_Qm_pos hβ0 hβ1 (hsmall y hy).1).le ℓ
  have hk := hkernel N B c hN hB hc i ℓ x y (hsmall x hx) (hsmall y hy)
  refine ⟨hk.1, hk.2.trans ?_⟩
  calc K0 * lagNumer β B (plSpec α c N) i ℓ x y
      ≤ K0 * (Cθ ^ 2 * m0 / δ ^ 2 * DLag β (Qm β x) (Qm β y) ℓ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hWW hD) hK0.le
    _ = _ := by ring

private lemma vm_compact_square_bound {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β)
    (hβ1 : β < 1) {δ M : ℝ} (hδ : 0 < δ) (hδM : δ < M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c →
      2 * M + 2 ≤ gammaOf N B → ∀ i : Fin N,
        0 ≤ vIJ β B (plSpec α c N) i (Ioo δ M) (Ioo δ M) ∧
          vIJ β B (plSpec α c N) i (Ioo δ M) (Ioo δ M) ≤
            K * partMN B (plSpec α c N) (1 / plSpec α c N i) := by
  classical
  obtain ⟨K0, hK0, hkernel⟩ := vm_compact_kernel_bound hα hβ0 hβ1 hδ hδM
  obtain ⟨CD, hCD0, hCD⟩ := vm_Dsum hβ0 hβ1
  let S := Ioo δ M ×ˢ Ioo δ M
  have hS : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
  haveI : IsFiniteMeasure (volume.restrict S) := ⟨by
    simp only [Measure.restrict_apply_univ, S, Measure.volume_eq_prod,
      Measure.prod_prod, Real.volume_Ioo]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top⟩
  refine ⟨(Real.pi ^ 2)⁻¹ * (volume S).toReal * K0 * CD, by positivity, ?_⟩
  intro N B c hN hB hc hγ i
  let m0 := partMN B (plSpec α c N) (1 / plSpec α c N i)
  have hm0 : 0 < m0 := (vm_m0_facts (α := α) hN hB hc i).1.1
  let F : ℤ → ℝ × ℝ → ℝ := fun ℓ p => lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2
  have hsub : S ⊆ Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B) := by
    intro p hp
    exact ⟨⟨hδ.trans hp.1.1, by linarith [hp.1.2]⟩,
      ⟨hδ.trans hp.2.1, by linarith [hp.2.2]⟩⟩
  have hF : ∀ ℓ, IntegrableOn (F ℓ) S := fun ℓ =>
    ((lem_app_pl_age_iv hα hβ0 hβ1 N B c hN hB hc i).2.2.1 ℓ).mono_set hsub
  have hpoint : ∀ ℓ p, p ∈ S → 0 ≤ F ℓ p ∧
      F ℓ p ≤ K0 * m0 * DLag β (Qm β p.1) (Qm β p.2) ℓ :=
    fun ℓ p hp => hkernel N B c hN hB hc hγ i ℓ p.1 p.2 hp.1 hp.2
  have hnn : ∀ ℓ, 0 ≤ ∫ p in S, F ℓ p := fun ℓ =>
    setIntegral_nonneg hS fun p hp => (hpoint ℓ p hp).1
  have hfin : ∀ s : Finset ℤ, (∑ ℓ ∈ s, ∫ p in S, F ℓ p) ≤
      (volume S).toReal * (K0 * m0 * CD) := by
    intro s
    rw [← integral_finsetSum s (fun ℓ _ => hF ℓ)]
    calc
      (∫ p in S, ∑ ℓ ∈ s, F ℓ p) ≤ ∫ p in S, K0 * m0 * CD := by
        apply setIntegral_mono_on (integrable_finsetSum s (fun ℓ _ => hF ℓ))
          (integrable_const _) hS
        intro p hp
        have hp1 : 0 < p.1 := hδ.trans hp.1.1
        have hp2 : 0 < p.2 := hδ.trans hp.2.1
        have hD0 : ∀ ℓ, 0 ≤ DLag β (Qm β p.1) (Qm β p.2) ℓ := fun ℓ =>
          vm_DLag_nonneg hβ0 (vm_Qm_pos hβ0 hβ1 hp1).le (vm_Qm_pos hβ0 hβ1 hp2).le ℓ
        have hs := (lem_app_pl_age_iii hβ0 hβ1 p.1 p.2 hp1 hp2).2.summable
        have hd := hCD p.1 p.2 hp1 hp2
        rw [← ENNReal.ofReal_tsum_of_nonneg hD0 hs] at hd
        have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hd
        rw [ENNReal.toReal_ofReal (tsum_nonneg hD0), ENNReal.toReal_ofReal hCD0] at hreal
        calc (∑ ℓ ∈ s, F ℓ p) ≤ ∑ ℓ ∈ s, K0 * m0 * DLag β (Qm β p.1) (Qm β p.2) ℓ :=
            Finset.sum_le_sum fun ℓ _ => (hpoint ℓ p hp).2
          _ = K0 * m0 * ∑ ℓ ∈ s, DLag β (Qm β p.1) (Qm β p.2) ℓ := by rw [Finset.mul_sum]
          _ ≤ K0 * m0 * ∑' ℓ, DLag β (Qm β p.1) (Qm β p.2) ℓ :=
            mul_le_mul_of_nonneg_left (hs.sum_le_tsum s (fun ℓ _ => hD0 ℓ)) (by positivity)
          _ ≤ K0 * m0 * CD := mul_le_mul_of_nonneg_left hreal (by positivity)
      _ = _ := by simp only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul]
  have heq : (Real.pi ^ 2)⁻¹ * (∑' ℓ, ∫ p in S, F ℓ p) =
      vIJ β B (plSpec α c N) i (Ioo δ M) (Ioo δ M) := by
    unfold vIJ lagTerm
    congr 1
    apply tsum_congr
    intro ℓ
    dsimp only [S]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact integral_prod _ (by rw [Measure.prod_restrict]; exact hF ℓ)
  rw [← heq]
  refine ⟨mul_nonneg (by positivity) (tsum_nonneg hnn), ?_⟩
  calc _ ≤ (Real.pi ^ 2)⁻¹ * ((volume S).toReal * (K0 * m0 * CD)) :=
      mul_le_mul_of_nonneg_left (Real.tsum_le_of_sum_le hnn hfin) (by positivity)
    _ = _ := by ring

private lemma vm_lag_swap (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ)
    (i : Fin N) (k : ℕ) (x y : ℝ) :
    lagIntegrand β B μ i (-((k : ℤ) + 1)) x y =
      lagIntegrand β B μ i ((k : ℤ) + 1) y x := by
  have hpos : (0 : ℤ) ≤ (k : ℤ) + 1 := by omega
  have hneg : ¬ (0 : ℤ) ≤ -((k : ℤ) + 1) := by omega
  have hT : TNpart B μ x y = TNpart B μ y x := by
    unfold TNpart
    congr 1
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  simp only [lagIntegrand, lagNumer, deltaN, DLag, MLag, if_pos hpos,
    if_neg hneg, neg_neg, hT]
  ring

private lemma vm_vPart_eq_vIJ {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (N B : ℕ) (c : ℝ) (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) (i : Fin N)
    (hzero : CbarPart β B (plSpec α c N) i 0 = 1) :
    vPart β B (plSpec α c N) i = vIJ β B (plSpec α c N) i
      (Ioo 0 (gammaOf N B)) (Ioo 0 (gammaOf N B)) := by
  have hage := lem_app_pl_age_iv hα hβ0 hβ1 N B c hN hB hc i
  let f : ℤ → ℝ := CbarPart β B (plSpec α c N) i
  have hs : Summable f := hage.2.2.2.1.mul_left _
  have hsym : ∀ k : ℕ, f (-((k : ℤ) + 1)) = f ((k : ℤ) + 1) := by
    intro k
    unfold f CbarPart lagTerm
    congr 1
    simp_rw [vm_lag_swap]
    symm
    apply integral_integral_swap
    rw [Measure.prod_restrict]
    exact hage.2.2.1 ((k : ℤ) + 1)
  have hp : Summable (fun k : ℕ => f ((k : ℤ) + 1)) :=
    hs.comp_injective (show Function.Injective (fun k : ℕ => (k : ℤ) + 1) from by
      intro a b h
      exact_mod_cast (add_right_cancel h : (a : ℤ) = (b : ℤ)))
  have hm : Summable (fun k : ℕ => f (-((k : ℤ) + 1))) := by simpa only [hsym] using hp
  have heq := tsum_of_add_one_of_neg_add_one hp hm
  simp only [hsym] at heq
  have hz : f 0 = 1 := hzero
  rw [hz] at heq
  unfold vIJ
  rw [← tsum_mul_left]
  change 1 + 2 * ∑' k : ℕ, f ((k : ℤ) + 1) = ∑' k : ℤ, f k
  rw [heq]
  ring

private lemma vm_flat_le_part {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (N B : ℕ) (c : ℝ) (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) (i : Fin N)
    (hzero : CbarPart β B (plSpec α c N) i 0 = 1) :
    0 ≤ vPart β B (plSpec α c N) i - vFlat β B (plSpec α c N) i := by
  rw [vm_vPart_eq_vIJ hα hβ0 hβ1 N B c hN hB hc i hzero]
  exact sub_nonneg.2 (lem_app_pl_age_iv hα hβ0 hβ1 N B c hN hB hc i).2.2.2.2.2

private lemma vm_kernel_order {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β)
    (hβ1 : β < 1) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) (i : Fin N) (ℓ : ℤ) {x y : ℝ}
    (hx : x ∈ Ioo 0 (gammaOf N B)) (hy : y ∈ Ioo 0 (gammaOf N B)) :
    0 ≤ lagNumer β B (plSpec α c N) i ℓ x y ∧
      lagNumer β B (plSpec α c N) i ℓ x y ≤
        lagIntegrand β B (plSpec α c N) i ℓ x y := by
  have hγ : 0 < gammaOf N B := hx.1.trans hx.2
  obtain ⟨k, hk, hchain⟩ := lem_app_pl_determinant_ii_chain hα
  have hx1 : 0 < 1 - x / gammaOf N B := by
    have := (div_lt_one hγ).2 hx.2
    linarith
  have hy1 : 0 < 1 - y / gammaOf N B := by
    have := (div_lt_one hγ).2 hy.2
    linarith
  have hd : 0 < deltaN β B (plSpec α c N) ℓ x y :=
    (mul_pos hk (mul_pos hx1 hy1)).trans_le
      ((hchain N B c hN hB hc x y hx hy).trans
        (lem_app_pl_determinant_ii hα hβ0 hβ1 N B c hN hB hc ℓ x y hx hy))
  have ha := vm_lagNumer_nonneg hα hβ0 hβ1 hN hB hc i ℓ hx hy
  refine ⟨ha, ?_⟩
  unfold lagIntegrand
  rw [le_div_iff₀ hd]
  have hd1 := (lem_app_pl_determinant_iii hα hβ0 hβ1 N B c hN hB hc ℓ x y hx hy).1
  nlinarith

private lemma vm_region_summability {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β)
    (hβ1 : β < 1) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) (i : Fin N) {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hsub : S ⊆ Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B)) :
    Summable (fun ℓ : ℤ => ∫ p in S, lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2) ∧
    Summable (fun ℓ : ℤ => ∫ p in S,
      (lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 -
        lagNumer β B (plSpec α c N) i ℓ p.1 p.2)) ∧
    0 ≤ (Real.pi ^ 2)⁻¹ * ∑' ℓ : ℤ, ∫ p in S,
      (lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 -
        lagNumer β B (plSpec α c N) i ℓ p.1 p.2) ∧
    (Real.pi ^ 2)⁻¹ * (∑' ℓ : ℤ, ∫ p in S,
      (lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 -
        lagNumer β B (plSpec α c N) i ℓ p.1 p.2)) ≤
      (Real.pi ^ 2)⁻¹ * ∑' ℓ : ℤ, ∫ p in S,
        lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 := by
  let Ω := Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B)
  let F : ℤ → ℝ × ℝ → ℝ := fun ℓ p => lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2
  let A : ℤ → ℝ × ℝ → ℝ := fun ℓ p => lagNumer β B (plSpec α c N) i ℓ p.1 p.2
  have ha := lem_app_pl_age_iv hα hβ0 hβ1 N B c hN hB hc i
  have hiF : ∀ ℓ, IntegrableOn (F ℓ) Ω := ha.2.2.1
  have hiA : ∀ ℓ, IntegrableOn (A ℓ) Ω := ha.1
  have hp : ∀ ℓ p, p ∈ Ω → 0 ≤ A ℓ p ∧ A ℓ p ≤ F ℓ p := fun ℓ p hm =>
    vm_kernel_order hα hβ0 hβ1 hN hB hc i ℓ hm.1 hm.2
  have hF0 : ∀ ℓ, 0 ≤ ∫ p in S, F ℓ p := fun ℓ =>
    setIntegral_nonneg hS fun p hm => (hp ℓ p (hsub hm)).1.trans (hp ℓ p (hsub hm)).2
  have hle : ∀ ℓ, (∫ p in S, F ℓ p) ≤ ∫ p in Ω, F ℓ p := fun ℓ =>
    setIntegral_mono_set (hiF ℓ)
      (ae_restrict_of_forall_mem (measurableSet_Ioo.prod measurableSet_Ioo)
        fun p hm => (hp ℓ p hm).1.trans (hp ℓ p hm).2) (Eventually.of_forall hsub)
  have hfull : Summable (fun ℓ => ∫ p in Ω, F ℓ p) := by
    convert ha.2.2.2.1 using 1
    ext ℓ
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact integral_prod _ (by rw [Measure.prod_restrict]; exact hiF ℓ)
  have hsF := Summable.of_nonneg_of_le hF0 hle hfull
  have hE0 : ∀ ℓ, 0 ≤ ∫ p in S, (F ℓ p - A ℓ p) := fun ℓ =>
    setIntegral_nonneg hS fun p hm => sub_nonneg.2 (hp ℓ p (hsub hm)).2
  have hEF : ∀ ℓ, (∫ p in S, (F ℓ p - A ℓ p)) ≤ ∫ p in S, F ℓ p := fun ℓ =>
    setIntegral_mono_on (((hiF ℓ).sub (hiA ℓ)).mono_set hsub)
      ((hiF ℓ).mono_set hsub) hS fun p hm => sub_le_self _ (hp ℓ p (hsub hm)).1
  have hsE := Summable.of_nonneg_of_le hE0 hEF hsF
  exact ⟨hsF, hsE, mul_nonneg (by positivity) (tsum_nonneg hE0),
    mul_le_mul_of_nonneg_left (hsE.tsum_le_tsum hEF hsF) (by positivity)⟩

private lemma vm_error_decomposition {κ : Type*} [Fintype κ]
    {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (N B : ℕ) (c : ℝ) (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) (i : Fin N)
    (hzero : CbarPart β B (plSpec α c N) i 0 = 1)
    (S : κ → Set (ℝ × ℝ)) (hS : ∀ k, MeasurableSet (S k))
    (hdisj : Pairwise (fun k j => Disjoint (S k) (S j)))
    (hcover : (⋃ k, S k) = Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B))
    (hsum : ∀ k, Summable (fun ℓ : ℤ => ∫ p in S k,
      (lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 -
        lagNumer β B (plSpec α c N) i ℓ p.1 p.2))) :
    vPart β B (plSpec α c N) i - vFlat β B (plSpec α c N) i =
      ∑ k, (Real.pi ^ 2)⁻¹ * ∑' ℓ : ℤ, ∫ p in S k,
        (lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 -
          lagNumer β B (plSpec α c N) i ℓ p.1 p.2) := by
  classical
  let Ω := Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B)
  let A : ℤ → ℝ × ℝ → ℝ := fun ℓ p => lagNumer β B (plSpec α c N) i ℓ p.1 p.2
  let F : ℤ → ℝ × ℝ → ℝ := fun ℓ p => lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2
  have ha := lem_app_pl_age_iv hα hβ0 hβ1 N B c hN hB hc i
  have hprod (ℓ : ℤ) : (∫ p in Ω, F ℓ p) =
      lagTerm β B (plSpec α c N) i (Ioo 0 (gammaOf N B)) (Ioo 0 (gammaOf N B)) ℓ := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact integral_prod _ (by rw [Measure.prod_restrict]; exact ha.2.2.1 ℓ)
  have hflat : HasSum (fun ℓ => ∫ p in Ω, A ℓ p)
      (Real.pi ^ 2 * vFlat β B (plSpec α c N) i) := by
    convert ha.2.1 using 1
    ext ℓ
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact integral_prod _ (by rw [Measure.prod_restrict]; exact ha.1 ℓ)
  have heq (ℓ : ℤ) : (∫ p in Ω, (F ℓ p - A ℓ p)) =
      ∑ k, ∫ p in S k, (F ℓ p - A ℓ p) := by
    change (∫ p in Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B), (F ℓ p - A ℓ p)) = _
    rw [← hcover]
    apply integral_iUnion_fintype hS hdisj
    intro k
    have hsub : S k ⊆ Ω := by
      change S k ⊆ Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B)
      rw [← hcover]
      exact subset_iUnion S k
    exact ((ha.2.2.1 ℓ).sub (ha.1 ℓ)).mono_set hsub
  have hsF : Summable (fun ℓ => ∫ p in Ω, F ℓ p) := by
    simpa only [hprod] using ha.2.2.2.1
  have hdiff : (∑' ℓ, ∫ p in Ω, (F ℓ p - A ℓ p)) =
      (∑' ℓ, ∫ p in Ω, F ℓ p) - Real.pi ^ 2 * vFlat β B (plSpec α c N) i := by
    have hiF : ∀ ℓ, IntegrableOn (F ℓ) Ω := ha.2.2.1
    have hiA : ∀ ℓ, IntegrableOn (A ℓ) Ω := ha.1
    simp_rw [integral_sub (hiF _) (hiA _)]
    rw [hsF.tsum_sub hflat.summable, hflat.tsum_eq]
  rw [vm_vPart_eq_vIJ hα hβ0 hβ1 N B c hN hB hc i hzero]
  unfold vIJ
  simp_rw [← hprod]
  have hp : Real.pi ^ 2 ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  calc
    _ = (Real.pi ^ 2)⁻¹ * ∑' ℓ, ∫ p in Ω, (F ℓ p - A ℓ p) := by
      rw [hdiff]; field_simp
    _ = (Real.pi ^ 2)⁻¹ * ∑ k, ∑' ℓ, ∫ p in S k, (F ℓ p - A ℓ p) := by
      simp_rw [heq]
      rw [Summable.tsum_finsetSum (fun k _ => hsum k)]
    _ = _ := by rw [Finset.mul_sum]

private lemma vm_error_cover_bound {κ : Type*} [Fintype κ]
    {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (N B : ℕ) (c : ℝ) (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) (i : Fin N)
    (hzero : CbarPart β B (plSpec α c N) i 0 = 1)
    (S : κ → Set (ℝ × ℝ)) (hS : ∀ k, MeasurableSet (S k))
    (hsub : ∀ k, S k ⊆ Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B))
    (hcover : Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B) ⊆ ⋃ k, S k) :
    vPart β B (plSpec α c N) i - vFlat β B (plSpec α c N) i ≤
      ∑ k, (Real.pi ^ 2)⁻¹ * ∑' ℓ : ℤ, ∫ p in S k,
        (lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 -
          lagNumer β B (plSpec α c N) i ℓ p.1 p.2) := by
  classical
  let Ω := Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B)
  let E : ℤ → ℝ × ℝ → ℝ := fun ℓ p =>
    lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 -
      lagNumer β B (plSpec α c N) i ℓ p.1 p.2
  have hΩ : MeasurableSet Ω := measurableSet_Ioo.prod measurableSet_Ioo
  have ha := lem_app_pl_age_iv hα hβ0 hβ1 N B c hN hB hc i
  have hi : ∀ ℓ, IntegrableOn (E ℓ) Ω := fun ℓ => (ha.2.2.1 ℓ).sub (ha.1 ℓ)
  have hnn : ∀ ℓ p, p ∈ Ω → 0 ≤ E ℓ p := fun ℓ p hp =>
    sub_nonneg.2 (vm_kernel_order hα hβ0 hβ1 hN hB hc i ℓ hp.1 hp.2).2
  have hs : ∀ k, Summable (fun ℓ => ∫ p in S k, E ℓ p) := fun k =>
    (vm_region_summability hα hβ0 hβ1 hN hB hc i (hS k) (hsub k)).2.1
  have hsΩ : Summable (fun ℓ => ∫ p in Ω, E ℓ p) :=
    (vm_region_summability hα hβ0 hβ1 hN hB hc i hΩ Subset.rfl).2.1
  have hid (ℓ : ℤ) (k : κ) : (∫ p in Ω, (S k).indicator (E ℓ) p) =
      ∫ p in S k, E ℓ p := by
    rw [setIntegral_indicator (hS k), inter_eq_right.2 (hsub k)]
  have hle (ℓ : ℤ) : (∫ p in Ω, E ℓ p) ≤ ∑ k, ∫ p in S k, E ℓ p := by
    have hind : ∀ k, IntegrableOn ((S k).indicator (E ℓ)) Ω :=
      fun k => (hi ℓ).indicator (hS k)
    calc
      _ ≤ ∫ p in Ω, ∑ k, (S k).indicator (E ℓ) p := by
        apply setIntegral_mono_on (hi ℓ) (integrable_finset_sum _ fun k _ => hind k) hΩ
        intro p hp
        obtain ⟨k, hk⟩ := mem_iUnion.1 (hcover hp)
        calc E ℓ p = (S k).indicator (E ℓ) p := (indicator_of_mem hk _).symm
          _ ≤ ∑ j, (S j).indicator (E ℓ) p := by
            apply Finset.single_le_sum _ (Finset.mem_univ k)
            intro j _
            by_cases hj : p ∈ S j
            · rw [indicator_of_mem hj]; exact hnn ℓ p hp
            · rw [indicator_of_notMem hj]
      _ = _ := by rw [integral_finset_sum _ fun k _ => hind k]; simp_rw [hid]
  have htotal : vPart β B (plSpec α c N) i - vFlat β B (plSpec α c N) i =
      (Real.pi ^ 2)⁻¹ * ∑' ℓ, ∫ p in Ω, E ℓ p := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_unit, Nat.cast_one, one_smul]
      using vm_error_decomposition hα hβ0 hβ1 N B c hN hB hc i hzero
        (fun _ : Unit => Ω) (fun _ => hΩ) (by intro a b hab; exact (hab (Subsingleton.elim a b)).elim)
        (by change (⋃ _ : Unit, Ω) = Ω; exact iUnion_const Ω) (fun _ => hsΩ)
  rw [htotal, ← Finset.mul_sum, ← Summable.tsum_finsetSum (fun k _ => hs k)]
  exact mul_le_mul_of_nonneg_left (hsΩ.tsum_le_tsum hle (summable_sum (fun k _ => hs k)))
    (by positivity)

private lemma vm_rectangle_error_bound {α β : ℝ} (hα : 0 < α)
    (hβ0 : 0 < β) (hβ1 : β < 1) {N B : ℕ} {c : ℝ}
    (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) (i : Fin N)
    {I J : Set ℝ} (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (hIsub : I ⊆ Ioo 0 (gammaOf N B)) (hJsub : J ⊆ Ioo 0 (gammaOf N B)) :
    (Real.pi ^ 2)⁻¹ * (∑' ℓ : ℤ, ∫ p in I ×ˢ J,
      (lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 -
        lagNumer β B (plSpec α c N) i ℓ p.1 p.2)) ≤
      vIJ β B (plSpec α c N) i I J := by
  have hsub := prod_mono hIsub hJsub
  have hb := (vm_region_summability hα hβ0 hβ1 hN hB hc i (hI.prod hJ) hsub).2.2.2
  have ha := lem_app_pl_age_iv hα hβ0 hβ1 N B c hN hB hc i
  convert hb using 1
  unfold vIJ lagTerm
  congr 1
  apply tsum_congr
  intro ℓ
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  symm
  exact integral_prod _ (by rw [Measure.prod_restrict]; exact (ha.2.2.1 ℓ).mono_set hsub)

private lemma vm_meso_region_cover {γ δ η Rr : ℝ}
    (hγ : 0 < γ) (hδ : 0 < δ) (hη : 0 < η) (hη1 : η < 1) (hγ2 : 2 ≤ γ) :
    let L := Ioo 0 (η * γ)
    let U := Ico (η * γ) γ
    let J := Ioo δ 2
    let T := stripSet η Rr 1 γ
    let G := (L ×ˢ L) \ ((J ×ˢ L) ∪ (L ×ˢ J) ∪ T)
    let S : Fin 7 → Set (ℝ × ℝ) := ![U ×ˢ U, U ×ˢ L, L ×ˢ U, J ×ˢ L, L ×ˢ J, T, G]
    (∀ k, MeasurableSet (S k)) ∧ (∀ k, S k ⊆ Ioo 0 γ ×ˢ Ioo 0 γ) ∧
      Ioo 0 γ ×ˢ Ioo 0 γ ⊆ ⋃ k, S k := by
  intro L U J T G S
  have hL : L ⊆ Ioo 0 γ := fun m hm => ⟨hm.1, hm.2.trans (by nlinarith)⟩
  have hU : U ⊆ Ioo 0 γ := fun m hm => ⟨lt_of_lt_of_le (mul_pos hη hγ) hm.1, hm.2⟩
  have hJ : J ⊆ Ioo 0 γ := fun m hm => ⟨hδ.trans hm.1, hm.2.trans_le hγ2⟩
  have hT : T ⊆ Ioo 0 γ ×ˢ Ioo 0 γ := by
    intro p hp
    exact ⟨hL ⟨by linarith [hp.1], hp.2.1⟩,
      hL ⟨by linarith [hp.2.2.1], hp.2.2.2.1⟩⟩
  have hG : MeasurableSet G := (measurableSet_Ioo.prod measurableSet_Ioo).diff
    (((measurableSet_Ioo.prod measurableSet_Ioo).union
      (measurableSet_Ioo.prod measurableSet_Ioo)).union (vm_strip_meas η Rr 1 γ))
  refine ⟨?_, ?_, ?_⟩
  · intro k
    fin_cases k
    · exact measurableSet_Ico.prod measurableSet_Ico
    · exact measurableSet_Ico.prod measurableSet_Ioo
    · exact measurableSet_Ioo.prod measurableSet_Ico
    · exact measurableSet_Ioo.prod measurableSet_Ioo
    · exact measurableSet_Ioo.prod measurableSet_Ioo
    · exact vm_strip_meas η Rr 1 γ
    · exact hG
  · intro k
    fin_cases k
    · exact prod_mono hU hU
    · exact prod_mono hU hL
    · exact prod_mono hL hU
    · exact prod_mono hJ hL
    · exact prod_mono hL hJ
    · exact hT
    · exact fun _ hp => ⟨hL hp.1.1, hL hp.1.2⟩
  · intro p hp
    apply mem_iUnion.2
    by_cases hx : p.1 < η * γ
    · by_cases hy : p.2 < η * γ
      · have hpl : p ∈ L ×ˢ L := ⟨⟨hp.1.1, hx⟩, ⟨hp.2.1, hy⟩⟩
        by_cases hxJ : p.1 ∈ J
        · exact ⟨3, ⟨hxJ, hpl.2⟩⟩
        · by_cases hyJ : p.2 ∈ J
          · exact ⟨4, ⟨hpl.1, hyJ⟩⟩
          · by_cases hpT : p ∈ T
            · exact ⟨5, hpT⟩
            · refine ⟨6, hpl, ?_⟩
              rintro ((hh | hh) | hh)
              · exact hxJ hh.1
              · exact hyJ hh.2
              · exact hpT hh
      · exact ⟨2, ⟨⟨hp.1.1, hx⟩, ⟨le_of_not_gt hy, hp.2.2⟩⟩⟩
    · by_cases hy : p.2 < η * γ
      · exact ⟨1, ⟨⟨le_of_not_gt hx, hp.1.2⟩, ⟨hp.2.1, hy⟩⟩⟩
      · exact ⟨0, ⟨⟨le_of_not_gt hx, hp.1.2⟩, ⟨le_of_not_gt hy, hp.2.2⟩⟩⟩

private lemma vm_gaussian_quadratic (a b : ℝ) :
    Integrable (fun g : ℝ => (a * g + b * Real.sign g) ^ 2) (gaussianReal 0 1) ∧
      (∫ g : ℝ, (a * g + b * Real.sign g) ^ 2 ∂(gaussianReal 0 1)) =
        a ^ 2 + 2 * c0 * a * b + b ^ 2 := by
  haveI : NullSingletonClass (gaussianReal (0 : ℝ) 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hae : ∀ᵐ g : ℝ ∂(gaussianReal 0 1), g ≠ 0 := by
    exact ae_iff.2 (by simp)
  have heq : (fun g : ℝ => (a * g + b * Real.sign g) ^ 2) =ᵐ[gaussianReal 0 1]
      (fun g => a ^ 2 * g ^ 2 + (2 * a * b) * |g| + b ^ 2) := by
    filter_upwards [hae] with g hg
    rcases hg.lt_or_gt with h | h
    · rw [Real.sign_of_neg h, abs_of_neg h]; ring
    · rw [Real.sign_of_pos h, abs_of_pos h]; ring
  have hi2 := (Muon.Foundations.gaussian_integrable_pow 2).const_mul (a ^ 2)
  have hiabs : Integrable (fun g : ℝ => |g|) (gaussianReal 0 1) := by
    simpa only [pow_one, Real.norm_eq_abs] using (Muon.Foundations.gaussian_integrable_pow 1).norm
  have hi := (hi2.add (hiabs.const_mul (2 * a * b))).add (integrable_const (b ^ 2))
  refine ⟨hi.congr heq.symm, ?_⟩
  have he1 := integral_add (hi2.add (hiabs.const_mul (2 * a * b)))
    (integrable_const (b ^ 2) : Integrable (fun _ : ℝ => b ^ 2) (gaussianReal 0 1))
  have he2 := integral_add hi2 (hiabs.const_mul (2 * a * b))
  simp only [Pi.add_apply] at he1 he2
  rw [integral_congr_ae heq, he1, he2, integral_const_mul, integral_const_mul,
    Muon.Foundations.gaussian_moment_two, Muon.Foundations.gaussian_abs_moment, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  unfold c0
  ring

private lemma vm_quadratic_bounds {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {b : ℝ} (hb : 0 ≤ b) :
    min (1 / sPow β 2) 1 / 2 * (1 + b) ^ 2 ≤
        1 / sPow β 2 + 2 * c0 / Real.sqrt (sPow β 2) * b + b ^ 2 ∧
      1 / sPow β 2 + 2 * c0 / Real.sqrt (sPow β 2) * b + b ^ 2 ≤
        (1 / sPow β 2 + 2 * c0 / Real.sqrt (sPow β 2) + 1) * (1 + b) ^ 2 := by
  have hs : 0 < sPow β 2 := by
    rw [sPow_two hβ0.le hβ1]
    exact div_pos (by linarith) (by linarith)
  have ha : 0 ≤ 1 / sPow β 2 := (one_div_pos.2 hs).le
  have hc : 0 ≤ 2 * c0 / Real.sqrt (sPow β 2) := by
    exact div_nonneg (mul_nonneg (by norm_num) vm_c0_pos.le) (Real.sqrt_nonneg _)
  have hm0 : 0 ≤ min (1 / sPow β 2) 1 := le_min ha (by norm_num)
  have hm1 := min_le_left (1 / sPow β 2) 1
  have hm2 := min_le_right (1 / sPow β 2) 1
  constructor
  · have hsq : 0 ≤ (1 - b) ^ 2 := sq_nonneg _
    have hbb := mul_le_mul_of_nonneg_right hm2 (sq_nonneg b)
    have hmid := mul_nonneg hc hb
    nlinarith
  · have h1 : 1 ≤ (1 + b) ^ 2 := by nlinarith [sq_nonneg b]
    have h2 : b ≤ (1 + b) ^ 2 := by nlinarith [sq_nonneg b]
    have h3 : b ^ 2 ≤ (1 + b) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hc]

private lemma vm_psd_cross_negligible {a d e b : ℕ → ℝ}
    (hb : ∀ᶠ n in atTop, 0 ≤ b n)
    (hPSD : ∀ᶠ n in atTop, 0 ≤ e n ∧ e n ≤ Real.sqrt (a n * d n))
    (ha : Tendsto (fun n => a n / (1 + b n) ^ 2) atTop (𝓝 0))
    (hd : IsBigO atTop d (fun n => (1 + b n) ^ 2)) :
    Tendsto (fun n => e n / (1 + b n) ^ 2) atTop (𝓝 0) := by
  have hzero : Tendsto (fun n => (a n / (1 + b n) ^ 2) *
      (d n / (1 + b n) ^ 2)) atTop (𝓝 0) := by
    have hlo : IsLittleO atTop a (fun n => (1 + b n) ^ 2) :=
      (isLittleO_iff_tendsto' (by
        filter_upwards [hb] with n hn
        have : (1 + b n) ^ 2 ≠ 0 := by positivity
        exact fun h => (this h).elim)).2 ha
    have hmul := hlo.mul_isBigO hd
    apply (isLittleO_iff_tendsto' (by
      filter_upwards [hb] with n hn
      have : (1 + b n) ^ 2 * (1 + b n) ^ 2 ≠ 0 := by positivity
      exact fun h => (this h).elim)).1 hmul |>.congr
    intro n
    simp only [div_mul_div_comm]
  have hsqrt := hzero.sqrt
  simp only [Real.sqrt_zero] at hsqrt
  refine squeeze_zero' ?_ ?_ hsqrt
  · filter_upwards [hPSD] with n hn
    exact div_nonneg hn.1 (sq_nonneg _)
  · filter_upwards [hb, hPSD] with n hn hp
    have hden : 0 < (1 + b n) ^ 2 := by positivity
    calc e n / (1 + b n) ^ 2 ≤ Real.sqrt (a n * d n) / (1 + b n) ^ 2 :=
          div_le_div_of_nonneg_right hp.2 hden.le
      _ = Real.sqrt ((a n / (1 + b n) ^ 2) * (d n / (1 + b n) ^ 2)) := by
        have he : (a n / (1 + b n) ^ 2) * (d n / (1 + b n) ^ 2) =
            (a n * d n) / ((1 + b n) ^ 2) ^ 2 := by
          rw [div_mul_div_comm, ← pow_two]
        rw [he, Real.sqrt_div' (a n * d n) (sq_nonneg _), Real.sqrt_sq hden.le]

private lemma vm_l2_sq_error {f h : ℝ → ℝ}
    (hf : MemLp f 2 (gaussianReal 0 1)) (hh : MemLp h 2 (gaussianReal 0 1)) :
    |(∫ g, f g ^ 2 ∂(gaussianReal 0 1)) - (∫ g, h g ^ 2 ∂(gaussianReal 0 1))| ≤
      l2Norm (fun g => f g - h g) *
        (2 * l2Norm h + l2Norm (fun g => f g - h g)) := by
  have hsub : MemLp (fun g => f g - h g) 2 (gaussianReal 0 1) := hf.sub hh
  have h1 := vm_l2Norm_add_le hsub hh
  have h2 := vm_l2Norm_add_le hsub.neg hf
  have he1 : (fun g => (f g - h g) + h g) = f := by ext g; ring
  have he2 : (fun g => -(f g - h g) + f g) = h := by ext g; ring
  rw [he1] at h1
  simp only [Pi.neg_apply] at h2
  rw [he2] at h2
  have hneg : l2Norm (-(fun g => f g - h g)) = l2Norm (fun g => f g - h g) := by
    unfold l2Norm
    simp only [Pi.neg_apply, neg_sq]
  rw [hneg] at h2
  have hF : 0 ≤ l2Norm f := Real.sqrt_nonneg _
  have hH : 0 ≤ l2Norm h := Real.sqrt_nonneg _
  have hE : 0 ≤ l2Norm (fun g => f g - h g) := Real.sqrt_nonneg _
  have hsF : l2Norm f ^ 2 = ∫ g, f g ^ 2 ∂(gaussianReal 0 1) :=
    Real.sq_sqrt (integral_nonneg fun g => sq_nonneg (f g))
  have hsH : l2Norm h ^ 2 = ∫ g, h g ^ 2 ∂(gaussianReal 0 1) :=
    Real.sq_sqrt (integral_nonneg fun g => sq_nonneg (h g))
  rw [← hsF, ← hsH, abs_le]
  have h3 : l2Norm f ^ 2 ≤
      (l2Norm (fun g => f g - h g) + l2Norm h) ^ 2 :=
    pow_le_pow_left₀ hF h1 2
  have h4 := mul_nonneg (by linarith : 0 ≤ l2Norm f - l2Norm h +
    l2Norm (fun g => f g - h g)) (by linarith : 0 ≤ l2Norm f + l2Norm h)
  have h5 := mul_le_mul_of_nonneg_left h1 hE
  constructor <;> nlinarith

private lemma vm_bCoef_nonneg {α : ℝ} (hα : 0 < α) {N B : ℕ} (i : Fin N) :
    0 ≤ bCoef α B i := by
  have hx := vm_rowFrac_bounds i
  have hPsi := lem_app_pl_Psi_i_pos hα (rowFrac i) hx
  unfold bCoef
  exact div_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hx.1.le _))
    hPsi.le) vm_c0_pos.le

private lemma vm_gamma_profile_equiv_bsq {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (i : ∀ n, Fin (N n)) (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) :
    IsEquivalent atTop
      (fun n => gammaOf (N n) (B n) * profGamma α (rowFrac (i n)))
      (fun n => bCoef α (B n) (i n) ^ 2) := by
  have hx0 : ∀ n, 0 < rowFrac (i n) := fun n => (vm_rowFrac_bounds (i n)).1
  have hm := (IsEquivalent.refl (u := fun n => gammaOf (N n) (B n))).mul
    ((lem_app_pl_matching R.hα hα1).comp_tendsto (vm_pull hx0 hx))
  refine hm.congr_right (Eventually.of_forall fun n => ?_)
  change gammaOf (N n) (B n) *
      (rowFrac (i n) ^ α * profPsi α (rowFrac (i n)) ^ 2 / c0 ^ 2) = _
  unfold bCoef
  convert (vm_bsq (α := α) (show 0 ≤ gammaOf (N n) (B n) by
    unfold gammaOf
    positivity) (hx0 n)).symm using 1 <;> ring

private lemma vm_profiles_gamma_lt {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    IsEquivalent (𝓝[>] (0 : ℝ)) (fun x : ℝ => profGamma α x)
      (fun x : ℝ => x ^ α * Real.log (x ^ (-α)) ^ 2 / (1 - α)) := by
  have hc0 : 0 < c0 := by
    unfold c0
    exact Real.sqrt_pos.2 (by positivity)
  have h := ((IsEquivalent.refl (u := fun x : ℝ => x ^ α)).mul
    ((lem_app_pl_Psi_ii_lt hα0 hα1).pow 2)).div
      (IsEquivalent.refl (u := fun _ : ℝ => c0 ^ 2))
  refine (lem_app_pl_matching hα0 hα1.le).trans (h.trans_eventuallyEq ?_)
  filter_upwards [] with x
  change x ^ α * (c0 / Real.sqrt (1 - α) * Real.log (x ^ (-α))) ^ 2 / c0 ^ 2 = _
  rw [mul_pow, div_pow, Real.sq_sqrt (by linarith : 0 ≤ 1 - α)]
  field_simp [hc0.ne']

private lemma vm_profiles_gamma_one {α : ℝ} (hα : α = 1) :
    IsEquivalent (𝓝[>] (0 : ℝ)) (fun x : ℝ => profGamma α x)
      (fun x : ℝ => 4 / 9 * x * Real.log (1 / x) ^ (3 : ℕ)) := by
  have hc0 : 0 < c0 := by
    unfold c0
    exact Real.sqrt_pos.2 (by positivity)
  have h := ((IsEquivalent.refl (u := fun x : ℝ => x ^ α)).mul
    ((lem_app_pl_Psi_ii_one hα).pow 2)).div
      (IsEquivalent.refl (u := fun _ : ℝ => c0 ^ 2))
  refine (lem_app_pl_matching (by linarith) hα.le).trans (h.trans_eventuallyEq ?_)
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with x hx
  have hlog : 0 ≤ Real.log (1 / x) := Real.log_nonneg (by
    rw [le_div_iff₀ hx.1]
    linarith [hx.2])
  have hpow : (Real.log (1 / x) ^ (3 / 2 : ℝ)) ^ 2 =
      Real.log (1 / x) ^ (3 : ℕ) := by
    rw [← Real.rpow_mul_natCast hlog]
    norm_num
  change x ^ α * (2 / 3 * c0 * Real.log (1 / x) ^ (3 / 2 : ℝ)) ^ 2 / c0 ^ 2 = _
  rw [hα, Real.rpow_one, mul_pow, mul_pow, hpow]
  field_simp [hc0.ne']
  ring

private lemma vm_sqrt_profile_equiv_b {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (i : ∀ n, Fin (N n)) (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) :
    IsEquivalent atTop
      (fun n => Real.sqrt (gammaOf (N n) (B n) * profGamma α (rowFrac (i n))))
      (fun n => bCoef α (B n) (i n)) := by
  have hbpos : ∀ n, 0 < bCoef α (B n) (i n) := by
    intro n
    have hxb := vm_rowFrac_bounds (i n)
    unfold bCoef
    exact div_pos (mul_pos (mul_pos (Real.sqrt_pos.2 (by
      unfold gammaOf
      exact div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n)))
      (Real.rpow_pos_of_pos hxb.1 _))
      (lem_app_pl_Psi_i_pos R.hα _ hxb)) vm_c0_pos
  have he := vm_gamma_profile_equiv_bsq R hα1 i hx
  have hr := (isEquivalent_iff_tendsto_one
    (Eventually.of_forall fun n => (sq_pos_of_pos (hbpos n)).ne')).1 he
  have hs : Tendsto (fun n => Real.sqrt
      ((gammaOf (N n) (B n) * profGamma α (rowFrac (i n))) /
        bCoef α (B n) (i n) ^ 2)) atTop (𝓝 1) := by
    convert Real.continuous_sqrt.continuousAt.tendsto.comp hr using 1
    · ext n
      rfl
    · norm_num
  rw [isEquivalent_iff_tendsto_one (Eventually.of_forall fun n => (hbpos n).ne')]
  refine hs.congr' (Eventually.of_forall fun n => ?_)
  have hA : 0 ≤ gammaOf (N n) (B n) * profGamma α (rowFrac (i n)) := by
    have hxI := vm_rowFrac_bounds (i n)
    exact mul_nonneg (by unfold gammaOf; exact (div_pos
      (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n)).le)
      (lem_app_pl_Gamma_helper_pos R.hα _ hxI).le
  change Real.sqrt ((gammaOf (N n) (B n) * profGamma α (rowFrac (i n))) /
      bCoef α (B n) (i n) ^ 2) =
    Real.sqrt (gammaOf (N n) (B n) * profGamma α (rowFrac (i n))) /
      bCoef α (B n) (i n)
  rw [Real.sqrt_div hA, Real.sqrt_sq_eq_abs, abs_of_pos (hbpos n)]

private lemma vm_vhat_equiv_quadratic {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (i : ∀ n, Fin (N n)) (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) :
    IsEquivalent atTop
      (fun n => vhatApprox β α (B n) (i n))
      (fun n => 1 / sPow β 2 + 2 * c0 / Real.sqrt (sPow β 2) * bCoef α (B n) (i n) +
        bCoef α (B n) (i n) ^ 2) := by
  let b : ℕ → ℝ := fun n => bCoef α (B n) (i n)
  let A : ℕ → ℝ := fun n => gammaOf (N n) (B n) * profGamma α (rowFrac (i n))
  let Q : ℕ → ℝ := fun n => 1 / sPow β 2 + 2 * c0 / Real.sqrt (sPow β 2) * b n + b n ^ 2
  let D : ℕ → ℝ := fun n => (1 + b n) ^ 2
  have hb : ∀ n, 0 ≤ b n := fun n => vm_bCoef_nonneg R.hα (i n)
  have hDQ : IsBigO atTop D Q := by
    let k : ℝ := min (1 / sPow β 2) 1 / 2
    have hs : 0 < sPow β 2 := by
      rw [sPow_two R.hβ0.le R.hβ1]
      exact div_pos (by linarith [R.hβ1]) (by linarith [R.hβ0])
    have hk : 0 < k := div_pos (lt_min (one_div_pos.2 hs) (by norm_num)) (by norm_num)
    refine IsBigO.of_bound (1 / k) (Eventually.of_forall fun n => ?_)
    have hl : k * D n ≤ Q n := by
      dsimp only [D, Q]
      exact (vm_quadratic_bounds R.hβ0 R.hβ1 (hb n)).1
    have hD : 0 ≤ D n := sq_nonneg _
    have hQ : 0 ≤ Q n := le_trans (mul_nonneg hk.le hD) hl
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hD, abs_of_nonneg hQ]
    calc D n ≤ Q n / k := (le_div_iff₀ hk).2 (by simpa only [mul_comm] using hl)
      _ = (1 / k) * Q n := by ring
  have hbD : IsBigO atTop b D := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hb n), abs_of_nonneg (sq_nonneg _), one_mul]
    dsimp only [D]
    nlinarith [hb n]
  have hb2D : IsBigO atTop (fun n => b n ^ 2) D := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (sq_nonneg _), one_mul]
    dsimp only [D]
    nlinarith [hb n]
  have hsqrt : IsLittleO atTop (fun n => Real.sqrt (A n) - b n) b := by
    have h := vm_sqrt_profile_equiv_b R hα1 i hx
    change IsLittleO atTop (fun n => Real.sqrt (gammaOf (N n) (B n) *
      profGamma α (rowFrac (i n))) - bCoef α (B n) (i n))
      (fun n => bCoef α (B n) (i n)) at h
    simpa only [A, b] using h
  have hA : IsLittleO atTop (fun n => A n - b n ^ 2) (fun n => b n ^ 2) := by
    have h := vm_gamma_profile_equiv_bsq R hα1 i hx
    change IsLittleO atTop (fun n => gammaOf (N n) (B n) *
      profGamma α (rowFrac (i n)) - bCoef α (B n) (i n) ^ 2)
      (fun n => bCoef α (B n) (i n) ^ 2) at h
    simpa only [A, b] using h
  change IsLittleO atTop (fun n => vhatApprox β α (B n) (i n) - Q n) Q
  have h1 := (hsqrt.trans_isBigO (hbD.trans hDQ)).const_mul_left
    (2 * c0 / Real.sqrt (sPow β 2))
  have h2 := hA.trans_isBigO (hb2D.trans hDQ)
  refine (h1.add h2).congr (fun n => ?_) (fun n => rfl)
  dsimp only [A, b, Q, vhatApprox]
  ring

private lemma vm_flat_error {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) :
    Tendsto (fun n => (vFlat β (B n) (plSpec α (c n) (N n)) (i n) -
      (1 / sPow β 2 + 2 * c0 / Real.sqrt (sPow β 2) * bCoef α (B n) (i n) +
        bCoef α (B n) (i n) ^ 2)) / (1 + bCoef α (B n) (i n)) ^ 2) atTop (𝓝 0) := by
  let b : ℕ → ℝ := fun n => bCoef α (B n) (i n)
  let f : ℕ → ℝ → ℝ := fun n => calV β (B n) (plSpec α (c n) (N n)) (i n)
  let h : ℕ → ℝ → ℝ := fun n g => g / Real.sqrt (sPow β 2) + b n * Real.sign g
  let E : ℕ → ℝ := fun n => l2Norm (fun g => f n g - h n g)
  let Q : ℕ → ℝ := fun n => 1 / sPow β 2 + 2 * c0 / Real.sqrt (sPow β 2) * b n + b n ^ 2
  let C : ℝ := 1 / sPow β 2 + 2 * c0 / Real.sqrt (sPow β 2) + 1
  have hb : ∀ n, 0 ≤ b n := fun n => vm_bCoef_nonneg R.hα (i n)
  have hs : 0 < sPow β 2 := by
    rw [sPow_two R.hβ0.le R.hβ1]
    exact div_pos (by linarith [R.hβ1]) (by linarith [R.hβ0])
  have hC : 0 ≤ C := by
    dsimp [C]
    have := vm_c0_pos
    positivity
  have hsqrt := Real.sq_sqrt hs.le
  have hm : ∀ n, Integrable (fun g => h n g ^ 2) (gaussianReal 0 1) ∧
      (∫ g, h n g ^ 2 ∂(gaussianReal 0 1)) = Q n := by
    intro n
    have hquad := vm_gaussian_quadratic (1 / Real.sqrt (sPow β 2)) (b n)
    have he : ∀ g, (1 / Real.sqrt (sPow β 2)) * g + b n * Real.sign g = h n g := by
      intro g; dsimp [h]; ring
    simp_rw [he] at hquad
    refine ⟨hquad.1, hquad.2.trans ?_⟩
    dsimp [Q]
    rw [div_pow, hsqrt]
    ring
  have hmeas : ∀ n, AEStronglyMeasurable (h n) (gaussianReal 0 1) := by
    intro n
    have hsign : Measurable Real.sign := by
      unfold Real.sign
      exact Measurable.ite measurableSet_Iio measurable_const
        (Measurable.ite measurableSet_Ioi measurable_const measurable_const)
    exact ((measurable_id.div_const _).add (hsign.const_mul _)).aestronglyMeasurable
  have hh : ∀ n, MemLp (h n) 2 (gaussianReal 0 1) := fun n => vm_memLp_of_sq (hmeas n) (hm n).1
  have hH : ∀ n, l2Norm (h n) ≤ Real.sqrt C * (1 + b n) := by
    intro n
    have hbound := (vm_quadratic_bounds R.hβ0 R.hβ1 (hb n)).2
    have hbound' : Q n ≤ C * (1 + b n) ^ 2 := hbound
    unfold l2Norm
    rw [(hm n).2]
    calc Real.sqrt (Q n) ≤ Real.sqrt (C * (1 + b n) ^ 2) := Real.sqrt_le_sqrt hbound'
      _ = _ := by rw [Real.sqrt_mul hC, Real.sqrt_sq (by linarith [hb n])]
  have hv := lem_app_pl_vector R hα1 i hi hx
  have hE : Tendsto (fun n => E n / (1 + b n)) atTop (𝓝 0) := hv.2.1
  have hlim : Tendsto (fun n => (E n / (1 + b n)) *
      (2 * Real.sqrt C + E n / (1 + b n))) atTop (𝓝 0) := by
    simpa using hE.mul (hE.const_add (2 * Real.sqrt C))
  have hnorm : Tendsto (fun n => |vFlat β (B n) (plSpec α (c n) (N n)) (i n) - Q n| /
      (1 + b n) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => div_nonneg (abs_nonneg _) (sq_nonneg _)) ?_ hlim
    filter_upwards [hv.1, Wpart_integrable_measurable R] with n hfn hmn
    have hfm : AEStronglyMeasurable (f n) (gaussianReal 0 1) := by
      exact ((hmn (i n)).2.2.prod_swap.integral_prod_right').const_mul _
    have hineq := vm_l2_sq_error (vm_memLp_of_sq hfm hfn) (hh n)
    rw [(hm n).2] at hineq
    have hden : 0 < 1 + b n := by linarith [hb n]
    have hE0 : 0 ≤ E n := Real.sqrt_nonneg _
    calc |vFlat β (B n) (plSpec α (c n) (N n)) (i n) - Q n| / (1 + b n) ^ 2
        ≤ E n * (2 * l2Norm (h n) + E n) / (1 + b n) ^ 2 :=
          div_le_div_of_nonneg_right hineq (sq_nonneg _)
      _ ≤ E n * (2 * (Real.sqrt C * (1 + b n)) + E n) / (1 + b n) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left (by linarith [hH n]) hE0
      _ = _ := by field_simp
  have hnorm' : Tendsto (fun n => |(vFlat β (B n) (plSpec α (c n) (N n)) (i n) - Q n) /
      (1 + b n) ^ 2|) atTop (𝓝 0) := by
    simpa only [abs_div, abs_of_nonneg (sq_nonneg (1 + b _))] using hnorm
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 hnorm'

private lemma vm_flat_bigO {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) :
    IsBigO atTop (fun n => vFlat β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => (1 + bCoef α (B n) (i n)) ^ 2) := by
  let D : ℕ → ℝ := fun n => (1 + bCoef α (B n) (i n)) ^ 2
  let Q : ℕ → ℝ := fun n => 1 / sPow β 2 +
    2 * c0 / Real.sqrt (sPow β 2) * bCoef α (B n) (i n) + bCoef α (B n) (i n) ^ 2
  have hD : ∀ n, 0 < D n := fun n => by
    have := vm_bCoef_nonneg (B := B n) R.hα (i n)
    dsimp [D]; positivity
  have herr : IsLittleO atTop
      (fun n => vFlat β (B n) (plSpec α (c n) (N n)) (i n) - Q n) D :=
    (isLittleO_iff_tendsto (fun n hn => ((hD n).ne' hn).elim)).2
      (vm_flat_error R hα1 i hi hx)
  have hs : 0 < sPow β 2 := by
    rw [sPow_two R.hβ0.le R.hβ1]
    exact div_pos (by linarith [R.hβ1]) (by linarith [R.hβ0])
  have hq : IsBigO atTop Q D := by
    refine IsBigO.of_bound (1 / sPow β 2 + 2 * c0 / Real.sqrt (sPow β 2) + 1)
      (Eventually.of_forall fun n => ?_)
    have hb := vm_bCoef_nonneg (B := B n) R.hα (i n)
    have hc := vm_c0_pos
    have hQ : 0 ≤ Q n := by dsimp [Q]; positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hQ, abs_of_pos (hD n)]
    exact (vm_quadratic_bounds R.hβ0 R.hβ1 hb).2
  convert herr.isBigO.add hq using 1
  ext n
  simp only [sub_add_cancel]

private lemma vm_interior_bigO {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) :
    IsBigO atTop (fun n => vIJ β (B n) (plSpec α (c n) (N n)) (i n)
      (Ioo 0 (η * gammaOf (N n) (B n))) (Ioo 0 (η * gammaOf (N n) (B n))))
      (fun n => (1 + bCoef α (B n) (i n)) ^ 2) := by
  obtain ⟨K, hK, hbound⟩ := vm_interior_square_bound R.hα R.hβ0 R.hβ1 η hη0 hη1
  have hcomp : IsBigO atTop (fun n => vIJ β (B n) (plSpec α (c n) (N n)) (i n)
      (Ioo 0 (η * gammaOf (N n) (B n))) (Ioo 0 (η * gammaOf (N n) (B n))))
      (fun n => vFlat β (B n) (plSpec α (c n) (N n)) (i n)) := by
    refine IsBigO.of_bound K (Eventually.of_forall fun n => ?_)
    have hn := hbound (N n) (B n) (c n) (R.hNpos n) (R.hBpos n) (R.hcpos n) (i n)
    have hf := (lem_app_pl_age_iv R.hα R.hβ0 R.hβ1 (N n) (B n) (c n)
      (R.hNpos n) (R.hBpos n) (R.hcpos n) (i n)).2.2.2.2.1
    simpa only [Real.norm_eq_abs, abs_of_nonneg hn.1, abs_of_nonneg hf] using hn.2
  exact hcomp.trans (vm_flat_bigO R hα1 i hi hx)

private lemma vm_scale_negligible {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (i : ∀ n, Fin (N n)) (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) :
    Tendsto (fun n => gammaOf (N n) (B n) * rowFrac (i n) ^ α /
      (1 + bCoef α (B n) (i n)) ^ 2) atTop (𝓝 0) := by
  have hx0 : ∀ n, 0 < rowFrac (i n) := fun n => (vm_rowFrac_bounds (i n)).1
  have hγ : ∀ n, 0 < gammaOf (N n) (B n) := fun n => by
    unfold gammaOf
    exact div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n)
  rcases hα1.lt_or_eq with ha | ha
  · have hL := vm_L_tendsto R.hα hx0 hx
    have hev := hL.eventually_ge_atTop (1 - (1 / 2 + Real.log (1 - α)))
    refine squeeze_zero' ?_ ?_ (vm_lim_lt R.hα ha hγ hx0 hx)
    · exact Eventually.of_forall fun n => by
        have := (hγ n).le
        have := Real.rpow_nonneg (hx0 n).le α
        exact div_nonneg (mul_nonneg ‹0 ≤ gammaOf (N n) (B n)› this) (sq_nonneg _)
    · filter_upwards [hev] with n hn
      have h1 : 1 ≤ 1 / 2 + Real.log (1 - α) + Real.log (rowFrac (i n) ^ (-α)) := by linarith
      have h2 : 1 ≤ (1 / 2 + Real.log (1 - α) + Real.log (rowFrac (i n) ^ (-α))) / (1 - α) := by
        rw [le_div_iff₀ (by linarith : 0 < 1 - α)]
        linarith [R.hα]
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      have hn0 := mul_nonneg (hγ n).le (Real.rpow_nonneg (hx0 n).le α)
      have hh := mul_le_mul_of_nonneg_left h2 hn0
      simpa only [mul_one, one_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hh
  · subst α
    have hL : Tendsto (fun n => Real.log (1 / rowFrac (i n))) atTop atTop := by
      have := vm_L_tendsto (by norm_num : (0 : ℝ) < 1) hx0 hx
      simpa [Real.rpow_neg_one, one_div] using this
    have hev := hL.eventually_ge_atTop 1
    refine squeeze_zero' ?_ ?_ (vm_lim_one hγ hx0 hx)
    · exact Eventually.of_forall fun n => by
        apply div_nonneg _ (sq_nonneg _)
        exact mul_nonneg (hγ n).le (Real.rpow_nonneg (hx0 n).le _)
    · filter_upwards [hev] with n hn
      have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have h1 : 1 ≤ (Real.log 2 + Real.log (1 / rowFrac (i n))) *
          (1 / 2 + Real.log (1 / rowFrac (i n))) := by nlinarith
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      have hn0 := mul_nonneg (hγ n).le (Real.rpow_nonneg (hx0 n).le (1 : ℝ))
      nlinarith [mul_le_mul_of_nonneg_left h1 hn0]

private lemma vm_m0_negligible {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (i : ∀ n, Fin (N n)) (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) :
    Tendsto (fun n => partMN (B n) (plSpec α (c n) (N n))
      (1 / plSpec α (c n) (N n) (i n)) /
      (1 + bCoef α (B n) (i n)) ^ 2) atTop (𝓝 0) := by
  have hγ : ∀ n, 0 < gammaOf (N n) (B n) := fun n => by
    unfold gammaOf
    exact div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n)
  have hx0 : ∀ n, 0 < rowFrac (i n) := fun n => (vm_rowFrac_bounds (i n)).1
  have hm : ∀ n, 0 < partMN (B n) (plSpec α (c n) (N n))
      (1 / plSpec α (c n) (N n) (i n)) := fun n =>
    (vm_m0_facts (α := α) (R.hNpos n) (R.hBpos n) (R.hcpos n) (i n)).1.1
  have hbound : ∀ n, partMN (B n) (plSpec α (c n) (N n))
      (1 / plSpec α (c n) (N n) (i n)) ≤
      gammaOf (N n) (B n) * contS α (rowFrac (i n) ^ α) := by
    intro n
    rw [vm_m0_eq (R.hNpos n) (R.hBpos n) (R.hcpos n) (i n)]
    exact mul_le_mul_of_nonneg_left
      (sub_nonneg.1 (lem_app_pl_finite_inverse_i_a R.hα (R.hNpos n) _
        (Real.rpow_pos_of_pos (hx0 n) α)).1) (hγ n).le
  rcases hα1.lt_or_eq with ha | ha
  · have hu := (vm_scale_negligible R hα1 i hx).const_mul (1 / (1 - α))
    simp only [mul_zero] at hu
    refine squeeze_zero' (Eventually.of_forall fun n => div_nonneg (hm n).le (sq_nonneg _))
      (Eventually.of_forall fun n => ?_) hu
    have hb := (hbound n).trans (mul_le_mul_of_nonneg_left
      (vm_contS_lt R.hα ha (Real.rpow_pos_of_pos (hx0 n) α)) (hγ n).le)
    calc _ ≤ (gammaOf (N n) (B n) * (rowFrac (i n) ^ α / (1 - α))) /
        (1 + bCoef α (B n) (i n)) ^ 2 :=
        div_le_div_of_nonneg_right hb (sq_nonneg _)
      _ = _ := by ring
  · subst α
    have hL : Tendsto (fun n => Real.log (1 / rowFrac (i n))) atTop atTop := by
      have := vm_L_tendsto (by norm_num : (0 : ℝ) < 1) hx0 hx
      simpa only [Real.rpow_neg_one, one_div] using this
    refine squeeze_zero' (Eventually.of_forall fun n => div_nonneg (hm n).le (sq_nonneg _))
      ?_ (vm_lim_one hγ hx0 hx)
    filter_upwards [hL.eventually_ge_atTop 1] with n hn
    have hc := vm_contS_one (hx0 n) (vm_rowFrac_bounds (i n)).2
    have hb := (hbound n).trans (mul_le_mul_of_nonneg_left (by
      simpa only [Real.rpow_one] using hc) (hγ n).le)
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlog : 0 ≤ Real.log (1 / rowFrac (i n)) := by linarith
    have hxn := hx0 n
    have hγn := hγ n
    have hbase : 0 ≤ gammaOf (N n) (B n) * rowFrac (i n) *
        (Real.log 2 + Real.log (1 / rowFrac (i n))) := by positivity
    have hmul := mul_le_mul_of_nonneg_left
      (by linarith : 1 ≤ 1 / 2 + Real.log (1 / rowFrac (i n))) hbase
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    simpa only [Real.rpow_one, mul_one, mul_assoc] using hb.trans (by
      simpa only [mul_one, mul_assoc] using hmul)

private lemma vm_middle_negligible {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (i : ∀ n, Fin (N n)) (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0))
    {δ M : ℝ} (hδ : 0 < δ) (hδM : δ < M) :
    Tendsto (fun n => vIJ β (B n) (plSpec α (c n) (N n)) (i n)
      (Ioo δ M) (Ioo δ M) / (1 + bCoef α (B n) (i n)) ^ 2) atTop (𝓝 0) := by
  obtain ⟨K, hK, hbound⟩ := vm_compact_square_bound R.hα R.hβ0 R.hβ1 hδ hδM
  have hu := (vm_m0_negligible R hα1 i hx).const_mul K
  simp only [mul_zero] at hu
  have hev := R.hγ.eventually_ge_atTop (2 * M + 2)
  refine squeeze_zero' ?_ ?_ hu
  · filter_upwards [hev] with n hn
    exact div_nonneg (hbound (N n) (B n) (c n)
      (R.hNpos n) (R.hBpos n) (R.hcpos n) hn (i n)).1 (sq_nonneg _)
  · filter_upwards [hev] with n hn
    have h := div_le_div_of_nonneg_right (hbound (N n) (B n) (c n)
      (R.hNpos n) (R.hBpos n) (R.hcpos n) hn (i n)).2
      (sq_nonneg (1 + bCoef α (B n) (i n)))
    simpa only [mul_div_assoc] using h

private lemma vm_upper_negligible {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (hPSD : volHPSD α β N B c) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (i : ∀ n, Fin (N n)) (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) :
    Tendsto (fun n => vIJ β (B n) (plSpec α (c n) (N n)) (i n)
      (Ico (η * gammaOf (N n) (B n)) (gammaOf (N n) (B n)))
      (Ico (η * gammaOf (N n) (B n)) (gammaOf (N n) (B n))) /
      (1 + bCoef α (B n) (i n)) ^ 2) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := lem_app_pl_upper (α := α) (β := β) η hη0 hη1
  have hup := (vm_scale_negligible R hα1 i hx).const_mul C
  simp only [mul_zero] at hup
  refine squeeze_zero' ?_ ?_ hup
  · refine Eventually.of_forall fun n => ?_
    have hγ : 0 < gammaOf (N n) (B n) := by
      unfold gammaOf
      exact div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n)
    have hsub : Ico (η * gammaOf (N n) (B n)) (gammaOf (N n) (B n)) ⊆
        Ioo 0 (gammaOf (N n) (B n)) := fun m hm => ⟨lt_of_lt_of_le (mul_pos hη0 hγ) hm.1, hm.2⟩
    exact div_nonneg (hPSD n (i n) _ _ ordConnected_Ico hsub ordConnected_Ico hsub).1 (sq_nonneg _)
  · filter_upwards [hC N B c R] with n hn
    have h := (hn (i n)).2.2
    have h' := div_le_div_of_nonneg_right h (sq_nonneg (1 + bCoef α (B n) (i n)))
    convert h' using 1 <;> simp only [rowFrac, rowIdx] <;> ring

private lemma vm_upper_cross_negligible {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (hPSD : volHPSD α β N B c) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) :
    Tendsto (fun n => vIJ β (B n) (plSpec α (c n) (N n)) (i n)
      (Ico (η * gammaOf (N n) (B n)) (gammaOf (N n) (B n)))
      (Ioo 0 (η * gammaOf (N n) (B n))) /
      (1 + bCoef α (B n) (i n)) ^ 2) atTop (𝓝 0) ∧
    Tendsto (fun n => vIJ β (B n) (plSpec α (c n) (N n)) (i n)
      (Ioo 0 (η * gammaOf (N n) (B n)))
      (Ico (η * gammaOf (N n) (B n)) (gammaOf (N n) (B n))) /
      (1 + bCoef α (B n) (i n)) ^ 2) atTop (𝓝 0) := by
  have hsets : ∀ n,
      Ioo 0 (η * gammaOf (N n) (B n)) ⊆ Ioo 0 (gammaOf (N n) (B n)) ∧
      Ico (η * gammaOf (N n) (B n)) (gammaOf (N n) (B n)) ⊆
        Ioo 0 (gammaOf (N n) (B n)) := by
    intro n
    have hγ : 0 < gammaOf (N n) (B n) := by
      unfold gammaOf
      exact div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n)
    constructor
    · intro m hm
      exact ⟨hm.1, hm.2.trans (by nlinarith)⟩
    · intro m hm
      exact ⟨lt_of_lt_of_le (mul_pos hη0 hγ) hm.1, hm.2⟩
  have hb : ∀ᶠ n in atTop, 0 ≤ bCoef α (B n) (i n) :=
    Eventually.of_forall fun n => vm_bCoef_nonneg R.hα (i n)
  have ha := vm_upper_negligible R hα1 hPSD η hη0 hη1 i hx
  have hd := vm_interior_bigO R hα1 η hη0 hη1 i hi hx
  constructor
  · apply vm_psd_cross_negligible hb _ ha hd
    exact Eventually.of_forall fun n =>
      hPSD n (i n) _ _ ordConnected_Ico (hsets n).2 ordConnected_Ioo (hsets n).1
  · apply vm_psd_cross_negligible hb _ ha hd
    refine Eventually.of_forall fun n => ?_
    simpa only [mul_comm] using
      hPSD n (i n) _ _ ordConnected_Ioo (hsets n).1 ordConnected_Ico (hsets n).2

private lemma vm_middle_cross_negligible {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (hPSD : volHPSD α β N B c) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0))
    {δ M : ℝ} (hδ : 0 < δ) (hδM : δ < M) :
    Tendsto (fun n => vIJ β (B n) (plSpec α (c n) (N n)) (i n)
      (Ioo δ M) (Ioo 0 (η * gammaOf (N n) (B n))) /
      (1 + bCoef α (B n) (i n)) ^ 2) atTop (𝓝 0) ∧
    Tendsto (fun n => vIJ β (B n) (plSpec α (c n) (N n)) (i n)
      (Ioo 0 (η * gammaOf (N n) (B n))) (Ioo δ M) /
      (1 + bCoef α (B n) (i n)) ^ 2) atTop (𝓝 0) := by
  have hsets : ∀ᶠ n in atTop,
      Ioo δ M ⊆ Ioo 0 (gammaOf (N n) (B n)) ∧
      Ioo 0 (η * gammaOf (N n) (B n)) ⊆ Ioo 0 (gammaOf (N n) (B n)) := by
    filter_upwards [R.hγ.eventually_ge_atTop M] with n hn
    have hγ : 0 < gammaOf (N n) (B n) := by
      unfold gammaOf
      exact div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n)
    exact ⟨fun m hm => ⟨hδ.trans hm.1, hm.2.trans_le hn⟩,
      fun m hm => ⟨hm.1, hm.2.trans (by nlinarith)⟩⟩
  have hb : ∀ᶠ n in atTop, 0 ≤ bCoef α (B n) (i n) :=
    Eventually.of_forall fun n => vm_bCoef_nonneg R.hα (i n)
  have ha := vm_middle_negligible R hα1 i hx hδ hδM
  have hd := vm_interior_bigO R hα1 η hη0 hη1 i hi hx
  constructor
  · apply vm_psd_cross_negligible hb _ ha hd
    filter_upwards [hsets] with n hn
    exact hPSD n (i n) _ _ ordConnected_Ioo hn.1 ordConnected_Ioo hn.2
  · apply vm_psd_cross_negligible hb _ ha hd
    filter_upwards [hsets] with n hn
    simpa only [mul_comm] using
      hPSD n (i n) _ _ ordConnected_Ioo hn.2 ordConnected_Ioo hn.1

private lemma vm_negligible_of_small_flat {e f d : ℕ → ℝ}
    (hd : ∀ n, 0 < d n) (he : ∀ᶠ n in atTop, 0 ≤ e n)
    (hf : IsBigO atTop f d)
    (hbound : ∀ q : ℝ, 0 < q → ∃ r : ℕ → ℝ,
      Tendsto (fun n => r n / d n) atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, e n ≤ q * f n + r n) :
    Tendsto (fun n => e n / d n) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := hf.bound
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [he] with n hn
    exact ha.trans_le (div_nonneg hn (hd n).le)
  · intro a ha
    let k : ℝ := |K| + 1
    have hk : 0 < k := by dsimp [k]; positivity
    let q : ℝ := a / (4 * k)
    have hq : 0 < q := div_pos ha (mul_pos (by norm_num) hk)
    obtain ⟨r, hr, hcomp⟩ := hbound q hq
    have hsmall : ∀ᶠ n in atTop, r n / d n < a / 2 :=
      (tendsto_order.1 hr).2 _ (by linarith)
    have hqk : q * k = a / 4 := by dsimp [q]; field_simp
    filter_upwards [hK, hcomp, hsmall] with n hn hc hs
    have hfn : f n ≤ k * d n := by
      have hn' : |f n| ≤ K * d n := by
        simpa only [Real.norm_eq_abs, abs_of_pos (hd n)] using hn
      calc f n ≤ |f n| := le_abs_self _
        _ ≤ K * d n := hn'
        _ ≤ k * d n := mul_le_mul_of_nonneg_right (by dsimp [k]; linarith [le_abs_self K]) (hd n).le
    have hfd : f n / d n ≤ k := (div_le_iff₀ (hd n)).2 hfn
    have hh := div_le_div_of_nonneg_right hc (hd n).le
    rw [add_div, mul_div_assoc] at hh
    have hmul := mul_le_mul_of_nonneg_left hfd hq.le
    linarith

private lemma vm_meso_of_comparison {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0))
    (hcompare : Tendsto (fun n =>
      (vPart β (B n) (plSpec α (c n) (N n)) (i n) -
        vFlat β (B n) (plSpec α (c n) (N n)) (i n)) /
          (1 + bCoef α (B n) (i n)) ^ 2) atTop (𝓝 0)) :
    IsEquivalent atTop
      (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => 1 / sPow β 2 + 2 * c0 / Real.sqrt (sPow β 2) * bCoef α (B n) (i n) +
        bCoef α (B n) (i n) ^ 2) := by
  let Q : ℕ → ℝ := fun n => 1 / sPow β 2 +
    2 * c0 / Real.sqrt (sPow β 2) * bCoef α (B n) (i n) + bCoef α (B n) (i n) ^ 2
  let D : ℕ → ℝ := fun n => (1 + bCoef α (B n) (i n)) ^ 2
  have hdiff : Tendsto (fun n =>
      (vPart β (B n) (plSpec α (c n) (N n)) (i n) - Q n) / D n) atTop (𝓝 0) := by
    have h := hcompare.add (vm_flat_error R hα1 i hi hx)
    simp only [add_zero] at h
    convert h using 1
    ext n
    dsimp [Q, D]
    ring
  have hD : ∀ n, 0 < D n := fun n => by
    have := vm_bCoef_nonneg (B := B n) R.hα (i n)
    dsimp [D]
    positivity
  have hlo : IsLittleO atTop
      (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n) - Q n) D :=
    (isLittleO_iff_tendsto (fun n hn => ((hD n).ne' hn).elim)).2 hdiff
  let k : ℝ := min (1 / sPow β 2) 1 / 2
  have hs : 0 < sPow β 2 := by
    rw [sPow_two R.hβ0.le R.hβ1]
    exact div_pos (by linarith [R.hβ1]) (by linarith [R.hβ0])
  have hk : 0 < k := div_pos (lt_min (one_div_pos.2 hs) (by norm_num)) (by norm_num)
  have hbig : IsBigO atTop D Q := by
    refine IsBigO.of_bound (1 / k) (Eventually.of_forall fun n => ?_)
    have hl : k * D n ≤ Q n :=
      (vm_quadratic_bounds R.hβ0 R.hβ1 (vm_bCoef_nonneg R.hα (i n))).1
    have hQ : 0 < Q n := lt_of_lt_of_le (mul_pos hk (hD n)) hl
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hD n), abs_of_pos hQ]
    calc D n ≤ Q n / k := (le_div_iff₀ hk).2 (by simpa only [mul_comm] using hl)
      _ = _ := by ring
  exact hlo.trans_isBigO hbig

/-- `lem:app-pl-meso` (snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Mesoscopic crossover]\label{lem:app-pl-meso}
Let $0<\alpha\le1$. Along every row sequence $i\to\infty$ with $i/N\to0$,
\[
\mathfrak v_i(0)\sim\frac1{\sw2}+\frac{2c_0}{\sqrt{\sw2}}\,b_{i,N}+b_{i,N}^2 .
\]
\end{lemma}

The flat coefficient `𝔳_i(0)` is the part-form `vPart` (card §2); `hPSD` is `volHPSD`. -/
theorem lem_app_pl_meso {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (hPSD : volHPSD α β N B c) (hZero : volHZero α β N B c)
    (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) :
    IsEquivalent atTop
      (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => 1 / sPow β 2 + 2 * c0 / Real.sqrt (sPow β 2) * bCoef α (B n) (i n) +
        bCoef α (B n) (i n) ^ 2) := by
  classical
  let d : ℕ → ℝ := fun n => (1 + bCoef α (B n) (i n)) ^ 2
  let f : ℕ → ℝ := fun n => vFlat β (B n) (plSpec α (c n) (N n)) (i n)
  let e : ℕ → ℝ := fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n) - f n
  have hd : ∀ n, 0 < d n := by
    intro n
    have := vm_bCoef_nonneg (B := B n) R.hα (i n)
    dsimp [d]; positivity
  have he : ∀ᶠ n in atTop, 0 ≤ e n := Eventually.of_forall fun n =>
    vm_flat_le_part R.hα R.hβ0 R.hβ1 (N n) (B n) (c n)
      (R.hNpos n) (R.hBpos n) (R.hcpos n) (i n) (hZero n (i n))
  have hf : IsBigO atTop f d := vm_flat_bigO R hα1 i hi hx
  have hbound : ∀ q : ℝ, 0 < q → ∃ r : ℕ → ℝ,
      Tendsto (fun n => r n / d n) atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, e n ≤ q * f n + r n := by
    intro q hq
    obtain ⟨C, hC, hgood⟩ := vm_good_region_bound R.hα R.hβ0 R.hβ1
    have hparams : ∃ δ η Rr : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < η ∧ η < 1 / 2 ∧
        1 < Rr ∧ C * δ + Rr⁻¹ + 2 * η < 1 / 2 ∧
        2 * (C * δ + Rr⁻¹ + 2 * η) ≤ q := by
      let t : ℝ := min q 1 / 16
      have ht0 : 0 < t := by dsimp [t]; positivity
      have ht1 : t ≤ 1 / 16 := by
        dsimp [t]; linarith [min_le_right q (1 : ℝ)]
      have htq : 16 * t ≤ q := by
        dsimp [t]; linarith [min_le_left q (1 : ℝ)]
      have hcp : 0 < C + 1 := by linarith
      have hd0 : 0 < t / (C + 1) := div_pos ht0 hcp
      have hdeq : t / (C + 1) * (C + 1) = t := div_mul_cancel₀ _ hcp.ne'
      have hcd : C * (t / (C + 1)) ≤ t := by nlinarith
      have hd1 : t / (C + 1) ≤ 1 := by nlinarith
      have hr1 : 1 < t⁻¹ := by
        rw [← one_div]
        exact (lt_div_iff₀ ht0).2 (by linarith)
      refine ⟨t / (C + 1), t / 2, t⁻¹, hd0, hd1, by positivity,
        by linarith, hr1, ?_, ?_⟩ <;> simp only [inv_inv] <;> linarith
    obtain ⟨δ, η, Rr, hδ, hδ1, hη, hηhalf, hRr, ht, hsmall⟩ := hparams
    have hη1 : η < 1 := by linarith
    let L : ℕ → Set ℝ := fun n => Ioo 0 (η * gammaOf (N n) (B n))
    let U : ℕ → Set ℝ := fun n => Ico (η * gammaOf (N n) (B n)) (gammaOf (N n) (B n))
    let J : Set ℝ := Ioo δ 2
    let T : ℕ → Set (ℝ × ℝ) := fun n => stripSet η Rr 1 (gammaOf (N n) (B n))
    let V : ℕ → Set ℝ → Set ℝ → ℝ := fun n I J =>
      vIJ β (B n) (plSpec α (c n) (N n)) (i n) I J
    let a : ℕ → ℝ := fun n => (Real.pi ^ 2)⁻¹ * ∑' ℓ : ℤ, ∫ p in T n,
      lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ p.1 p.2
    let r : ℕ → ℝ := fun n => V n (U n) (U n) + V n (U n) (L n) +
      V n (L n) (U n) + V n J (L n) + V n (L n) J + a n
    have hr : Tendsto (fun n => r n / d n) atTop (𝓝 0) := by
      have hu := vm_upper_negligible R hα1 hPSD η hη hη1 i hx
      have huc := vm_upper_cross_negligible R hα1 hPSD η hη hη1 i hi hx
      have hmc := vm_middle_cross_negligible R hα1 hPSD η hη hη1 i hi hx
        hδ (show δ < (2 : ℝ) by linarith)
      have hs := (lem_app_pl_strip R hα1 Rr 1 η hRr le_rfl hη hηhalf i hi hx).2.2
      simpa only [r, V, U, L, J, a, T, d, add_div, add_zero] using
        (((((hu.add huc.1).add huc.2).add hmc.1).add hmc.2).add hs)
    refine ⟨r, hr, ?_⟩
    filter_upwards [R.hγ.eventually_ge_atTop 2] with n hn
    change 2 ≤ gammaOf (N n) (B n) at hn
    have hγ : 0 < gammaOf (N n) (B n) := by linarith
    let G := (L n ×ˢ L n) \ ((J ×ˢ L n) ∪ (L n ×ˢ J) ∪ T n)
    let S : Fin 7 → Set (ℝ × ℝ) :=
      ![U n ×ˢ U n, U n ×ˢ L n, L n ×ˢ U n, J ×ˢ L n, L n ×ˢ J, T n, G]
    have hcover := vm_meso_region_cover (Rr := Rr) hγ hδ hη hη1 hn
    have hb := vm_error_cover_bound R.hα R.hβ0 R.hβ1 (N n) (B n) (c n)
      (R.hNpos n) (R.hBpos n) (R.hcpos n) (i n) (hZero n (i n)) S
      hcover.1 hcover.2.1 hcover.2.2
    have hG := hgood (N n) (B n) (c n) (R.hNpos n) (R.hBpos n) (R.hcpos n)
      (i n) δ η Rr hδ hδ1 hη hη1 hRr (by linarith) ht
    have hsum : (∑ k, (Real.pi ^ 2)⁻¹ * ∑' ℓ : ℤ, ∫ p in S k,
        (lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ p.1 p.2 -
          lagNumer β (B n) (plSpec α (c n) (N n)) (i n) ℓ p.1 p.2)) ≤
        2 * (C * δ + Rr⁻¹ + 2 * η) * f n + r n := by
      let E : Fin 7 → ℝ := fun k => (Real.pi ^ 2)⁻¹ * ∑' ℓ : ℤ, ∫ p in S k,
        (lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ p.1 p.2 -
          lagNumer β (B n) (plSpec α (c n) (N n)) (i n) ℓ p.1 p.2)
      have hL : L n ⊆ Ioo 0 (gammaOf (N n) (B n)) :=
        fun m hm => ⟨hm.1, hm.2.trans (by nlinarith)⟩
      have hU : U n ⊆ Ioo 0 (gammaOf (N n) (B n)) :=
        fun m hm => ⟨lt_of_lt_of_le (mul_pos hη hγ) hm.1, hm.2⟩
      have hJ : J ⊆ Ioo 0 (gammaOf (N n) (B n)) :=
        fun m hm => ⟨hδ.trans hm.1, hm.2.trans_le hn⟩
      have h0 : E 0 ≤ V n (U n) (U n) :=
        vm_rectangle_error_bound R.hα R.hβ0 R.hβ1 (R.hNpos n) (R.hBpos n)
          (R.hcpos n) (i n) measurableSet_Ico measurableSet_Ico hU hU
      have h1 : E 1 ≤ V n (U n) (L n) :=
        vm_rectangle_error_bound R.hα R.hβ0 R.hβ1 (R.hNpos n) (R.hBpos n)
          (R.hcpos n) (i n) measurableSet_Ico measurableSet_Ioo hU hL
      have h2 : E 2 ≤ V n (L n) (U n) :=
        vm_rectangle_error_bound R.hα R.hβ0 R.hβ1 (R.hNpos n) (R.hBpos n)
          (R.hcpos n) (i n) measurableSet_Ioo measurableSet_Ico hL hU
      have h3 : E 3 ≤ V n J (L n) :=
        vm_rectangle_error_bound R.hα R.hβ0 R.hβ1 (R.hNpos n) (R.hBpos n)
          (R.hcpos n) (i n) measurableSet_Ioo measurableSet_Ioo hJ hL
      have h4 : E 4 ≤ V n (L n) J :=
        vm_rectangle_error_bound R.hα R.hβ0 R.hβ1 (R.hNpos n) (R.hBpos n)
          (R.hcpos n) (i n) measurableSet_Ioo measurableSet_Ioo hL hJ
      have h5 : E 5 ≤ a n :=
        (vm_region_summability R.hα R.hβ0 R.hβ1 (R.hNpos n) (R.hBpos n)
          (R.hcpos n) (i n) (hcover.1 5) (hcover.2.1 5)).2.2.2
      have h6 : E 6 ≤ 2 * (C * δ + Rr⁻¹ + 2 * η) * f n := hG
      change (∑ k, E k) ≤ _
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      change E 0 + (E 1 + (E 2 + (E 3 + (E 4 + (E 5 + E 6))))) ≤ _
      dsimp only [r]
      linarith only [h0, h1, h2, h3, h4, h5, h6]
    have hflat : 0 ≤ f n :=
      (lem_app_pl_age_iv R.hα R.hβ0 R.hβ1 (N n) (B n) (c n)
        (R.hNpos n) (R.hBpos n) (R.hcpos n) (i n)).2.2.2.2.1
    exact hb.trans (hsum.trans (add_le_add
      (mul_le_mul_of_nonneg_right hsmall hflat) le_rfl))
  exact vm_meso_of_comparison R hα1 i hi hx
    (vm_negligible_of_small_flat hd he hf hbound)

private lemma vm_meso_equiv_vhat {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (hPSD : volHPSD α β N B c) (hZero : volHZero α β N B c)
    (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) :
    IsEquivalent atTop
      (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => vhatApprox β α (B n) (i n)) := by
  exact (lem_app_pl_meso R hα1 hPSD hZero i hi hx).trans
    (vm_vhat_equiv_quadratic R hα1 i hx).symm

private lemma vm_bulk_equiv_vhat {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hBound : volHBound α β N B c)
    (i : ∀ n, Fin (N n)) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1)
    (hix : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 x)) :
    IsEquivalent atTop
      (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => vhatApprox β α (B n) (i n)) := by
  let K : Set ℝ := Icc (x / 2) 1
  have hK : K ⊆ Ioc (0 : ℝ) 1 := by
    intro y hy
    exact ⟨lt_of_lt_of_le (half_pos hx.1) hy.1, hy.2⟩
  have hKc : IsCompact K := isCompact_Icc
  have hiK : ∀ᶠ n in atTop, rowFrac (i n) ∈ K := by
    filter_upwards [hix.eventually (lt_mem_nhds (half_lt_self hx.1))] with n hn
    exact ⟨hn.le, (vm_rowFrac_bounds (i n)).2⟩
  have hu := (thm_app_pl_volatility_i_part R hBound).2 K hK hKc
  have herrAbs : Tendsto (fun n => |vPart β (B n) (plSpec α (c n) (N n)) (i n) /
      gammaOf (N n) (B n) - profGamma α (rowFrac (i n))|) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    filter_upwards [hu (ε / 2) (half_pos hε), hiK] with n hn hnK
    have hh := hn (i n) hnK
    rw [Real.dist_eq, sub_zero, abs_abs]
    have hh' : |vPart β (B n) (plSpec α (c n) (N n)) (i n) /
        gammaOf (N n) (B n) - profGamma α (rowFrac (i n))| ≤ ε / 2 := by
      simpa only [rowFrac, rowIdx] using hh
    linarith
  have herr : Tendsto (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n) /
      gammaOf (N n) (B n) - profGamma α (rowFrac (i n))) atTop (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 herrAbs
  have hprof : Tendsto (fun n => profGamma α (rowFrac (i n))) atTop (𝓝 (profGamma α x)) :=
    ((lem_app_pl_Gamma_helper_cont R.hα) x hx).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hix, Eventually.of_forall fun n => vm_rowFrac_bounds (i n)⟩)
  have hprofPos : 0 < profGamma α x := lem_app_pl_Gamma_helper_pos R.hα x hx
  have hvnorm : Tendsto (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n) /
      gammaOf (N n) (B n)) atTop (𝓝 (profGamma α x)) := by
    convert herr.add hprof using 1
    · ext n
      ring
    · ring
  let A : ℕ → ℝ := fun n => gammaOf (N n) (B n) * profGamma α (rowFrac (i n))
  have hApos : ∀ n, 0 < A n := by
    intro n
    exact mul_pos (by
      unfold gammaOf
      exact div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n))
      (lem_app_pl_Gamma_helper_pos R.hα _ (vm_rowFrac_bounds (i n)))
  have hAtop : Tendsto A atTop atTop := R.hγ.atTop_mul_pos hprofPos hprof
  have hvA : IsEquivalent atTop
      (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n)) A := by
    rw [isEquivalent_iff_tendsto_one (Eventually.of_forall fun n => (hApos n).ne')]
    have hh := hvnorm.div hprof (ne_of_gt hprofPos)
    rw [div_self (ne_of_gt hprofPos)] at hh
    refine hh.congr' (Eventually.of_forall fun n => ?_)
    dsimp only [A]
    have hγ : gammaOf (N n) (B n) ≠ 0 := by
      unfold gammaOf
      exact (div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n)).ne'
    have hG : profGamma α (rowFrac (i n)) ≠ 0 :=
      (lem_app_pl_Gamma_helper_pos R.hα _ (vm_rowFrac_bounds (i n))).ne'
    change (vPart β (B n) (plSpec α (c n) (N n)) (i n) /
      gammaOf (N n) (B n)) / profGamma α (rowFrac (i n)) =
      vPart β (B n) (plSpec α (c n) (N n)) (i n) /
        (gammaOf (N n) (B n) * profGamma α (rowFrac (i n)))
    field_simp
  have hInvA : Tendsto (fun n => 1 / A n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hAtop
  have hInvSqrtA : Tendsto (fun n => 1 / Real.sqrt (A n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hAtop)
  have hvhatRatio : Tendsto (fun n => vhatApprox β α (B n) (i n) / A n)
      atTop (𝓝 1) := by
    have h1 := hInvA.const_mul (1 / sPow β 2)
    have h2 := hInvSqrtA.const_mul (2 * c0 / Real.sqrt (sPow β 2))
    simp only [mul_zero] at h1 h2
    have h := (h1.add h2).add_const 1
    simp only [zero_add] at h
    refine h.congr' (Eventually.of_forall fun n => ?_)
    have hAn := hApos n
    have hsquare := Real.sq_sqrt hAn.le
    change 1 / sPow β 2 * (1 / A n) +
        2 * c0 / Real.sqrt (sPow β 2) * (1 / Real.sqrt (A n)) + 1 =
      (1 / sPow β 2 + 2 * c0 / Real.sqrt (sPow β 2) * Real.sqrt (A n) + A n) / A n
    have hinv : 1 / Real.sqrt (A n) = Real.sqrt (A n) / A n := by
      have hsqrt : Real.sqrt (A n) ≠ 0 := (Real.sqrt_pos.2 hAn).ne'
      field_simp [hsqrt, hAn.ne']
      nlinarith
    rw [hinv]
    field_simp [hAn.ne']
  have hvhatA : IsEquivalent atTop (fun n => vhatApprox β α (B n) (i n)) A :=
    (isEquivalent_iff_tendsto_one (Eventually.of_forall fun n => (hApos n).ne')).2 hvhatRatio
  exact hvA.trans hvhatA.symm

private lemma vm_explicit_lt_of_profile {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (i : ∀ n, Fin (N n))
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) (hα1 : α < 1)
    (hv : IsEquivalent atTop
      (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => gammaOf (N n) (B n) * profGamma α (rowFrac (i n)))) :
    IsEquivalent atTop
      (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => gammaOf (N n) (B n) * rowFrac (i n) ^ α *
        Real.log (((N n : ℝ) / rowIdx (i n)) ^ α) ^ 2 / (1 - α)) := by
  have hp := (vm_profiles_gamma_lt R.hα hα1).comp_tendsto
    (vm_pull (fun n => (vm_rowFrac_bounds (i n)).1) hx)
  have hm := (IsEquivalent.refl
    (u := fun n => gammaOf (N n) (B n))).mul hp
  refine hv.trans (hm.congr_right (Eventually.of_forall fun n => ?_))
  have hr : 0 < rowIdx (i n) := by unfold rowIdx; positivity
  have hN : (0 : ℝ) < N n := by exact_mod_cast R.hNpos n
  have he : rowFrac (i n) ^ (-α) = ((N n : ℝ) / rowIdx (i n)) ^ α := by
    unfold rowFrac
    rw [Real.rpow_neg (div_pos hr hN).le, ← Real.inv_rpow (div_pos hr hN).le, inv_div]
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [he]
  ring

private lemma vm_explicit_one_of_profile {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (i : ∀ n, Fin (N n))
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) (hα : α = 1)
    (hv : IsEquivalent atTop
      (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => gammaOf (N n) (B n) * profGamma α (rowFrac (i n)))) :
    IsEquivalent atTop
      (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => 4 / 9 * (rowIdx (i n) / (B n : ℝ)) *
        Real.log ((N n : ℝ) / rowIdx (i n)) ^ 3) := by
  have hp := (vm_profiles_gamma_one hα).comp_tendsto
    (vm_pull (fun n => (vm_rowFrac_bounds (i n)).1) hx)
  have hm := (IsEquivalent.refl
    (u := fun n => gammaOf (N n) (B n))).mul hp
  refine hv.trans (hm.congr_right (Eventually.of_forall fun n => ?_))
  have hr : 0 < rowIdx (i n) := by unfold rowIdx; positivity
  have hN : (0 : ℝ) < N n := by exact_mod_cast R.hNpos n
  have hB : (0 : ℝ) < B n := by exact_mod_cast R.hBpos n
  have he : 1 / rowFrac (i n) = (N n : ℝ) / rowIdx (i n) := by
    unfold rowFrac
    field_simp
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [he]
  unfold gammaOf rowFrac
  field_simp

/-! ### Crossover index and the profile `v ~ y^α` (task P-G.8.P4; private helpers) -/

private lemma vm_a_tendsto {ℓ : ℕ → ℝ} (hℓ : Tendsto ℓ atTop atTop) (p : ℕ) (c : ℝ) :
    Tendsto (fun n => 1 + (p * Real.log (ℓ n) + c) / ℓ n) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n => Real.log (ℓ n) / ℓ n) atTop (𝓝 0) :=
    (Real.isLittleO_log_id_atTop.comp_tendsto hℓ).tendsto_div_nhds_zero
  have h2 : Tendsto (fun n => c / ℓ n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hℓ
  have h3 := ((h1.const_mul (p : ℝ)).add h2).const_add 1
  simp only [mul_zero, add_zero] at h3
  refine h3.congr (fun n => ?_)
  rw [add_div, mul_div_assoc]

private lemma vm_R_eq {ℓ y R : ℕ → ℝ} {α : ℝ} {p : ℕ} {c : ℝ}
    (hℓ : ∀ᶠ n in atTop, 0 < ℓ n)
    (hR : ∀ᶠ n in atTop, R n * ℓ n = ℓ n + p * Real.log (ℓ n) + c - α * Real.log (y n)) :
    ∀ᶠ n in atTop, R n = (1 + (p * Real.log (ℓ n) + c) / ℓ n) - α * Real.log (y n) / ℓ n := by
  filter_upwards [hℓ, hR] with n h1 h2
  field_simp
  linarith

private lemma vm_R_mid {ℓ y R : ℕ → ℝ} {α : ℝ} {p : ℕ} {c y0 : ℝ}
    (hℓ : Tendsto ℓ atTop atTop) (hy0 : 0 < y0) (hy : Tendsto y atTop (𝓝 y0))
    (hR : ∀ᶠ n in atTop, R n * ℓ n = ℓ n + p * Real.log (ℓ n) + c - α * Real.log (y n)) :
    Tendsto (fun n => y n ^ α * R n ^ p) atTop (𝓝 (y0 ^ α)) := by
  have hR1 : Tendsto R atTop (𝓝 1) := by
    have hlog : Tendsto (fun n => Real.log (y n)) atTop (𝓝 (Real.log y0)) :=
      (Real.continuousAt_log hy0.ne').tendsto.comp hy
    have h2 : Tendsto (fun n => α * Real.log (y n) / ℓ n) atTop (𝓝 0) :=
      (hlog.const_mul α).div_atTop hℓ
    have h3 := (vm_a_tendsto hℓ p c).sub h2
    rw [sub_zero] at h3
    exact h3.congr' ((vm_R_eq (hℓ.eventually_gt_atTop 0) hR).mono fun n hn => hn.symm)
  have h1 : Tendsto (fun n => y n ^ α) atTop (𝓝 (y0 ^ α)) :=
    (Real.continuousAt_rpow_const y0 α (Or.inl hy0.ne')).tendsto.comp hy
  have h2 := hR1.pow p
  rw [one_pow] at h2
  simpa using h1.mul h2


private lemma vm_R_small {ℓ y R : ℕ → ℝ} {α : ℝ} {p : ℕ} {c : ℝ} (hα : 0 < α)
    (hℓ : Tendsto ℓ atTop atTop) (hy : Tendsto y atTop (𝓝[>] 0))
    (hR : ∀ᶠ n in atTop, R n * ℓ n = ℓ n + p * Real.log (ℓ n) + c - α * Real.log (y n))
    (hR0 : ∀ᶠ n in atTop, 0 ≤ R n) :
    Tendsto (fun n => y n ^ α * R n ^ p) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n => Real.log (y n)) atTop atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hy
  have hu : Tendsto (fun n => 2 - α * Real.log (y n)) atTop atTop := by
    have := hlog.const_mul_atBot hα
    have h := tendsto_atTop_add_const_left atTop (2:ℝ) (tendsto_neg_atBot_atTop.comp this)
    exact h.congr (fun n => by simp only [Function.comp]; ring)
  have hmain : Tendsto (fun n => (2 - α * Real.log (y n)) ^ p * Real.exp (-(2 - α * Real.log (y n))))
      atTop (𝓝 0) := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero p).comp hu
  have hmain' := hmain.const_mul (Real.exp 2)
  rw [mul_zero] at hmain'
  have ha := vm_a_tendsto hℓ p c
  have hy0 : ∀ᶠ n in atTop, 0 < y n := hy.eventually self_mem_nhdsWithin
  have hy1 : ∀ᶠ n in atTop, y n < 1 :=
    (tendsto_nhdsWithin_iff.1 hy).1.eventually (eventually_lt_nhds (show (0:ℝ) < 1 by norm_num))
  refine squeeze_zero' ?_ ?_ hmain'
  · filter_upwards [hy0, hR0] with n h1 h2
    exact mul_nonneg (Real.rpow_nonneg h1.le _) (pow_nonneg h2 _)
  · filter_upwards [vm_R_eq (hℓ.eventually_gt_atTop 0) hR, hR0, hℓ.eventually_ge_atTop 1,
      ha.eventually (gt_mem_nhds (show (1:ℝ) < 2 by norm_num)), hy0, hy1] with n h1 h2 h3 h4 h5 h6
    have hlogneg : Real.log (y n) ≤ 0 := (Real.log_neg h5 h6).le
    have hRle : R n ≤ 2 - α * Real.log (y n) := by
      rw [h1]
      have : -(α * Real.log (y n)) ≤ -(α * Real.log (y n)) * ℓ n := by nlinarith [mul_nonneg hα.le (neg_nonneg.2 hlogneg)]
      have h7 : -(α * Real.log (y n)) / ℓ n ≤ -(α * Real.log (y n)) := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [mul_nonneg hα.le (neg_nonneg.2 hlogneg)]
      have : α * Real.log (y n) / ℓ n = -(-(α * Real.log (y n)) / ℓ n) := by ring
      linarith
    have hye : y n ^ α = Real.exp 2 * Real.exp (-(2 - α * Real.log (y n))) := by
      rw [Real.rpow_def_of_pos h5, ← Real.exp_add]; congr 1; ring
    rw [hye, mul_assoc]
    have hp : R n ^ p ≤ (2 - α * Real.log (y n)) ^ p := pow_le_pow_left₀ h2 hRle p
    have := mul_le_mul_of_nonneg_left hp (Real.exp_pos (-(2 - α * Real.log (y n)))).le
    nlinarith [Real.exp_pos 2, Real.exp_pos (-(2 - α * Real.log (y n)))]

private lemma vm_R_big {ℓ y R : ℕ → ℝ} {α : ℝ} {p : ℕ} {c : ℝ} (hα : 0 < α)
    (hℓ : Tendsto ℓ atTop atTop) (hy : Tendsto y atTop atTop)
    (hR : ∀ᶠ n in atTop, R n * ℓ n = ℓ n + p * Real.log (ℓ n) + c - α * Real.log (y n))
    (hRlow : ∀ᶠ n in atTop, α / ℓ n ≤ R n) :
    Tendsto (fun n => y n ^ α * R n ^ p) atTop atTop := by
  have ha := vm_a_tendsto hℓ p c
  have hf : Tendsto (fun n => y n ^ α * (1 / 4 : ℝ) ^ p) atTop atTop :=
    ((tendsto_rpow_atTop hα).comp hy).atTop_mul_const (by positivity)
  have hg : Tendsto (fun n => Real.exp (ℓ n / 2) * (α / ℓ n) ^ p) atTop atTop := by
    have h1 := (tendsto_exp_mul_div_rpow_atTop (p : ℝ) (1 / 2) (by norm_num)).comp hℓ
    have h2 := h1.const_mul_atTop (show 0 < α ^ p by positivity)
    refine h2.congr (fun n => ?_)
    simp only [Function.comp, Real.rpow_natCast]
    rw [div_pow]
    have : 1 / 2 * ℓ n = ℓ n / 2 := by ring
    rw [this]; ring
  have hmin : Tendsto (fun n => min (y n ^ α * (1 / 4 : ℝ) ^ p)
      (Real.exp (ℓ n / 2) * (α / ℓ n) ^ p)) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [tendsto_atTop.1 hf b, tendsto_atTop.1 hg b] with n h1 h2
    exact le_min h1 h2
  refine tendsto_atTop_mono' atTop ?_ hmin
  filter_upwards [vm_R_eq (hℓ.eventually_gt_atTop 0) hR, hRlow, hℓ.eventually_gt_atTop 0,
    hy.eventually_gt_atTop 0, ha.eventually (lt_mem_nhds (show (3 / 4 : ℝ) < 1 by norm_num))]
    with n h1 h2 h3 h4 h5
  by_cases hc : (1 / 4 : ℝ) ≤ R n
  · refine (min_le_left _ _).trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hc p)
      (Real.rpow_nonneg h4.le _)
  · push Not at hc
    refine (min_le_right _ _).trans ?_
    have hlog : ℓ n / 2 ≤ α * Real.log (y n) := by
      have : α * Real.log (y n) / ℓ n > 1 / 2 := by rw [h1] at hc; linarith
      rw [gt_iff_lt, lt_div_iff₀ h3] at this
      linarith
    have hye : Real.exp (ℓ n / 2) ≤ y n ^ α := by
      rw [Real.rpow_def_of_pos h4]
      exact Real.exp_le_exp.2 (by rw [mul_comm]; exact hlog)
    calc Real.exp (ℓ n / 2) * (α / ℓ n) ^ p ≤ y n ^ α * (α / ℓ n) ^ p :=
          mul_le_mul_of_nonneg_right hye (by positivity)
      _ ≤ y n ^ α * R n ^ p :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2 p) (Real.rpow_nonneg h4.le _)

private lemma vm_core_alg {α s A γ κ y x ℓ : ℝ} {p : ℕ} (hα : 0 < α) (hs : 0 < s) (hA : 0 < A)
    (hγ : 0 < γ) (hℓ : 0 < ℓ) (hκ : 0 < κ) (hy : 0 < y) (hx : x = y * κ)
    (hℓdef : ℓ = Real.log γ)
    (hK : A * γ * κ ^ α * ℓ ^ p = α ^ p / s) :
    s * (A * γ * x ^ α * Real.log (1 / x) ^ p) = y ^ α * (α * Real.log (1 / x) / ℓ) ^ p ∧
    (α * Real.log (1 / x)) = ℓ + p * Real.log ℓ + Real.log (A * s / α ^ p) - α * Real.log y := by
  have hxpos : 0 < x := by rw [hx]; positivity
  have hlogx : Real.log (1 / x) = -(Real.log y + Real.log κ) := by
    rw [one_div, Real.log_inv, hx, Real.log_mul hy.ne' hκ.ne']
  have hKl : Real.log A + Real.log γ + α * Real.log κ + p * Real.log ℓ =
      p * Real.log α - Real.log s := by
    have := congrArg Real.log hK
    rw [Real.log_div (by positivity) hs.ne', Real.log_pow,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul hA.ne' hγ.ne', Real.log_rpow hκ, Real.log_pow] at this
    linarith
  have hc : Real.log (A * s / α ^ p) = Real.log A + Real.log s - p * Real.log α := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul hA.ne' hs.ne', Real.log_pow]
  have h2 : (α * Real.log (1 / x)) = ℓ + p * Real.log ℓ + Real.log (A * s / α ^ p) - α * Real.log y := by
    rw [hc, hlogx, ← hℓdef] at *
    rw [← hℓdef] at hKl
    linarith
  refine ⟨?_, h2⟩
  have hxa : x ^ α = y ^ α * κ ^ α := by rw [hx, Real.mul_rpow hy.le hκ.le]
  rw [div_pow, mul_pow, hxa]
  have hℓp : 0 < ℓ ^ p := by positivity
  have hmain : s * (A * γ * κ ^ α * ℓ ^ p) = α ^ p := by rw [hK]; field_simp
  calc s * (A * γ * (y ^ α * κ ^ α) * Real.log (1 / x) ^ p)
      = y ^ α * Real.log (1 / x) ^ p * (s * (A * γ * κ ^ α * ℓ ^ p)) / ℓ ^ p := by
        field_simp
    _ = _ := by rw [hmain]; field_simp

private lemma vm_icv_data {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1) :
    ∃ (A : ℝ) (p : ℕ), 0 < A ∧
      IsEquivalent (𝓝[>] (0 : ℝ)) (fun x => profGamma α x)
        (fun x => A * x ^ α * Real.log (1 / x) ^ p) ∧
      ∀ᶠ n in atTop, 0 < icvIdx β α (N n) (B n) ∧
        A * gammaOf (N n) (B n) * (icvIdx β α (N n) (B n) / (N n : ℝ)) ^ α *
          Real.log (gammaOf (N n) (B n)) ^ p = α ^ p / sPow β 2 := by
  have hs : 0 < sPow β 2 := by
    rw [sPow_two R.hβ0.le R.hβ1]
    exact div_pos (by linarith [R.hβ1]) (by linarith [R.hβ0])
  rcases hα1.lt_or_eq with hlt | heq
  · refine ⟨α ^ 2 / (1 - α), 2, div_pos (by have := R.hα; positivity) (by linarith), ?_, ?_⟩
    · refine (vm_profiles_gamma_lt R.hα hlt).trans_eventuallyEq ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : 0 < x := hx
      rw [Real.log_rpow hx', one_div, Real.log_inv]
      ring
    · filter_upwards [R.hγ.eventually_gt_atTop 1] with n hn
      have hNp : (0 : ℝ) < N n := by exact_mod_cast R.hNpos n
      have hBp : (0 : ℝ) < B n := by exact_mod_cast R.hBpos n
      have hγ : 1 < gammaOf (N n) (B n) := hn
      have hℓ := Real.log_pos hγ
      have hγ0 : 0 < gammaOf (N n) (B n) := by linarith
      have hq : 0 < (1 - α) / (sPow β 2 * gammaOf (N n) (B n) * Real.log (gammaOf (N n) (B n)) ^ 2) := by
        have : 0 < 1 - α := by linarith
        positivity
      have hicv := eqn_app_pl_icv R.hβ0 R.hβ1 R.hα hα1 (R.hNpos n) (R.hBpos n) hγ
      rw [if_pos hlt] at hicv
      have hκ : icvIdx β α (N n) (B n) / (N n : ℝ) =
          ((1 - α) / (sPow β 2 * gammaOf (N n) (B n) * Real.log (gammaOf (N n) (B n)) ^ 2)) ^ (1 / α) := by
        rw [hicv]; field_simp
      refine ⟨by rw [hicv]; positivity, ?_⟩
      rw [hκ, one_div, Real.rpow_inv_rpow hq.le R.hα.ne']
      have hs0 := hs.ne'
      have hℓ0 := hℓ.ne'
      have h1a : (1 - α) ≠ 0 := by intro h; linarith
      field_simp
  · subst heq
    refine ⟨4 / 9, 3, by norm_num, ?_, ?_⟩
    · refine (vm_profiles_gamma_one rfl).trans_eventuallyEq ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [Real.rpow_one]
    · filter_upwards [R.hγ.eventually_gt_atTop 1] with n hn
      have hNp : (0 : ℝ) < N n := by exact_mod_cast R.hNpos n
      have hBp : (0 : ℝ) < B n := by exact_mod_cast R.hBpos n
      have hγ : 1 < gammaOf (N n) (B n) := hn
      have hℓ := Real.log_pos hγ
      have hicv := eqn_app_pl_icv R.hβ0 R.hβ1 R.hα hα1 (R.hNpos n) (R.hBpos n) hγ
      rw [if_neg (lt_irrefl _)] at hicv
      refine ⟨by rw [hicv]; positivity, ?_⟩
      rw [hicv, Real.rpow_one, one_pow]
      have hs0 := hs.ne'
      have hℓ0 := hℓ.ne'
      generalize Real.log (gammaOf (N n) (B n)) = L at *
      unfold gammaOf
      field_simp

private lemma vm_icv_core {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1) (i : ∀ n, Fin (N n)) :
    (∀ y0 : ℝ, 0 < y0 → Tendsto (fun n => icvRow β α (B n) (i n)) atTop (𝓝 y0) →
      Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0) ∧
      Tendsto (fun n => gammaOf (N n) (B n) * profGamma α (rowFrac (i n))) atTop
        (𝓝 (y0 ^ α / sPow β 2))) ∧
    (Tendsto (fun n => icvRow β α (B n) (i n)) atTop (𝓝 0) →
      Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0) ∧
      Tendsto (fun n => gammaOf (N n) (B n) * profGamma α (rowFrac (i n))) atTop (𝓝 0)) ∧
    (Tendsto (fun n => icvRow β α (B n) (i n)) atTop atTop →
      Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0) →
      Tendsto (fun n => gammaOf (N n) (B n) * profGamma α (rowFrac (i n))) atTop atTop) := by
  obtain ⟨A, p, hA, hprof, hev⟩ := vm_icv_data R hα1
  have hs : 0 < sPow β 2 := by
    rw [sPow_two R.hβ0.le R.hβ1]
    exact div_pos (by linarith [R.hβ1]) (by linarith [R.hβ0])
  have hγ : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop := R.hγ
  have hℓ : Tendsto (fun n => Real.log (gammaOf (N n) (B n))) atTop atTop :=
    Real.tendsto_log_atTop.comp hγ
  have hγ1 : ∀ᶠ n in atTop, 1 < gammaOf (N n) (B n) := hγ.eventually_gt_atTop 1
  have hℓ1 : ∀ᶠ n in atTop, 1 ≤ Real.log (gammaOf (N n) (B n)) := hℓ.eventually_ge_atTop 1
  -- κ → 0
  have hκ0 : Tendsto (fun n => icvIdx β α (N n) (B n) / (N n : ℝ)) atTop (𝓝 0) := by
    have hden : Tendsto (fun n => sPow β 2 * A * gammaOf (N n) (B n)) atTop atTop :=
      hγ.const_mul_atTop (mul_pos hs hA)
    have hbd : Tendsto (fun n => α ^ p / (sPow β 2 * A * gammaOf (N n) (B n))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    have hα0 : Tendsto (fun n => (icvIdx β α (N n) (B n) / (N n : ℝ)) ^ α) atTop (𝓝 0) := by
      refine squeeze_zero' ?_ ?_ hbd
      · filter_upwards [hev] with n hn
        exact Real.rpow_nonneg (div_nonneg hn.1.le (by exact_mod_cast (R.hNpos n).le)) _
      · filter_upwards [hev, hγ1, hℓ1] with n hn h1 h2
        have hγ0 : 0 < gammaOf (N n) (B n) := by linarith
        have hk0 : 0 ≤ (icvIdx β α (N n) (B n) / (N n : ℝ)) ^ α :=
          Real.rpow_nonneg (div_nonneg hn.1.le (by exact_mod_cast (R.hNpos n).le)) _
        have hpow : 1 ≤ Real.log (gammaOf (N n) (B n)) ^ p := one_le_pow₀ h2
        rw [le_div_iff₀ (by have := mul_pos hs hA; positivity)]
        have h3 := hn.2
        have h4 : (icvIdx β α (N n) (B n) / (N n : ℝ)) ^ α * (A * gammaOf (N n) (B n)) ≤
            (icvIdx β α (N n) (B n) / (N n : ℝ)) ^ α *
              (A * gammaOf (N n) (B n) * Real.log (gammaOf (N n) (B n)) ^ p) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity) hpow) hk0
        have h5 : (icvIdx β α (N n) (B n) / (N n : ℝ)) ^ α *
              (A * gammaOf (N n) (B n) * Real.log (gammaOf (N n) (B n)) ^ p) = α ^ p / sPow β 2 := by
          rw [← h3]; ring
        have h6 : (icvIdx β α (N n) (B n) / (N n : ℝ)) ^ α * (sPow β 2 * A * gammaOf (N n) (B n)) =
            sPow β 2 * ((icvIdx β α (N n) (B n) / (N n : ℝ)) ^ α * (A * gammaOf (N n) (B n))) := by ring
        rw [h6]
        calc _ ≤ sPow β 2 * (α ^ p / sPow β 2) := mul_le_mul_of_nonneg_left (h4.trans h5.le) hs.le
          _ = α ^ p := by field_simp
    have h2 := (Real.continuousAt_rpow_const 0 α⁻¹ (Or.inr (inv_pos.2 R.hα).le)).tendsto.comp hα0
    rw [Real.zero_rpow (inv_pos.2 R.hα).ne'] at h2
    refine h2.congr' ?_
    filter_upwards [hev] with n hn
    exact Real.rpow_rpow_inv (div_nonneg hn.1.le (by exact_mod_cast (R.hNpos n).le)) R.hα.ne'
  -- the exact row relations
  have hyk : ∀ᶠ n in atTop, 0 < icvRow β α (B n) (i n) ∧
      rowFrac (i n) = icvRow β α (B n) (i n) * (icvIdx β α (N n) (B n) / (N n : ℝ)) := by
    filter_upwards [hev] with n hn
    have hNp : (0 : ℝ) < N n := by exact_mod_cast R.hNpos n
    have hr : 0 < rowIdx (i n) := by unfold rowIdx; positivity
    refine ⟨div_pos hr hn.1, ?_⟩
    unfold icvRow rowFrac
    field_simp [hn.1.ne']
  -- the key equivalence and exact form
  have key : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0) →
      IsEquivalent atTop
        (fun n => sPow β 2 * (gammaOf (N n) (B n) * profGamma α (rowFrac (i n))))
        (fun n => sPow β 2 * (gammaOf (N n) (B n) *
          (A * rowFrac (i n) ^ α * Real.log (1 / rowFrac (i n)) ^ p))) := by
    intro hx
    exact (IsEquivalent.refl (u := fun _ : ℕ => sPow β 2)).mul
      ((IsEquivalent.refl (u := fun n => gammaOf (N n) (B n))).mul
        (hprof.comp_tendsto (vm_pull (fun n => (vm_rowFrac_bounds (i n)).1) hx)))
  let Rr : ℕ → ℝ := fun n => α * Real.log (1 / rowFrac (i n)) / Real.log (gammaOf (N n) (B n))
  have hexact : ∀ᶠ n in atTop,
      sPow β 2 * (gammaOf (N n) (B n) * (A * rowFrac (i n) ^ α * Real.log (1 / rowFrac (i n)) ^ p))
        = icvRow β α (B n) (i n) ^ α * Rr n ^ p ∧
      Rr n * Real.log (gammaOf (N n) (B n)) = Real.log (gammaOf (N n) (B n)) +
        p * Real.log (Real.log (gammaOf (N n) (B n))) + Real.log (A * sPow β 2 / α ^ p) -
          α * Real.log (icvRow β α (B n) (i n)) := by
    filter_upwards [hev, hyk, hγ1, hℓ1] with n h1 h2 h3 h4
    have hγ0 : 0 < gammaOf (N n) (B n) := by linarith
    have hℓ0 : 0 < Real.log (gammaOf (N n) (B n)) := by linarith
    have hNp : (0 : ℝ) < N n := by exact_mod_cast R.hNpos n
    have hκ : 0 < icvIdx β α (N n) (B n) / (N n : ℝ) := div_pos h1.1 hNp
    obtain ⟨e1, e2⟩ := vm_core_alg R.hα hs hA hγ0 hℓ0 hκ h2.1 h2.2 rfl h1.2
    refine ⟨?_, ?_⟩
    · rw [← e1]; ring
    · show α * Real.log (1 / rowFrac (i n)) / Real.log (gammaOf (N n) (B n)) *
        Real.log (gammaOf (N n) (B n)) = _
      rw [div_mul_cancel₀ _ hℓ0.ne', e2]
  have hR0 : ∀ᶠ n in atTop, 0 ≤ Rr n := by
    filter_upwards [hℓ1] with n h
    have hx := vm_rowFrac_bounds (i n)
    have : 0 ≤ Real.log (1 / rowFrac (i n)) := Real.log_nonneg (by
      rw [le_div_iff₀ hx.1]; linarith [hx.2])
    have := R.hα
    positivity
  have hxy : ∀ {L : ℝ}, Tendsto (fun n => icvRow β α (B n) (i n)) atTop (𝓝 L) →
      Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0) := by
    intro L hL
    have := hL.mul hκ0
    rw [mul_zero] at this
    exact this.congr' (hyk.mono fun n hn => hn.2.symm)
  refine ⟨?_, ?_, ?_⟩
  · intro y0 hy0 hy
    have hx := hxy hy
    refine ⟨hx, ?_⟩
    have hM := vm_R_mid (c := Real.log (A * sPow β 2 / α ^ p)) (α := α) (p := p) hℓ hy0 hy
      (hexact.mono fun n hn => hn.2)
    have h1 : Tendsto (fun n => sPow β 2 * (gammaOf (N n) (B n) *
        (A * rowFrac (i n) ^ α * Real.log (1 / rowFrac (i n)) ^ p))) atTop (𝓝 (y0 ^ α)) :=
      hM.congr' (hexact.mono fun n hn => hn.1.symm)
    have h2 := ((key hx).symm.tendsto_nhds h1).div_const (sPow β 2)
    refine h2.congr (fun n => ?_)
    field_simp
  · intro hy
    have hy' : Tendsto (fun n => icvRow β α (B n) (i n)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hy, hyk.mono fun n hn => hn.1⟩
    have hx := hxy hy
    refine ⟨hx, ?_⟩
    have hM := vm_R_small (c := Real.log (A * sPow β 2 / α ^ p)) R.hα hℓ hy'
      (hexact.mono fun n hn => hn.2) hR0
    have h1 : Tendsto (fun n => sPow β 2 * (gammaOf (N n) (B n) *
        (A * rowFrac (i n) ^ α * Real.log (1 / rowFrac (i n)) ^ p))) atTop (𝓝 0) :=
      hM.congr' (hexact.mono fun n hn => hn.1.symm)
    have h2 := ((key hx).symm.tendsto_nhds h1).div_const (sPow β 2)
    rw [zero_div] at h2
    refine h2.congr (fun n => ?_)
    field_simp
  · intro hy hx
    have hlow : ∀ᶠ n in atTop, α / Real.log (gammaOf (N n) (B n)) ≤ Rr n := by
      filter_upwards [hℓ1, hx.eventually (eventually_lt_nhds (show (0:ℝ) < Real.exp (-1) by positivity))]
        with n h1 h2
      have hx0 := (vm_rowFrac_bounds (i n)).1
      have : 1 ≤ Real.log (1 / rowFrac (i n)) := by
        rw [one_div, Real.log_inv]
        have := Real.log_lt_log hx0 h2
        rw [Real.log_exp] at this
        linarith
      have hℓ0 : 0 < Real.log (gammaOf (N n) (B n)) := by linarith
      show α / _ ≤ α * _ / _
      exact div_le_div_of_nonneg_right (by nlinarith [R.hα]) hℓ0.le
    have hM := vm_R_big (c := Real.log (A * sPow β 2 / α ^ p)) R.hα hℓ hy
      (hexact.mono fun n hn => hn.2) hlow
    have h1 : Tendsto (fun n => sPow β 2 * (gammaOf (N n) (B n) *
        (A * rowFrac (i n) ^ α * Real.log (1 / rowFrac (i n)) ^ p))) atTop atTop :=
      hM.congr' (hexact.mono fun n hn => hn.1.symm)
    have h2 := ((key hx).symm.tendsto_atTop h1).atTop_div_const hs
    refine h2.congr (fun n => ?_)
    field_simp

private lemma vm_equiv_of_subseq {v w : ℕ → ℝ} (hw : ∀ n, w n ≠ 0)
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      IsEquivalent atTop (v ∘ φ ∘ ψ) (w ∘ φ ∘ ψ)) : IsEquivalent atTop v w := by
  rw [isEquivalent_iff_tendsto_one (Eventually.of_forall hw)]
  have h0 : Tendsto (fun n => v n / w n - 1) atTop (𝓝 0) := by
    apply vm_tendsto_zero_of_subseq
    intro φ hφ
    obtain ⟨ψ, hψ, he⟩ := h φ hφ
    refine ⟨ψ, hψ, ?_⟩
    have h1 := (isEquivalent_iff_tendsto_one
      (Eventually.of_forall fun k => hw (φ (ψ k)))).1 he
    have h2 := h1.sub_const 1
    simpa [Function.comp_def] using h2
  have h3 := h0.add_const 1
  simpa [Pi.div_def] using h3

private lemma vm_vhat_equiv_A {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (i : ∀ n, Fin (N n))
    (hAtop : Tendsto (fun n => gammaOf (N n) (B n) * profGamma α (rowFrac (i n))) atTop atTop) :
    IsEquivalent atTop (fun n => vhatApprox β α (B n) (i n))
      (fun n => gammaOf (N n) (B n) * profGamma α (rowFrac (i n))) := by
  let A : ℕ → ℝ := fun n => gammaOf (N n) (B n) * profGamma α (rowFrac (i n))
  have hApos : ∀ n, 0 < A n := by
    intro n
    exact mul_pos (by
      unfold gammaOf
      exact div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n))
      (lem_app_pl_Gamma_helper_pos R.hα _ (vm_rowFrac_bounds (i n)))
  have hInvA : Tendsto (fun n => 1 / A n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hAtop
  have hInvSqrtA : Tendsto (fun n => 1 / Real.sqrt (A n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hAtop)
  have hvhatRatio : Tendsto (fun n => vhatApprox β α (B n) (i n) / A n)
      atTop (𝓝 1) := by
    have h1 := hInvA.const_mul (1 / sPow β 2)
    have h2 := hInvSqrtA.const_mul (2 * c0 / Real.sqrt (sPow β 2))
    simp only [mul_zero] at h1 h2
    have h := (h1.add h2).add_const 1
    simp only [zero_add] at h
    refine h.congr' (Eventually.of_forall fun n => ?_)
    have hAn := hApos n
    have hsquare := Real.sq_sqrt hAn.le
    change 1 / sPow β 2 * (1 / A n) +
        2 * c0 / Real.sqrt (sPow β 2) * (1 / Real.sqrt (A n)) + 1 =
      (1 / sPow β 2 + 2 * c0 / Real.sqrt (sPow β 2) * Real.sqrt (A n) + A n) / A n
    have hinv : 1 / Real.sqrt (A n) = Real.sqrt (A n) / A n := by
      have hsqrt : Real.sqrt (A n) ≠ 0 := (Real.sqrt_pos.2 hAn).ne'
      field_simp [hsqrt, hAn.ne']
      nlinarith
    rw [hinv]
    field_simp [hAn.ne']
  exact (isEquivalent_iff_tendsto_one (Eventually.of_forall fun n => (hApos n).ne')).2 hvhatRatio

private lemma vm_vhat_tendsto {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (i : ∀ n, Fin (N n)) {G0 : ℝ}
    (hG0 : 0 ≤ G0)
    (hG : Tendsto (fun n => gammaOf (N n) (B n) * profGamma α (rowFrac (i n))) atTop (𝓝 G0)) :
    Tendsto (fun n => vhatApprox β α (B n) (i n)) atTop
      (𝓝 (1 / sPow β 2 + 2 * c0 / Real.sqrt (sPow β 2) * Real.sqrt G0 + G0)) := by
  have h1 := ((Real.continuous_sqrt.tendsto G0).comp hG).const_mul (2 * c0 / Real.sqrt (sPow β 2))
  exact ((tendsto_const_nhds (x := 1 / sPow β 2)).add h1).add hG

private lemma vm_seq_mid {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (hPSD : volHPSD α β N B c) (hZero : volHZero α β N B c)
    (i : ∀ n, Fin (N n)) (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    {y0 : ℝ} (hy0 : 0 < y0) (hy : Tendsto (fun n => icvRow β α (B n) (i n)) atTop (𝓝 y0)) :
    Tendsto (fun n => sPow β 2 * vPart β (B n) (plSpec α (c n) (N n)) (i n)) atTop
      (𝓝 (1 + 2 * c0 * y0 ^ (α / 2) + y0 ^ α)) := by
  have hs : 0 < sPow β 2 := by
    rw [sPow_two R.hβ0.le R.hβ1]
    exact div_pos (by linarith [R.hβ1]) (by linarith [R.hβ0])
  obtain ⟨hx, hG⟩ := (vm_icv_core R hα1 i).1 y0 hy0 hy
  have heq := vm_meso_equiv_vhat R hα1 hPSD hZero i hi hx
  have hvhat := vm_vhat_tendsto R i (by positivity) hG
  have hv := (heq.symm.tendsto_nhds hvhat).const_mul (sPow β 2)
  convert hv using 2
  have hsq : Real.sqrt (y0 ^ α / sPow β 2) = y0 ^ (α / 2) / Real.sqrt (sPow β 2) := by
    rw [Real.sqrt_div (Real.rpow_nonneg hy0.le _), Real.sqrt_eq_rpow, ← Real.rpow_mul hy0.le]
    congr 2; ring
  rw [hsq]
  have hss : Real.sqrt (sPow β 2) ^ 2 = sPow β 2 := Real.sq_sqrt hs.le
  have hsp : 0 < Real.sqrt (sPow β 2) := Real.sqrt_pos.2 hs
  field_simp
  rw [hss]
  ring

private lemma vm_seq_zero {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (hPSD : volHPSD α β N B c) (hZero : volHZero α β N B c)
    (i : ∀ n, Fin (N n)) (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hy : Tendsto (fun n => icvRow β α (B n) (i n)) atTop (𝓝 0)) :
    Tendsto (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n)) atTop (𝓝 (1 / sPow β 2)) := by
  obtain ⟨hx, hG⟩ := (vm_icv_core R hα1 i).2.1 hy
  have heq := vm_meso_equiv_vhat R hα1 hPSD hZero i hi hx
  have hvhat := vm_vhat_tendsto R i le_rfl hG
  rw [Real.sqrt_zero, mul_zero, add_zero, add_zero] at hvhat
  exact heq.symm.tendsto_nhds hvhat

private lemma vm_seq_inf {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (hBound : volHBound α β N B c) (hPSD : volHPSD α β N B c) (hZero : volHZero α β N B c)
    (i : ∀ n, Fin (N n)) (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hy : Tendsto (fun n => icvRow β α (B n) (i n)) atTop atTop) :
    IsEquivalent atTop
      (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => gammaOf (N n) (B n) * profGamma α (rowFrac (i n))) := by
  refine vm_equiv_of_subseq (fun n => ?_) ?_
  · exact (mul_pos (by
      unfold gammaOf
      exact div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n))
      (lem_app_pl_Gamma_helper_pos R.hα _ (vm_rowFrac_bounds (i n)))).ne'
  intro φ hφ
  have hxmem : ∀ k, rowFrac (i (φ k)) ∈ Icc (0 : ℝ) 1 := fun k =>
    ⟨(vm_rowFrac_bounds (i (φ k))).1.le, (vm_rowFrac_bounds (i (φ k))).2⟩
  obtain ⟨x, hxI, ψ, hψ, hx⟩ := isCompact_Icc.tendsto_subseq hxmem
  have hθ : StrictMono (φ ∘ ψ) := hφ.comp hψ
  have R'' : assum_app_pl_regime α β (N ∘ (φ ∘ ψ)) (B ∘ (φ ∘ ψ)) (c ∘ (φ ∘ ψ)) :=
    vm_regime_comp R hθ
  let j : ∀ k, Fin ((N ∘ (φ ∘ ψ)) k) := fun k => i (φ (ψ k))
  have hj : Tendsto (fun k => rowIdx (j k)) atTop atTop := hi.comp hθ.tendsto_atTop
  have hjy : Tendsto (fun k => icvRow β α ((B ∘ (φ ∘ ψ)) k) (j k)) atTop atTop :=
    hy.comp hθ.tendsto_atTop
  have hjx : Tendsto (fun k => rowFrac (j k)) atTop (𝓝 x) := hx
  refine ⟨ψ, hψ, ?_⟩
  have hPSD' : volHPSD α β (N ∘ (φ ∘ ψ)) (B ∘ (φ ∘ ψ)) (c ∘ (φ ∘ ψ)) :=
    fun k q I J hI hIs hJ hJs => hPSD (φ (ψ k)) q I J hI hIs hJ hJs
  have hZero' : volHZero α β (N ∘ (φ ∘ ψ)) (B ∘ (φ ∘ ψ)) (c ∘ (φ ∘ ψ)) :=
    fun k q => hZero (φ (ψ k)) q
  have hBound' : volHBound α β (N ∘ (φ ∘ ψ)) (B ∘ (φ ∘ ψ)) (c ∘ (φ ∘ ψ)) :=
    fun k q ℓ => hBound (φ (ψ k)) q ℓ
  rcases eq_or_lt_of_le hxI.1 with hx0 | hx0
  · subst x
    have hAtop := (vm_icv_core R'' hα1 j).2.2 hjy hjx
    have h1 := vm_meso_equiv_vhat R'' hα1 hPSD' hZero' j hj hjx
    have h2 := vm_vhat_equiv_A R'' j hAtop
    exact h1.trans h2
  · have h1 := vm_bulk_equiv_vhat R'' hBound' j ⟨hx0, hxI.2⟩ hjx
    have hprof : Tendsto (fun k => profGamma α (rowFrac (j k))) atTop (𝓝 (profGamma α x)) :=
      ((lem_app_pl_Gamma_helper_cont R.hα) x ⟨hx0, hxI.2⟩).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hjx, Eventually.of_forall fun k => vm_rowFrac_bounds (j k)⟩)
    have hprofPos : 0 < profGamma α x := lem_app_pl_Gamma_helper_pos R.hα x ⟨hx0, hxI.2⟩
    have hAtop : Tendsto (fun k => gammaOf ((N ∘ (φ ∘ ψ)) k) ((B ∘ (φ ∘ ψ)) k) *
        profGamma α (rowFrac (j k))) atTop atTop := R''.hγ.atTop_mul_pos hprofPos hprof
    have h2 := vm_vhat_equiv_A R'' j hAtop
    exact h1.trans h2

/-- `thm:app-pl-volatility`, part (ii) (crossover), in part-form (snapshot `cr-2026-10-23`). The statement
is the uniform form of the source's (ii) for the uniform claim, and the sequential form for the others, as
explained in the module header. LaTeX, verbatim from `sections/06-power-law/section.tex` (whole theorem; this
declaration states part (ii) only):

\begin{theorem}[Volatility crossover and bulk profile]\label{thm:app-pl-volatility}
Assume \cref{assum:app-pl-regime} and let $i=i_N$ be a row sequence.
\begin{enumerate}[label=(\roman*)]
\item (Bulk.) If $i/N\to x\in(0,1]$ and $\ell=\ell_N$ are integers with
$\ell/\gamma\to\tau\in(0,1)$, then
\[
\overline C_{i,\ell}(0)\longrightarrow C_{\alpha,x}(\tau),\qquad \frac{\mathfrak v_i(0)}{\gamma}\longrightarrow\Gamma_\alpha(x),
\]
locally uniformly in $x\in(0,1]$ and $\tau\in(0,1)$.
\item Let $0<\alpha\le1$, let $i\to\infty$, and put
\begin{equation}\label{eqn:app-pl-icv}
i_{\mathrm c,\mathfrak v}\defeq c_0^{2/\alpha}\,i_{\mathrm c,\mathfrak d}=\begin{cases}N\big[(1-\alpha)/(\sw2\gamma\log^2\gamma)\big]^{1/\alpha},&\alpha<1,\\ 9B/(4\sw2\log^3\gamma),&\alpha=1.\end{cases}
\end{equation}
If $i/i_{\mathrm c,\mathfrak v}\to y\in(0,\infty)$, then
$\sw2\,\mathfrak v_i(0)\to1+2c_0y^{\alpha/2}+y^\alpha$, uniformly for $y$ in compact subsets of
$(0,\infty)$. If $i/i_{\mathrm c,\mathfrak v}\to0$, then $\mathfrak v_i(0)\to1/\sw2$. If
$i/i_{\mathrm c,\mathfrak v}\to\infty$, then $\mathfrak v_i(0)\sim\gamma\Gamma_\alpha(i/N)$, and if moreover
$i/N\to0$,
\[
\mathfrak v_i(0)\sim\frac{\gamma(i/N)^\alpha\big[\log((N/i)^\alpha)\big]^2}{1-\alpha}\quad(\alpha<1),\qquad
\mathfrak v_i(0)\sim\frac49\,\frac iB\,\big[\log(N/i)\big]^3\quad(\alpha=1).
\]
\item Let $\alpha>1$ and $i\to\infty$. If $i/i_{\mathrm c}\to X_0\in(0,\infty)$, then
$\mathfrak v_i(0)\to G_{\alpha,\bmom}(X_0)$. If $i/i_{\mathrm c}\to0$, then $\mathfrak v_i(0)\to1/\sw2$. If
$i/i_{\mathrm c}\to\infty$, then $\mathfrak v_i(0)\sim\gamma\Gamma_\alpha(i/N)$, and if moreover $i/N\to0$,
\[
\mathfrak v_i(0)\sim\frac{4K_\alpha^2}{\alpha-1}\,\frac iB .
\]
\end{enumerate}
\end{theorem}
-/
theorem thm_app_pl_volatility_ii_part {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (hBound : volHBound α β N B c) (hPSD : volHPSD α β N B c)
    (hZero : volHZero α β N B c) :
    (∀ K : Set ℝ, K ⊆ Ioi 0 → IsCompact K → ∀ ε > 0, ∃ M : ℕ, ∀ᶠ n in atTop,
      ∀ i : Fin (N n), (M : ℝ) ≤ rowIdx i → icvRow β α (B n) i ∈ K →
        |sPow β 2 * vPart β (B n) (plSpec α (c n) (N n)) i -
          (1 + 2 * c0 * icvRow β α (B n) i ^ (α / 2) + icvRow β α (B n) i ^ α)| ≤ ε) ∧
    ∀ i : ∀ n, Fin (N n), Tendsto (fun n => rowIdx (i n)) atTop atTop →
      (Tendsto (fun n => icvRow β α (B n) (i n)) atTop (𝓝 0) →
        Tendsto (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n)) atTop (𝓝 (1 / sPow β 2))) ∧
      (Tendsto (fun n => icvRow β α (B n) (i n)) atTop atTop →
        IsEquivalent atTop
          (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n))
          (fun n => gammaOf (N n) (B n) * profGamma α (rowFrac (i n)))) ∧
      (Tendsto (fun n => icvRow β α (B n) (i n)) atTop atTop →
        Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0) → α < 1 →
        IsEquivalent atTop
          (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n))
          (fun n => gammaOf (N n) (B n) * rowFrac (i n) ^ α *
            Real.log (((N n : ℝ) / rowIdx (i n)) ^ α) ^ 2 / (1 - α))) ∧
      (Tendsto (fun n => icvRow β α (B n) (i n)) atTop atTop →
        Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0) → α = 1 →
        IsEquivalent atTop
          (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n))
          (fun n => 4 / 9 * (rowIdx (i n) / (B n : ℝ)) *
            Real.log ((N n : ℝ) / rowIdx (i n)) ^ 3)) := by
  refine ⟨?_, ?_⟩
  · intro K hK hKc ε hε
    by_contra hcon
    have hfreq : ∀ M : ℕ, ∃ᶠ n in atTop, ∃ i : Fin (N n), (M : ℝ) ≤ rowIdx i ∧
        icvRow β α (B n) i ∈ K ∧ ε < |sPow β 2 * vPart β (B n) (plSpec α (c n) (N n)) i -
          (1 + 2 * c0 * icvRow β α (B n) i ^ (α / 2) + icvRow β α (B n) i ^ α)| := by
      intro M
      have h1 := not_exists.1 hcon M
      refine (Filter.not_eventually.1 h1).mono ?_
      intro n hn
      push Not at hn
      exact hn
    obtain ⟨φ, hφ, hP⟩ := Filter.extraction_forall_of_frequently hfreq
    choose z hz1 hz2 hz3 using hP
    obtain ⟨y0, hy0K, ψ, hψ, hψy⟩ := hKc.tendsto_subseq
      (x := fun k => icvRow β α (B (φ k)) (z k)) hz2
    have hθ : StrictMono (φ ∘ ψ) := hφ.comp hψ
    have R'' : assum_app_pl_regime α β (N ∘ (φ ∘ ψ)) (B ∘ (φ ∘ ψ)) (c ∘ (φ ∘ ψ)) :=
      vm_regime_comp R hθ
    have hPSD' : volHPSD α β (N ∘ (φ ∘ ψ)) (B ∘ (φ ∘ ψ)) (c ∘ (φ ∘ ψ)) :=
      fun k q I J hI hIs hJ hJs => hPSD (φ (ψ k)) q I J hI hIs hJ hJs
    have hZero' : volHZero α β (N ∘ (φ ∘ ψ)) (B ∘ (φ ∘ ψ)) (c ∘ (φ ∘ ψ)) :=
      fun k q => hZero (φ (ψ k)) q
    let j : ∀ k, Fin ((N ∘ (φ ∘ ψ)) k) := fun k => z (ψ k)
    have hj : Tendsto (fun k => rowIdx (j k)) atTop atTop :=
      tendsto_atTop_mono' atTop (Eventually.of_forall fun k => hz1 (ψ k))
        (tendsto_natCast_atTop_atTop.comp hψ.tendsto_atTop)
    have hy0pos : 0 < y0 := hK hy0K
    have hmid := vm_seq_mid R'' hα1 hPSD' hZero' j hj hy0pos hψy
    have hf : Tendsto (fun k => 1 + 2 * c0 * icvRow β α (B (φ (ψ k))) (j k) ^ (α / 2) +
        icvRow β α (B (φ (ψ k))) (j k) ^ α) atTop
        (𝓝 (1 + 2 * c0 * y0 ^ (α / 2) + y0 ^ α)) := by
      have h1 := (Real.continuousAt_rpow_const y0 (α / 2) (Or.inl hy0pos.ne')).tendsto.comp hψy
      have h2 := (Real.continuousAt_rpow_const y0 α (Or.inl hy0pos.ne')).tendsto.comp hψy
      exact ((h1.const_mul (2 * c0)).const_add 1).add h2
    have herr := (hmid.sub hf).abs
    rw [sub_self, abs_zero] at herr
    have hev := (Metric.tendsto_nhds.1 herr ε hε)
    obtain ⟨k, hk⟩ := hev.exists
    rw [Real.dist_eq, sub_zero, abs_abs] at hk
    exact absurd (hz3 (ψ k)) (not_lt.2 hk.le)
  · intro i hi
    refine ⟨fun hy => vm_seq_zero R hα1 hPSD hZero i hi hy, fun hy => vm_seq_inf R hα1 hBound hPSD hZero i hi hy,
      fun hy hx hlt => ?_, fun hy hx heq => ?_⟩
    · exact vm_explicit_lt_of_profile R i hx hlt (vm_seq_inf R hα1 hBound hPSD hZero i hi hy)
    · exact vm_explicit_one_of_profile R i hx heq (vm_seq_inf R hα1 hBound hPSD hZero i hi hy)

/-- `triple_vol_le_one` (card §5, L-G.8; helper). The volatility half for `0 < α ≤ 1` of
`thm:app-pl-triple` (snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{theorem}[The coefficient pair]\label{thm:app-pl-triple}
Under \cref{assum:app-pl-regime}, for every sequence of integers $1\le n_N\le N$
with $n_N\to\infty$,
\begin{equation}\label{eqn:app-pl-triple}
\sup_{n_N\le i\le N}\max\Big\{\Big|\frac{\mathfrak d_i(0)}{\widehat{\mathfrak d}_i}-1\Big|,\ \Big|\frac{\mathfrak v_i(0)}{\widehat{\mathfrak v}_i}-1\Big|\Big\}\longrightarrow0 .
\end{equation}
\end{theorem}

Lean form of the supremum: for every `ε > 0`, eventually in `n`, every row `i ≥ nn n` (1-based) satisfies the bound.
The approximant is `vhatApprox`. -/
theorem triple_vol_le_one {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (hBound : volHBound α β N B c) (hPSD : volHPSD α β N B c)
    (hZero : volHZero α β N B c)
    (nn : ℕ → ℕ) (hnn : ∀ᶠ n in atTop, 1 ≤ nn n ∧ nn n ≤ N n)
    (hnnTop : Tendsto nn atTop atTop) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ i : Fin (N n), nn n ≤ (i : ℕ) + 1 →
      |vPart β (B n) (plSpec α (c n) (N n)) i / vhatApprox β α (B n) i - 1| ≤ ε := by
  intro ε hε
  apply vm_unif_of_seq (ι := fun n => Fin (N n))
    (cond := fun n i => nn n ≤ (i : ℕ) + 1)
    (F := fun n i => vPart β (B n) (plSpec α (c n) (N n)) i /
      vhatApprox β α (B n) i - 1) ?_ ε hε
  intro φ hφ z hz
  have R' := vm_regime_comp R hφ
  have hnn' : Tendsto (nn ∘ φ) atTop atTop := hnnTop.comp hφ.tendsto_atTop
  have hcast : Tendsto (fun k => ((nn (φ k) : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hnn'
  have hi : Tendsto (fun k => rowIdx (z k)) atTop atTop :=
    tendsto_atTop_mono' atTop (Eventually.of_forall fun k => by
      have hk := hz k
      change (nn (φ k) : ℝ) ≤ ((z k : ℕ) : ℝ) + 1
      exact_mod_cast hk) hcast
  apply vm_tendsto_zero_of_subseq
  intro ψ hψ
  have hxmem : ∀ k, rowFrac (z (ψ k)) ∈ Icc (0 : ℝ) 1 := fun k =>
    ⟨(vm_rowFrac_bounds (z (ψ k))).1.le, (vm_rowFrac_bounds (z (ψ k))).2⟩
  obtain ⟨x, hxI, χ, hχ, hx⟩ := isCompact_Icc.tendsto_subseq hxmem
  let θ : ℕ → ℕ := ψ ∘ χ
  have hθ : StrictMono θ := hψ.comp hχ
  let R'' : assum_app_pl_regime α β (N ∘ φ ∘ θ) (B ∘ φ ∘ θ) (c ∘ φ ∘ θ) :=
    vm_regime_comp R' hθ
  let j : ∀ k, Fin ((N ∘ φ ∘ θ) k) := fun k => z (θ k)
  have hj : Tendsto (fun k => rowIdx (j k)) atTop atTop := hi.comp hθ.tendsto_atTop
  have hjx : Tendsto (fun k => rowFrac (j k)) atTop (𝓝 x) := by
    convert hx using 1
    ext k
    rfl
  have heq : IsEquivalent atTop
      (fun k => vPart β ((B ∘ φ ∘ θ) k)
        (plSpec α ((c ∘ φ ∘ θ) k) ((N ∘ φ ∘ θ) k)) (j k))
      (fun k => vhatApprox β α ((B ∘ φ ∘ θ) k) (j k)) := by
    rcases eq_or_lt_of_le hxI.1 with hx0 | hx0
    · subst x
      exact vm_meso_equiv_vhat R'' hα1
        (fun k q I J hI hIs hJ hJs => hPSD (φ (θ k)) q I J hI hIs hJ hJs)
        (fun k q => hZero (φ (θ k)) q) j hj hjx
    · exact vm_bulk_equiv_vhat R''
        (fun k q ℓ => hBound (φ (θ k)) q ℓ) j ⟨hx0, hxI.2⟩ hjx
  have hvhatPos : ∀ k, 0 < vhatApprox β α ((B ∘ φ ∘ θ) k) (j k) := by
    intro k
    have hs : 0 < sPow β 2 := by
      rw [sPow_two R.hβ0.le R.hβ1]
      exact div_pos (by linarith [R.hβ1]) (by linarith [R.hβ0])
    have hγ : 0 < gammaOf ((N ∘ φ ∘ θ) k) ((B ∘ φ ∘ θ) k) := by
      unfold gammaOf
      exact div_pos (by exact_mod_cast R.hNpos (φ (θ k)))
        (by exact_mod_cast R.hBpos (φ (θ k)))
    have hG : 0 < profGamma α (rowFrac (j k)) :=
      lem_app_pl_Gamma_helper_pos R.hα _ (vm_rowFrac_bounds (j k))
    unfold vhatApprox
    have hfirst : 0 < 1 / sPow β 2 := one_div_pos.2 hs
    have hmid : 0 ≤ 2 * c0 / Real.sqrt (sPow β 2) *
        Real.sqrt (gammaOf ((N ∘ φ ∘ θ) k) ((B ∘ φ ∘ θ) k) *
          profGamma α (rowFrac (j k))) :=
      mul_nonneg (div_nonneg (mul_nonneg (by norm_num) vm_c0_pos.le) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
    have hlast : 0 ≤ gammaOf ((N ∘ φ ∘ θ) k) ((B ∘ φ ∘ θ) k) *
        profGamma α (rowFrac (j k)) := mul_nonneg hγ.le hG.le
    linarith
  have hratio := (isEquivalent_iff_tendsto_one
    (Eventually.of_forall fun k => (hvhatPos k).ne')).1 heq
  refine ⟨χ, hχ, ?_⟩
  have herr := (hratio.sub_const 1).abs
  convert herr using 1
  · ext k
    rfl
  · simp

end Muon.PowerLaw

end
