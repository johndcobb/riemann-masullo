module

public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import RiemannMasullo.Ch03_IdelicZeta.Sec2

/-!
# §B.5 Recurrence and equidistribution

Continuous-time torus equidistribution, vertical self-approximation, and recurrence of
reciprocal finite Euler products.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set
open Complex.HadamardThreeLines (verticalStrip)
open scoped ENNReal NNReal Topology

namespace RiemannMasullo

section Torus

variable {N : ℕ}

/-- Paper: Definition B.5.1.1(1), p. 626.
The product torus, represented by Mathlib's `UnitAddTorus (Fin N)`, is compact Hausdorff. -/
theorem unitAddTorus_compactHausdorff (N : ℕ) :
    CompactSpace (UnitAddTorus (Fin N)) ∧ T2Space (UnitAddTorus (Fin N)) :=
  ⟨inferInstance, inferInstance⟩

/-- Paper: Definition B.5.1.1(2), p. 626.
The torus quotient reduces each real coordinate modulo one. -/
def torusQuotient (N : ℕ) : (Fin N → ℝ) →ₜ+ UnitAddTorus (Fin N) where
  toAddMonoidHom := AddMonoidHom.pi fun i ↦
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp (Pi.evalAddMonoidHom _ i)
  continuous_toFun := continuous_pi fun i ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
    (continuous_apply i)

/-- Two real vectors have the same image in the torus precisely when their coordinate
differences are integers. -/
theorem torusQuotient_eq_iff (x y : Fin N → ℝ) :
    torusQuotient N x = torusQuotient N y ↔ ∀ i, ∃ m : ℤ, x i - y i = (m : ℝ) := by
  rw [funext_iff]
  refine forall_congr' fun i ↦ ?_
  change ((x i : ℝ) : AddCircle (1 : ℝ)) = (y i : AddCircle (1 : ℝ)) ↔ _
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
  exact exists_congr fun k ↦ by rw [zsmul_eq_mul, mul_one, eq_comm]

/-- Paper: Definition B.5.1.1(2), p. 626.
The hitting times are the times in the given interval when the projected curve belongs
to the image of the target set modulo one. -/
def torusHittingTimes (γ : ℝ → Fin N → ℝ) (J : Set ℝ) (U : Set (Fin N → ℝ)) : Set ℝ :=
  J ∩ (torusQuotient N ∘ γ) ⁻¹' (torusQuotient N '' U)

/-- The constant zero curve hits a singleton integer vector modulo one at every time. -/
theorem torusHittingTimes_zero_singleton_int (J : Set ℝ) (m : Fin N → ℤ) :
    torusHittingTimes (fun _ ↦ 0) J {fun i ↦ (m i : ℝ)} = J := by
  have h : torusQuotient N (fun i ↦ (m i : ℝ)) = torusQuotient N 0 :=
    (torusQuotient_eq_iff _ _).mpr fun i ↦ ⟨m i, sub_zero _⟩
  exact inter_eq_left.mpr fun t _ ↦ ⟨_, rfl, h⟩

/-- Paper: §B.5.1, p. 627.
The one-parameter torus subgroup of a frequency vector is the projection of its real line. -/
def torusFlow (τ : Fin N → ℝ) : ℝ →ₜ+ UnitAddTorus (Fin N) :=
  (torusQuotient N).comp (↑((ContinuousLinearMap.id ℝ ℝ).smulRight τ))

/-- At time one the flow has the phase given by the frequency vector modulo one. -/
theorem torusFlow_one (τ : Fin N → ℝ) : torusFlow τ 1 = torusQuotient N τ := by
  change torusQuotient N ((1 : ℝ) • τ) = torusQuotient N τ
  rw [one_smul]

-- TODO(paper-gap): The sentence before §B.5.2 claims injectivity also in dimension one.
-- For N = 1 and τ₁ = 1, times zero and one have the same image.

/-- Paper: §B.5.1, p. 627. Rationally independent frequencies give a dense
one-parameter subgroup of the ambient torus. -/
theorem torusFlow_denseRange_of_linearIndependent [NeZero N] {τ : Fin N → ℝ}
    (hτ : LinearIndependent ℚ τ) : DenseRange (torusFlow τ) := by sorry

/-- Paper: §B.5.1, p. 627. For at least two rationally independent frequencies,
distinct times give distinct phases.
Deviation: Adds the dimension hypothesis used in the proof on p. 628. -/
theorem torusFlow_injective_of_linearIndependent (hN : 2 ≤ N) {τ : Fin N → ℝ}
    (hτ : LinearIndependent ℚ τ) : Injective (torusFlow τ) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  have hint (i : Fin N) : ∃ m : ℤ, t * τ i = (m : ℝ) := by
    have h : torusQuotient N (t • τ) = torusQuotient N 0 := by
      rw [map_zero]
      exact ht
    obtain ⟨m, hm⟩ := (torusQuotient_eq_iff _ _).mp h i
    exact ⟨m, by simpa using hm⟩
  by_contra ht0
  let i₀ : Fin N := ⟨0, by omega⟩
  let i₁ : Fin N := ⟨1, by omega⟩
  have hne : i₀ ≠ i₁ := by
    intro h
    exact absurd (congrArg Fin.val h) (by simp [i₀, i₁])
  obtain ⟨m₀, h₀⟩ := hint i₀
  obtain ⟨m₁, h₁⟩ := hint i₁
  have hrel : (m₁ : ℚ) • τ i₀ + (-(m₀ : ℚ)) • τ i₁ = 0 := by
    have hmul : t * ((m₁ : ℝ) * τ i₀ - (m₀ : ℝ) * τ i₁) = 0 := by
      have h : t * ((m₁ : ℝ) * τ i₀ - (m₀ : ℝ) * τ i₁) =
          (m₁ : ℝ) * (t * τ i₀) - (m₀ : ℝ) * (t * τ i₁) := by ring
      rw [h, h₀, h₁]
      ring
    have hzero := (mul_eq_zero.mp hmul).resolve_left ht0
    rw [Rat.smul_def, Rat.smul_def]
    push_cast
    linarith
  have hm₁ : (m₁ : ℚ) = 0 :=
    ((LinearIndepOn.pair_iff τ hne).mp (hτ.comp _ Subtype.val_injective) _ _ hrel).1
  have hτ₁ : τ i₁ = 0 := by
    have hm₁' : (m₁ : ℝ) = 0 := by exact_mod_cast hm₁
    have h : t * τ i₁ = 0 := by rw [h₁, hm₁']
    exact (mul_eq_zero.mp h).resolve_left ht0
  exact hτ.ne_zero i₁ hτ₁

/-- Paper: Theorem B.5.2.1(1), p. 627.
The orbit closure is the closed additive subgroup obtained by closing the range of the flow. -/
def torusFlowClosure (τ : Fin N → ℝ) : AddSubgroup (UnitAddTorus (Fin N)) :=
  (torusFlow τ).toAddMonoidHom.range.topologicalClosure

/-- The zero frequency vector has the trivial orbit closure. -/
theorem torusFlowClosure_zero : torusFlowClosure (0 : Fin N → ℝ) = ⊥ := by
  have hrange : (torusFlow (0 : Fin N → ℝ)).toAddMonoidHom.range = ⊥ := by
    rw [AddMonoidHom.range_eq_bot_iff]
    refine AddMonoidHom.ext fun t ↦ ?_
    change torusQuotient N (t • (0 : Fin N → ℝ)) = 0
    rw [smul_zero, map_zero]
  refine SetLike.coe_injective ?_
  rw [torusFlowClosure, hrange, AddSubgroup.topologicalClosure_coe, AddSubgroup.coe_bot,
    closure_singleton]

/-- Paper: Theorem B.5.2.1(2), p. 627.
The torus flow takes values in its orbit closure when used in time averages. -/
def torusFlowInClosure (τ : Fin N → ℝ) (t : ℝ) : torusFlowClosure τ :=
  ⟨torusFlow τ t, AddSubgroup.le_topologicalClosure (torusFlow τ).toAddMonoidHom.range
    ⟨t, rfl⟩⟩

/-- In the ambient torus the restricted flow at time one gives the original phases. -/
theorem coe_torusFlowInClosure_one (τ : Fin N → ℝ) :
    (torusFlowInClosure τ 1 : UnitAddTorus (Fin N)) = torusQuotient N τ :=
  torusFlow_one τ

/-- Paper: §B.5.2.1, p. 627.
The fundamental domain for the torus quotient is the product of the half-open unit intervals. -/
def unitHalfOpenCube (N : ℕ) : Set (Fin N → ℝ) :=
  {x | ∀ i, x i ∈ Ico (0 : ℝ) 1}

/-- The one-dimensional cube includes the lower endpoint and excludes the upper endpoint. -/
theorem mem_unitHalfOpenCube_one (x : Fin 1 → ℝ) :
    x ∈ unitHalfOpenCube 1 ↔ 0 ≤ x 0 ∧ x 0 < 1 :=
  Fin.forall_fin_one

/-- Paper: §B.5.2.1, p. 627.
The torus volume is the pushforward of Lebesgue measure on the half-open unit cube. -/
theorem map_volume_unitHalfOpenCube (N : ℕ) :
    (volume.restrict (unitHalfOpenCube N)).map (torusQuotient N) =
      (volume : Measure (UnitAddTorus (Fin N))) := by sorry

/-- Paper: §B.5.2.1, p. 627.
Riemann integrability on a torus with Haar probability is expressed by boundedness and
continuity almost everywhere.
Deviation: Uses the Lebesgue criterion for Riemann integrability on the fundamental cube. -/
def TorusRiemannIntegrable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) (u : X → ℂ) : Prop :=
  (∃ C : ℝ, ∀ x, ‖u x‖ ≤ C) ∧ ∀ᵐ x ∂μ, ContinuousAt u x

/-- The indicator of the identity on the unit circle is Riemann integrable. -/
theorem torusRiemannIntegrable_indicator_zero :
    TorusRiemannIntegrable (volume : Measure UnitAddCircle)
      (({0} : Set UnitAddCircle).indicator (fun _ ↦ (1 : ℂ))) := by sorry

/-- Paper: Theorem B.5.2.1(1), p. 627.
The closed orbit subgroup is topologically isomorphic to the torus of dimension the rational
rank of the frequencies. -/
theorem torusFlowClosure_equiv_torus [NeZero N] (τ : Fin N → ℝ) :
    Nonempty (torusFlowClosure τ ≃ₜ+
      UnitAddTorus (Fin (Module.finrank ℚ (Submodule.span ℚ (range τ))))) := by sorry

-- TODO(paper-gap): Theorem B.5.2.1(2) for arbitrary Riemann-integrable observables.
-- A function supported on a Haar-null orbit arc can pull back to a nonmeasurable time function.
-- TODO(paper-gap): The bound in (B.5.2.14) needs an absolute value around the frequency.

/-- Paper: Theorem B.5.2.1(2), p. 627. Symmetric time averages of a
Riemann-integrable observable converge to its Haar probability integral.
Deviation: Requires Lebesgue measurability up to null sets along the orbit for the time integral. -/
theorem kroneckerWeyl_riemannIntegrable_symmetric [NeZero N] (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (u : torusFlowClosure τ → ℂ) (hu : TorusRiemannIntegrable μ u)
    (ht : AEStronglyMeasurable (fun t ↦ u (torusFlowInClosure τ t)) volume) :
    Tendsto (fun T : ℝ ↦ (2 * T)⁻¹ • ∫ t in -T..T, u (torusFlowInClosure τ t))
      atTop (𝓝 (∫ x, u x ∂μ)) := by sorry

/-- Paper: Theorem B.5.2.1(2), p. 627. Forward time averages of a
Riemann-integrable observable converge to its Haar probability integral.
Deviation: Requires Lebesgue measurability up to null sets on the forward orbit. -/
theorem kroneckerWeyl_riemannIntegrable_forward [NeZero N] (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (u : torusFlowClosure τ → ℂ) (hu : TorusRiemannIntegrable μ u)
    (ht : AEStronglyMeasurable (fun t ↦ u (torusFlowInClosure τ t))
      (volume.restrict (Ici (0 : ℝ)))) :
    Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in 0..T, u (torusFlowInClosure τ t))
      atTop (𝓝 (∫ x, u x ∂μ)) := by sorry

/-- Paper: Theorem B.5.2.1(2), p. 627.
Symmetric time averages of a continuous observable converge to its Haar probability integral.
Deviation: This is the continuous case singled out in the paper. -/
theorem kroneckerWeyl_continuous_symmetric [NeZero N] (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (u : C(torusFlowClosure τ, ℂ)) :
    Tendsto (fun T : ℝ ↦ (2 * T)⁻¹ • ∫ t in -T..T, u (torusFlowInClosure τ t))
      atTop (𝓝 (∫ x, u x ∂μ)) := by sorry

/-- Paper: Theorem B.5.2.1(2), p. 627.
Forward time averages of a continuous observable converge to its Haar probability integral.
Deviation: This is the continuous case singled out in the paper. -/
theorem kroneckerWeyl_continuous_forward [NeZero N] (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (u : C(torusFlowClosure τ, ℂ)) :
    Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in 0..T, u (torusFlowInClosure τ t))
      atTop (𝓝 (∫ x, u x ∂μ)) := by sorry

/-- Paper: Lemma B.5.2.2, p. 627.
The indicator of an open set with null boundary can be sandwiched between continuous
functions into the unit interval whose integrated difference is arbitrarily small. -/
theorem exists_continuous_sandwich_indicator {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.Regular]
    {U : Set X} (hU : IsOpen U) (hfront : μ (frontier U) = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ lower upper : C(X, Icc (0 : ℝ) 1),
      (∀ x, (lower x : ℝ) ≤ U.indicator (fun _ ↦ (1 : ℝ)) x ∧
        U.indicator (fun _ ↦ (1 : ℝ)) x ≤ (upper x : ℝ)) ∧
      (∫ x, ((upper x : ℝ) - (lower x : ℝ)) ∂μ) < ε := by
  have : IsFiniteMeasure μ := ⟨isCompact_univ.measure_lt_top⟩
  have hδ : ENNReal.ofReal (ε / 2) ≠ 0 := (ENNReal.ofReal_pos.mpr (half_pos hε)).ne'
  -- A compact set inside `U` and an open set around its closure, both of nearly the same mass.
  obtain ⟨K, hKU, hK, hKμ⟩ := hU.measurableSet.exists_isCompact_lt_add (measure_ne_top μ U) hδ
  obtain ⟨V, hV, hVo, hVμ⟩ := (closure U).exists_isOpen_lt_add (measure_ne_top μ _) hδ
  have hcl : μ (closure U) ≤ μ U := by
    rw [closure_eq_self_union_frontier]
    exact (measure_union_le _ _).trans (by rw [hfront, add_zero])
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed hU.isClosed_compl
    hK.isClosed (disjoint_compl_left_iff_subset.mpr hKU)
  obtain ⟨g, hg0, hg1, hg01⟩ := exists_continuous_zero_one_of_isClosed hVo.isClosed_compl
    isClosed_closure (disjoint_compl_left_iff_subset.mpr hV)
  refine ⟨⟨fun x ↦ ⟨f x, hf01 x⟩, f.continuous.subtype_mk _⟩,
    ⟨fun x ↦ ⟨g x, hg01 x⟩, g.continuous.subtype_mk _⟩, fun x ↦ ?_, ?_⟩
  · change f x ≤ U.indicator (fun _ ↦ (1 : ℝ)) x ∧ U.indicator (fun _ ↦ (1 : ℝ)) x ≤ g x
    by_cases hx : x ∈ U
    · have hgx : g x = 1 := hg1 (subset_closure hx)
      rw [indicator_of_mem hx, hgx]
      exact ⟨(hf01 x).2, le_rfl⟩
    · have hfx : f x = 0 := hf0 hx
      rw [indicator_of_notMem hx, hfx]
      exact ⟨le_rfl, (hg01 x).1⟩
  · change (∫ x, (g x - f x) ∂μ) < ε
    have hKV : K ⊆ V := hKU.trans (subset_closure.trans hV)
    have hmeas : MeasurableSet (V \ K) := hVo.measurableSet.diff hK.measurableSet
    have hpt (x : X) : g x - f x ≤ (V \ K).indicator (fun _ ↦ (1 : ℝ)) x := by
      by_cases hxK : x ∈ K
      · have hfx : f x = 1 := hf1 hxK
        rw [indicator_of_notMem (show x ∉ V \ K from fun h ↦ h.2 hxK), hfx]
        linarith [(hg01 x).2]
      · by_cases hxV : x ∈ V
        · rw [indicator_of_mem (show x ∈ V \ K from ⟨hxV, hxK⟩)]
          linarith [(hg01 x).2, (hf01 x).1]
        · have hgx : g x = 0 := hg0 hxV
          have hfx : f x = 0 := hf0 fun h ↦ hxV (hV (subset_closure h))
          rw [indicator_of_notMem (show x ∉ V \ K from fun h ↦ hxV h.1), hgx, hfx, sub_zero]
    have hint : Integrable (fun x ↦ g x - f x) μ :=
      (g.continuous.sub f.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hmass : μ (V \ K) < ENNReal.ofReal ε := by
      rw [measure_sdiff hKV hK.measurableSet.nullMeasurableSet (measure_ne_top μ K)]
      refine ENNReal.sub_lt_of_lt_add (measure_mono hKV) ?_
      calc μ V < μ (closure U) + ENNReal.ofReal (ε / 2) := hVμ
        _ ≤ μ K + ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
          add_le_add (hcl.trans hKμ.le) le_rfl
        _ = ENNReal.ofReal ε + μ K := by
          rw [add_assoc, ← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves,
            add_comm]
    calc ∫ x, (g x - f x) ∂μ ≤ ∫ x, (V \ K).indicator (fun _ ↦ (1 : ℝ)) x ∂μ :=
          integral_mono hint ((integrable_const 1).indicator hmeas) hpt
      _ = μ.real (V \ K) := by rw [integral_indicator_const _ hmeas, smul_eq_mul, mul_one]
      _ < ε := ENNReal.toReal_lt_of_lt_ofReal hmass

-- TODO(paper-gap): Neither inclusion in the asserted frontier identity holds in general.
-- Away from the coordinate seams the cube projection is a local homeomorphism, so the
-- torus frontier lies in the image of the relative frontier together with the null seams.

/-- Paper: Remark B.5.2.3(1), p. 628.
A subset of the half-open cube with a null relative frontier has a torus image with null
frontier. The restricted Lebesgue measure identifies relative null sets via their images
in the ambient real vector space. -/
theorem volume_frontier_torusQuotient_image [NeZero N] (U : Set (unitHalfOpenCube N))
    (hU : volume (Subtype.val '' frontier U) = 0) :
    volume (frontier (torusQuotient N '' (Subtype.val '' U))) = 0 := by sorry

/-- Paper: Remark B.5.2.3(2), p. 628.
For a Jordan-measurable subset of the cube, its torus image and the interior of that
image have the same volume. Jordan measurability is expressed by the null relative frontier. -/
theorem volume_interior_torusQuotient_image [NeZero N] (U : Set (unitHalfOpenCube N))
    (hU : volume (Subtype.val '' frontier U) = 0) :
    volume (interior (torusQuotient N '' (Subtype.val '' U))) =
      volume (torusQuotient N '' (Subtype.val '' U)) := by sorry

/-- Paper: Remark B.5.2.3(2), p. 628.
The interior of the torus image of a Jordan-measurable set has null frontier. -/
theorem volume_frontier_interior_torusQuotient_image [NeZero N] (U : Set (unitHalfOpenCube N))
    (hU : volume (Subtype.val '' frontier U) = 0) :
    volume (frontier (interior (torusQuotient N '' (Subtype.val '' U)))) = 0 := by sorry

/-- Paper: Corollary B.5.2.4, p. 631.
For a relatively open subset of the unit cube, the symmetric frequency of visits converges
to Haar probability on the orbit closure when the target has null relative frontier. -/
theorem torusHittingTimes_tendsto_symmetric [NeZero N] (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (U : Set (unitHalfOpenCube N)) (hU : IsOpen U) :
    let V : Set (torusFlowClosure τ) := Subtype.val ⁻¹' (torusQuotient N '' (Subtype.val '' U))
    μ (frontier V) = 0 →
      Tendsto (fun T : ℝ ↦
        volume.real (torusHittingTimes (fun t ↦ t • τ) (Icc (-T) T) (Subtype.val '' U)) /
          (2 * T)) atTop (𝓝 (μ.real V)) := by
  intro V hfront
  let q : (Fin N → ℝ) → UnitAddTorus (Fin N) := torusQuotient N
  have hq : Continuous q := (torusQuotient N).continuous
  have hV : MeasurableSet V := by
    have hC : MeasurableSet (unitHalfOpenCube N) :=
      MeasurableSet.univ_pi' fun _ ↦ measurableSet_Ico
    have hinj : InjOn q (unitHalfOpenCube N) := by
      intro x hx y hy hxy
      funext i
      exact AddCircle.injOn_coe_Ico (p := (1 : ℝ)) 0
        (by simpa only [zero_add] using hx i) (by simpa only [zero_add] using hy i)
        (congrFun hxy i)
    have hCU : MeasurableSet (Subtype.val '' U) :=
      (MeasurableEmbedding.subtype_coe hC).measurableSet_image.2 hU.measurableSet
    exact (hCU.image_of_measurable_injOn hq.measurable
      (hinj.mono (Subtype.coe_image_subset _ _))).preimage measurable_subtype_coe
  let F : ℝ → torusFlowClosure τ := torusFlowInClosure τ
  have hF : Continuous F := (torusFlow τ).continuous.subtype_mk _
  let u : torusFlowClosure τ → ℂ := V.indicator (fun _ ↦ 1)
  have hu : TorusRiemannIntegrable μ u := by
    refine ⟨⟨1, fun x ↦ ?_⟩, ?_⟩
    · by_cases hx : x ∈ V <;> simp [u, hx]
    · have hn : ∀ᵐ x ∂μ, x ∉ frontier V := by
        simpa only [ae_iff, not_not, setOf_mem_eq] using hfront
      filter_upwards [hn] with x hx
      exact continuousOn_const.continuousAt_indicator hx
  have hlim : Tendsto (fun T : ℝ ↦ (2 * T)⁻¹ • ∫ t in -T..T, u (F t))
      atTop (𝓝 (∫ x, u x ∂μ)) :=
    kroneckerWeyl_riemannIntegrable_symmetric τ μ u hu
      ((measurable_const.indicator hV).comp hF.measurable).aestronglyMeasurable
  have hmean : (∫ x, u x ∂μ) = (μ.real V : ℂ) := by
    change (∫ x, V.indicator (fun _ ↦ (1 : ℂ)) x ∂μ) = _
    rw [integral_indicator_const _ hV, Complex.real_smul, mul_one]
  rw [hmean] at hlim
  have hlimRe : Tendsto (fun T : ℝ ↦ ((2 * T)⁻¹ • ∫ t in -T..T, u (F t)).re)
      atTop (𝓝 (μ.real V)) := by
    simpa only [Function.comp_def, Complex.ofReal_re] using
      (Complex.continuous_re.continuousAt (x := (μ.real V : ℂ))).tendsto.comp hlim
  let W : Set ℝ := F ⁻¹' V
  have hW : MeasurableSet W := hV.preimage hF.measurable
  have hIndicator : (fun t ↦ u (F t)) = W.indicator (fun _ ↦ (1 : ℂ)) :=
    funext fun t ↦ (Set.indicator_comp_right F (s := V) (g := fun _ ↦ (1 : ℂ)) (x := t)).symm
  refine hlimRe.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  have hHits : torusHittingTimes (fun t ↦ t • τ) (Icc (-T) T) (Subtype.val '' U) =
      W ∩ Icc (-T) T := inter_comm _ _
  rw [intervalIntegral.integral_of_le ((neg_nonpos.mpr hT).trans hT), ← integral_Icc_eq_integral_Ioc,
    hIndicator, integral_indicator_const _ hW, measureReal_restrict_apply hW, ← hHits]
  rw [Complex.real_smul, Complex.real_smul, mul_one, ← Complex.ofReal_mul, Complex.ofReal_re,
    div_eq_mul_inv, mul_comm]

/-- Paper: Corollary B.5.2.4, p. 631.
For a relatively open subset of the unit cube, the forward frequency of visits converges
to Haar probability on the orbit closure when the target has null relative frontier. -/
theorem torusHittingTimes_tendsto_forward [NeZero N] (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (U : Set (unitHalfOpenCube N)) (hU : IsOpen U) :
    let V : Set (torusFlowClosure τ) := Subtype.val ⁻¹' (torusQuotient N '' (Subtype.val '' U))
    μ (frontier V) = 0 →
      Tendsto (fun T : ℝ ↦
        volume.real (torusHittingTimes (fun t ↦ t • τ) (Icc 0 T) (Subtype.val '' U)) /
          T) atTop (𝓝 (μ.real V)) := by sorry

-- TODO(paper-gap): Remark B.5.2.5 does not state the discrete versions. The discrete orbit
-- closure can be disconnected, so the continuous-time dimension claim cannot be reused verbatim.

end Torus

section Recurrence

/-- Paper: Definition B.5.3.1(1), p. 632.
The upper density is the limsup of the fraction of a symmetric interval occupied by the set.
Deviation: For arbitrary subsets the numerator is Lebesgue outer measure. -/
def upperDensity (X : Set ℝ) : ℝ :=
  limsup (fun T : ℝ ↦ volume.real (Icc (-T) T ∩ X) / (2 * T)) atTop

/-- Every right half-line has symmetric upper density one half. -/
theorem upperDensity_Ici (a : ℝ) : upperDensity (Ici a) = 1 / 2 := by
  have hev : (fun T : ℝ ↦ 1 / 2 - a / 2 * T⁻¹) =ᶠ[atTop]
      fun T ↦ volume.real (Icc (-T) T ∩ Ici a) / (2 * T) := by
    filter_upwards [eventually_ge_atTop (max |a| 1)] with T hT
    have hT0 : T ≠ 0 := (zero_lt_one.trans_le ((le_max_right _ _).trans hT)).ne'
    have haT : |a| ≤ T := (le_max_left _ _).trans hT
    have hset : Icc (-T) T ∩ Ici a = Icc a T := by
      ext x
      simp only [mem_inter_iff, mem_Icc, mem_Ici]
      exact ⟨fun h ↦ ⟨h.2, h.1.2⟩,
        fun h ↦ ⟨⟨(neg_le.mp ((neg_le_abs a).trans haT)).trans h.1, h.2⟩, h.1⟩⟩
    rw [hset, Real.volume_real_Icc_of_le ((le_abs_self a).trans haT),
      eq_div_iff (mul_ne_zero two_ne_zero hT0)]
    have h : (1 / 2 - a / 2 * T⁻¹) * (2 * T) = T - a * (T⁻¹ * T) := by ring
    rw [h, inv_mul_cancel₀ hT0, mul_one]
  have hlim : Tendsto (fun T : ℝ ↦ 1 / 2 - a / 2 * T⁻¹) atTop (𝓝 (1 / 2)) := by
    have h := (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub
      ((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (a / 2))
    rwa [mul_zero, sub_zero] at h
  exact (hlim.congr' hev).limsup_eq

/-- Paper: Definition B.5.3.1(2), p. 632.
The vertical return times are the shifts whose uniform approximation error on the specified set
is less than the tolerance. -/
def verticalReturnTimes (f : ℂ → ℂ) (K : Set ℂ) (ε : ℝ) : Set ℝ :=
  {t | (⨆ z : K, (‖f ((z : ℂ) + (t : ℂ) * Complex.I) - f z‖₊ : ℝ≥0∞)) < ENNReal.ofReal ε}

/-- The return times of the identity on a singleton are the shifts of absolute value
less than the tolerance. -/
theorem verticalReturnTimes_id_singleton (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    verticalReturnTimes id {z} ε = Ioo (-ε) ε := by
  ext t
  have : Nonempty ({z} : Set ℂ) := ⟨⟨z, rfl⟩⟩
  have hconst (w : ({z} : Set ℂ)) :
      (‖id ((w : ℂ) + (t : ℂ) * Complex.I) - id (w : ℂ)‖₊ : ℝ≥0∞) =
        (‖(t : ℂ) * Complex.I‖₊ : ℝ≥0∞) := by
    simp only [id_eq, add_sub_cancel_left]
  change (⨆ w : ({z} : Set ℂ),
    (‖id ((w : ℂ) + (t : ℂ) * Complex.I) - id (w : ℂ)‖₊ : ℝ≥0∞)) < ENNReal.ofReal ε ↔ _
  rw [iSup_congr hconst, iSup_const, ← ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_lt_ofReal_iff hε, coe_nnNorm, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_lt, mem_Ioo]

/-- Paper: Definition B.5.3.1(2), p. 632.
Strong recurrence means positive upper density of vertical return times for every positive
tolerance.
Deviation: The domain is represented by a complex function with holomorphy on the strip
and compact containment imposed at use sites. The printed `C_{>R}` is read as `C_I`. -/
def StronglyRecurrentOn (f : ℂ → ℂ) (K : Set ℂ) : Prop :=
  ∀ ε > 0, 0 < upperDensity (verticalReturnTimes f K ε)

/-- On compact sets, the complex exponential is strongly recurrent by its imaginary period. -/
theorem stronglyRecurrentOn_exp {K : Set ℂ} (hK : IsCompact K) :
    StronglyRecurrentOn Complex.exp K := by sorry

-- TODO(paper-gap): Proposition B.5.3.2 forces T₀ = 0. Over ℚ with the trivial character
-- and a finite place above 2, the denominator at T₀ vanishes.

open IsDedekindDomain NumberField

variable {F : Type*} [Field F] [NumberField F]

/-- Paper: Proposition B.5.3.3, p. 632.
The reciprocal partial Euler product multiplies the reciprocals of the finite Euler factors
from §3.2. At a zero of the local Euler polynomial this gives its holomorphic value zero. -/
def reciprocalPartialHeckeEulerProduct (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (s : ℂ) : ℂ :=
  ∏ v ∈ S, (finiteHeckeEulerFactor χ v s)⁻¹

/-- For a singleton unramified place the product is the linear factor with coefficient
given by the value of the character on a local uniformizer. -/
theorem reciprocalPartialHeckeEulerProduct_singleton
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (v : HeightOneSpectrum (𝓞 F))
    (hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v) (s : ℂ) :
    reciprocalPartialHeckeEulerProduct χ {v} s =
      1 - (ideleClassNormTwist χ 0).localValue v * (v.asIdeal.absNorm : ℂ) ^ (-s) := by
  classical
  simp [reciprocalPartialHeckeEulerProduct, finiteHeckeEulerFactor, hv]

/-- Paper: Proposition B.5.3.2, p. 632. There is a nondecreasing sequence
escaping to infinity on both tails on which the reciprocal product is bounded away from zero.
Deviation: Uses the negative sign condition for strictly negative indices. The height at
index zero may then be chosen away from all poles of the Euler factors. -/
theorem exists_heights_reciprocalPartialHeckeEulerProduct_boundedBelow
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) :
    ∃ (c : ℝ) (T : ℤ → ℝ), 0 < c ∧ Monotone T ∧
      (∀ k, 0 ≤ k → 0 ≤ T k) ∧ (∀ k, k < 0 → T k ≤ 0) ∧
      Tendsto (fun k ↦ |T k|) (comap (abs : ℤ → ℤ) atTop) atTop ∧
      ∀ k, c ≤ ‖reciprocalPartialHeckeEulerProduct χ S ((T k : ℂ) * Complex.I)‖ := by sorry

/-- Paper: Proposition B.5.3.3, p. 632.
The nonnegative vertical shifts that uniformly approximate the reciprocal partial Euler
product on the compact set have positive symmetric upper density. -/
theorem reciprocalPartialHeckeEulerProduct_upperDensity_nonneg
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    {a b : ℝ} (hI : (0 : ℝ) ∈ Ioo a b) {K : Set ℂ} (hK : IsCompact K)
    (hKI : K ⊆ verticalStrip a b) (hKint : (interior K).Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    0 < upperDensity (Ici 0 ∩ verticalReturnTimes (reciprocalPartialHeckeEulerProduct χ S) K ε) :=
  by sorry

/-- Paper: Proposition B.5.3.3, p. 632.
The nonpositive vertical shifts that uniformly approximate the reciprocal partial Euler
product on the compact set have positive symmetric upper density. -/
theorem reciprocalPartialHeckeEulerProduct_upperDensity_nonpos
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    {a b : ℝ} (hI : (0 : ℝ) ∈ Ioo a b) {K : Set ℂ} (hK : IsCompact K)
    (hKI : K ⊆ verticalStrip a b) (hKint : (interior K).Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    0 < upperDensity (Iic 0 ∩ verticalReturnTimes (reciprocalPartialHeckeEulerProduct χ S) K ε) :=
  by sorry

-- TODO(paper-gap): The proof of Proposition B.5.3.3 uses the ambient cube to infer Haar
-- nullity on a possibly lower-dimensional orbit closure. The level set must be treated
-- intrinsically on that closure. To apply the area estimate, integrate on an open
-- neighbourhood of the target compact set.

/-- Upper density is monotone in the set. -/
private theorem upperDensity_mono {X Y : Set ℝ} (h : X ⊆ Y) :
    upperDensity X ≤ upperDensity Y := by
  have hfin (T : ℝ) (Z : Set ℝ) : volume (Icc (-T) T ∩ Z) ≠ ∞ :=
    ((measure_mono inter_subset_left).trans_lt measure_Icc_lt_top).ne
  have hle (Z : Set ℝ) : ∀ᶠ T : ℝ in atTop, volume.real (Icc (-T) T ∩ Z) / (2 * T) ≤ 1 := by
    filter_upwards [eventually_gt_atTop 0] with T hT
    rw [div_le_one (by positivity)]
    refine (measureReal_mono inter_subset_left measure_Icc_lt_top.ne).trans ?_
    rw [Real.volume_real_Icc_of_le (by linarith)]
    linarith
  have hge (Z : Set ℝ) : ∀ᶠ T : ℝ in atTop, 0 ≤ volume.real (Icc (-T) T ∩ Z) / (2 * T) := by
    filter_upwards [eventually_ge_atTop 0] with T hT
    exact div_nonneg measureReal_nonneg (by positivity)
  refine limsup_le_limsup ?_ (isCoboundedUnder_le_of_eventually_le _ (hge X))
    (isBoundedUnder_of_eventually_le (hle Y))
  filter_upwards [eventually_ge_atTop 0] with T hT
  exact div_le_div_of_nonneg_right
    (measureReal_mono (inter_subset_inter_right _ h) (hfin T Y)) (by positivity)

/-- Paper: Lemma B.5.3.4(1), p. 633.
For a holomorphic function on a bounded open strip, strong recurrence on a compact subset
descends to every compact subset of that subset. -/
theorem stronglyRecurrentOn_of_subset {a b : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (verticalStrip a b)) {K K' : Set ℂ}
    (hK : IsCompact K) (hKI : K ⊆ verticalStrip a b) (hK' : IsCompact K') (hsub : K' ⊆ K)
    (hrec : StronglyRecurrentOn f K) : StronglyRecurrentOn f K' := by
  intro ε hε
  refine (hrec ε hε).trans_le (upperDensity_mono fun t ht ↦ ?_)
  exact lt_of_le_of_lt (iSup_le fun z : K' ↦ le_iSup
    (fun w : K ↦ (‖f ((w : ℂ) + (t : ℂ) * Complex.I) - f w‖₊ : ℝ≥0∞)) ⟨z.1, hsub z.2⟩) ht

-- TODO(paper-gap): Lemma B.5.3.4(2) fails. A compact vertical segment need not fit inside
-- any disc contained in the strip, and disc-by-disc recurrence need not give simultaneous return
-- times on that segment. The report gives a Runge approximation counterexample.

/-- Paper: Lemma B.5.3.5, p. 633.
If the squared area error integrated over the closure of the open set is below
`π * δ² * X²`, the uniform error on the compact set is below `X`.
Deviation: The subscript `r` in (B.5.3.6) is read as `2`, as in (B.5.3.8). -/
theorem areaApproximation_subset_verticalReturnTimes {a b : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (verticalStrip a b)) {K U : Set ℂ}
    (hK : IsCompact K) (hKne : K.Nonempty) (hKI : K ⊆ verticalStrip a b)
    (hU : IsOpen U) (hUcompact : IsCompact (closure U)) (hUI : closure U ⊆ verticalStrip a b)
    (hKU : K ⊆ U) {δ : ℝ} (hδ : δ = ⨅ z : K, Metric.infDist (z : ℂ) Uᶜ)
    (hδpos : 0 < δ) {T X : ℝ} (hT : 0 < T) (hX : 0 < X) :
    {t ∈ Icc (-T) T | (∫ z in closure U, ‖f (z + (t : ℂ) * Complex.I) - f z‖ ^ 2) <
      Real.pi * δ ^ 2 * X ^ 2} ⊆ Icc (-T) T ∩ verticalReturnTimes f K X := by sorry

end Recurrence

end RiemannMasullo
