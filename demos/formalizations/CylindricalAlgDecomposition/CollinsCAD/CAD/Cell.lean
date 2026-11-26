import Mathlib

namespace CollinsCAD

/-- A connected cell in `ℝ^r` together with a sample point. -/
structure Cell (r : ℕ) where
  carrier : Set (Fin r → ℝ)
  sample : Fin r → ℝ
  sample_mem : sample ∈ carrier
  connected : IsConnected carrier

namespace Cell

variable {r : ℕ}

/-- The whole cylinder over a base cell. -/
noncomputable def whole (S : Cell r) : Cell (r + 1) where
  carrier := (fun p : (Fin r → ℝ) × ℝ => Fin.snoc p.1 p.2) ''
    (S.carrier ×ˢ Set.univ)
  sample := Fin.snoc S.sample 0
  sample_mem := ⟨(S.sample, 0), ⟨S.sample_mem, Set.mem_univ _⟩, rfl⟩
  connected := by
    apply (S.connected.prod isConnected_univ).image
    fun_prop

@[simp] theorem mem_whole {S : Cell r} {z : Fin (r + 1) → ℝ} :
    z ∈ (whole S).carrier ↔ Fin.init z ∈ S.carrier := by
  constructor
  · rintro ⟨⟨a, x⟩, ⟨ha, _⟩, rfl⟩
    simpa using ha
  · intro hz
    refine ⟨(Fin.init z, z (Fin.last r)), ⟨hz, Set.mem_univ _⟩, ?_⟩
    change Fin.snoc (Fin.init z) (z (Fin.last r)) = z
    exact Fin.snoc_init_self z

/-- The open sector below a continuous root function. -/
noncomputable def lower (S : Cell r) (f : (Fin r → ℝ) → ℝ)
    (hf : ContinuousOn f S.carrier) : Cell (r + 1) where
  carrier := (fun p : (Fin r → ℝ) × ℝ => Fin.snoc p.1 (f p.1 - p.2)) ''
    (S.carrier ×ˢ Set.Ioi 0)
  sample := Fin.snoc S.sample (f S.sample - 1)
  sample_mem := ⟨(S.sample, 1), ⟨S.sample_mem, by simp⟩, by simp⟩
  connected := by
    apply (S.connected.prod isConnected_Ioi).image
    have hf' : ContinuousOn (fun p : (Fin r → ℝ) × ℝ => f p.1)
        (S.carrier ×ˢ Set.Ioi 0) :=
      hf.comp continuousOn_fst (fun _ hp => hp.1)
    exact ContinuousOn.finSnoc (X := fun _ : Fin (r + 1) => ℝ)
      (f := fun p : (Fin r → ℝ) × ℝ => p.1)
      (g := fun p : (Fin r → ℝ) × ℝ => f p.1 - p.2)
      continuousOn_fst (hf'.sub continuousOn_snd)

@[simp] theorem mem_lower {S : Cell r} {f : (Fin r → ℝ) → ℝ}
    {hf : ContinuousOn f S.carrier} {z : Fin (r + 1) → ℝ} :
    z ∈ (lower S f hf).carrier ↔
      Fin.init z ∈ S.carrier ∧ z (Fin.last r) < f (Fin.init z) := by
  constructor
  · rintro ⟨⟨a, t⟩, ⟨ha, ht⟩, rfl⟩
    have ht0 : 0 < t := ht
    refine ⟨by simpa using ha, ?_⟩
    simp only [Fin.init_snoc, Fin.snoc_last]
    linarith
  · rintro ⟨ha, hlt⟩
    refine ⟨(Fin.init z, f (Fin.init z) - z (Fin.last r)),
      ⟨ha, sub_pos.mpr hlt⟩, ?_⟩
    change Fin.snoc (Fin.init z)
      (f (Fin.init z) - (f (Fin.init z) - z (Fin.last r))) = z
    have hval : f (Fin.init z) -
        (f (Fin.init z) - z (Fin.last r)) = z (Fin.last r) := by ring
    rw [hval, Fin.snoc_init_self]

/-- The graph graph of a continuous root function. -/
noncomputable def graph (S : Cell r) (f : (Fin r → ℝ) → ℝ)
    (hf : ContinuousOn f S.carrier) : Cell (r + 1) where
  carrier := (fun a : Fin r → ℝ => Fin.snoc a (f a)) '' S.carrier
  sample := Fin.snoc S.sample (f S.sample)
  sample_mem := ⟨S.sample, S.sample_mem, rfl⟩
  connected := S.connected.image _ (ContinuousOn.finSnoc
    (X := fun _ : Fin (r + 1) => ℝ) (f := fun a : Fin r → ℝ => a)
    (g := f) continuousOn_id hf)
@[simp] theorem mem_graph {S : Cell r} {f : (Fin r → ℝ) → ℝ}
    {hf : ContinuousOn f S.carrier} {z : Fin (r + 1) → ℝ} :
    z ∈ (graph S f hf).carrier ↔
      Fin.init z ∈ S.carrier ∧ z (Fin.last r) = f (Fin.init z) := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simp [ha]
  · rintro ⟨ha, hz⟩
    refine ⟨Fin.init z, ha, ?_⟩
    change Fin.snoc (Fin.init z) (f (Fin.init z)) = z
    rw [← hz, Fin.snoc_init_self]

/-- The open sector between two ordered continuous root functions. -/
noncomputable def bounded (S : Cell r) (f g : (Fin r → ℝ) → ℝ)
    (hf : ContinuousOn f S.carrier) (hg : ContinuousOn g S.carrier)
    (_hfg : ∀ a ∈ S.carrier, f a < g a) : Cell (r + 1) where
  carrier :=
    (fun p : (Fin r → ℝ) × ℝ =>
      Fin.snoc p.1 ((1 - p.2) * f p.1 + p.2 * g p.1)) ''
        (S.carrier ×ˢ Set.Ioo 0 1)
  sample := Fin.snoc S.sample ((f S.sample + g S.sample) / 2)
  sample_mem := by
    refine ⟨(S.sample, (1 / 2 : ℝ)), ⟨S.sample_mem, by norm_num⟩, ?_⟩
    ring
  connected := by
    apply (S.connected.prod (isConnected_Ioo (by norm_num : (0 : ℝ) < 1))).image
    have hf' : ContinuousOn (fun p : (Fin r → ℝ) × ℝ => f p.1)
        (S.carrier ×ˢ Set.Ioo 0 1) :=
      hf.comp continuousOn_fst (fun _ hp => hp.1)
    have hg' : ContinuousOn (fun p : (Fin r → ℝ) × ℝ => g p.1)
        (S.carrier ×ˢ Set.Ioo 0 1) :=
      hg.comp continuousOn_fst (fun _ hp => hp.1)
    exact ContinuousOn.finSnoc (X := fun _ : Fin (r + 1) => ℝ)
      (f := fun p : (Fin r → ℝ) × ℝ => p.1)
      (g := fun p : (Fin r → ℝ) × ℝ =>
        (1 - p.2) * f p.1 + p.2 * g p.1)
      continuousOn_fst
      (((continuousOn_const.sub continuousOn_snd).mul hf').add
        (continuousOn_snd.mul hg'))

@[simp] theorem mem_bounded {S : Cell r} {f g : (Fin r → ℝ) → ℝ}
    {hf : ContinuousOn f S.carrier} {hg : ContinuousOn g S.carrier}
    {hfg : ∀ a ∈ S.carrier, f a < g a} {z : Fin (r + 1) → ℝ} :
    z ∈ (bounded S f g hf hg hfg).carrier ↔
      Fin.init z ∈ S.carrier ∧ f (Fin.init z) < z (Fin.last r) ∧
        z (Fin.last r) < g (Fin.init z) := by
  let a := Fin.init z
  let x := z (Fin.last r)
  constructor
  · rintro ⟨⟨b, t⟩, ⟨hb, ht⟩, rfl⟩
    have ht0 : 0 < t := ht.1
    have ht1 : t < 1 := ht.2
    have hfb : f b < g b := hfg b (by simpa using hb)
    simp only [Fin.init_snoc, Fin.snoc_last]
    refine ⟨by simpa using hb, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨ha, hfx, hxg⟩
    have hfa : f a < g a := hfg a ha
    let t : ℝ := (x - f a) / (g a - f a)
    have hden : 0 < g a - f a := sub_pos.mpr hfa
    have ht0 : 0 < t := div_pos (sub_pos.mpr hfx) hden
    have ht1 : t < 1 := by
      rw [div_lt_one hden]
      linarith
    refine ⟨(a, t), ⟨ha, ⟨ht0, ht1⟩⟩, ?_⟩
    change Fin.snoc a ((1 - t) * f a + t * g a) = z
    rw [← Fin.snoc_init_self z]
    apply congrArg (Fin.snoc (Fin.init z))
    dsimp [t]
    field_simp [hden.ne']
    ring

/-- The open sector above a continuous root function. -/
noncomputable def upper (S : Cell r) (f : (Fin r → ℝ) → ℝ)
    (hf : ContinuousOn f S.carrier) : Cell (r + 1) where
  carrier := (fun p : (Fin r → ℝ) × ℝ => Fin.snoc p.1 (f p.1 + p.2)) ''
    (S.carrier ×ˢ Set.Ioi 0)
  sample := Fin.snoc S.sample (f S.sample + 1)
  sample_mem := ⟨(S.sample, 1), ⟨S.sample_mem, by simp⟩, by simp⟩
  connected := by
    apply (S.connected.prod isConnected_Ioi).image
    have hf' : ContinuousOn (fun p : (Fin r → ℝ) × ℝ => f p.1)
        (S.carrier ×ˢ Set.Ioi 0) :=
      hf.comp continuousOn_fst (fun _ hp => hp.1)
    exact ContinuousOn.finSnoc (X := fun _ : Fin (r + 1) => ℝ)
      (f := fun p : (Fin r → ℝ) × ℝ => p.1)
      (g := fun p : (Fin r → ℝ) × ℝ => f p.1 + p.2)
      continuousOn_fst (hf'.add continuousOn_snd)

@[simp] theorem mem_upper {S : Cell r} {f : (Fin r → ℝ) → ℝ}
    {hf : ContinuousOn f S.carrier} {z : Fin (r + 1) → ℝ} :
    z ∈ (upper S f hf).carrier ↔
      Fin.init z ∈ S.carrier ∧ f (Fin.init z) < z (Fin.last r) := by
  constructor
  · rintro ⟨⟨a, t⟩, ⟨ha, ht⟩, rfl⟩
    have ht0 : 0 < t := ht
    refine ⟨by simpa using ha, ?_⟩
    simp only [Fin.init_snoc, Fin.snoc_last]
    linarith
  · rintro ⟨ha, hlt⟩
    refine ⟨(Fin.init z, z (Fin.last r) - f (Fin.init z)),
      ⟨ha, sub_pos.mpr hlt⟩, ?_⟩
    change Fin.snoc (Fin.init z)
      (f (Fin.init z) + (z (Fin.last r) - f (Fin.init z))) = z
    have hval : f (Fin.init z) +
        (z (Fin.last r) - f (Fin.init z)) = z (Fin.last r) := by ring
    rw [hval, Fin.snoc_init_self]

end Cell

end CollinsCAD
