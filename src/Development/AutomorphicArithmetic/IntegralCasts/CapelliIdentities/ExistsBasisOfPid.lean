module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Dvr

@[expose] public section

namespace UpperTheory.Reformulated.B.Qi33

open scoped NumberField

theorem aux1.{u_1, u_2} {R : Type u_2} [CommRing R] {W : Type u_1} [AddCommGroup W] [Module R W]
    (S : Submonoid R) (L : Submodule R W) {x y : W} (hx : x ∈ {x : W | ∃ s ∈ S, s • x ∈ L})
    (hy : y ∈ {x : W | ∃ s ∈ S, s • x ∈ L}) : x + y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  obtain ⟨s, hs, hx⟩ := hx
  obtain ⟨t, ht, hy⟩ := hy
  refine ⟨s * t, S.mul_mem hs ht, ?_⟩
  rw [smul_add]
  refine L.add_mem ?_ ?_
  · rw [mul_comm, mul_smul]
    exact L.smul_mem t hx
  · rw [mul_smul]
    exact L.smul_mem s hy

theorem aux2.{u_1, u_2} {R : Type u_1} [CommRing R] {W : Type u_2} [AddCommGroup W] [Module R W]
    (S : Submonoid R) (L : Submodule R W) : ∃ s ∈ S, s • (0 : W) ∈ L :=
  ⟨1, S.one_mem, by simp⟩

theorem aux3.{u_1, u_2} {R : Type u_2} [CommRing R] {W : Type u_1} [AddCommGroup W] [Module R W]
    (S : Submonoid R) (L : Submodule R W) (r : R) {x : W} (hx : x ∈ {x : W | ∃ s ∈ S, s • x ∈ L}) :
    r • x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  obtain ⟨s, hs, hx⟩ := hx
  refine ⟨s, hs, ?_⟩
  rw [smul_comm]
  exact L.smul_mem r hx

noncomputable def locS.{u_1, u_4} {R : Type u_1} [CommRing R] {W : Type u_4} [AddCommGroup W]
    [Module R W] (S : Submonoid R) (L : Submodule R W) : Submodule R W :=
  { carrier := {x : W | ∃ s ∈ S, s • x ∈ L}, add_mem' := @aux1 R _ W _ _ S L,
    zero_mem' := aux2 S L, smul_mem' := aux3 S L : Submodule R W }

noncomputable def localization₂.{u_1, u_4} {R : Type u_1} [CommRing R] {W : Type u_4} [AddCommGroup W]
    [Module R W] (p : Ideal R) [p.IsPrime] (L : Submodule R W) : Submodule R W :=
  locS p.primeCompl L

private theorem mem_locS_iff {R : Type*} [CommRing R] {W : Type*} [AddCommGroup W]
    [Module R W] (S : Submonoid R) (R' : Type*) [CommRing R'] [Algebra R R'] [IsLocalization S R']
    [Module R' W] [IsScalarTower R R' W] (L : Submodule R W) (x : W) :
    x ∈ locS S L ↔ x ∈ Submodule.span R' (L : Set W) := by
  rw [IsLocalization.mem_span_iff S, Submodule.span_eq]
  constructor
  · rintro ⟨s, hs, hx⟩
    refine ⟨s • x, hx, ⟨s, hs⟩, ?_⟩
    rw [← algebraMap_smul R' s x, smul_smul]
    have h := IsLocalization.mk'_spec R' (1 : R) (⟨s, hs⟩ : S)
    simp only [map_one] at h
    rw [h, one_smul]
  · rintro ⟨y, hy, z, rfl⟩
    refine ⟨z, z.2, ?_⟩
    rw [← algebraMap_smul R' (z : R), smul_smul]
    have h := IsLocalization.mk'_spec' R' (1 : R) z
    simp only [map_one] at h
    rw [h, one_smul]
    exact hy

private theorem exists_basis_of_pid {D K Z : Type} [CommRing D] [IsDomain D]
    [IsPrincipalIdealRing D] [Field K] [Algebra D K] [IsFractionRing D K] [AddCommGroup Z]
    [Module K Z] [Module D Z] [IsScalarTower D K Z] (M : Submodule D Z) (hM : M.FG)
    (hs : Submodule.span K (M : Set Z) = ⊤) :
    ∃ b : Module.Basis (Fin (Module.finrank K Z)) K Z, Submodule.span D (Set.range b) = M := by
  have : Module.Finite D M := Module.Finite.iff_fg.mpr hM
  have : Module.IsTorsionFree D Z := Module.IsTorsionFree.trans_faithfulSMul D K Z
  have : Module.Free D M := inferInstance
  let c := Module.finBasis D M
  let v : Fin (Module.finrank D M) → Z := fun i => (c i : Z)
  have hli : LinearIndependent D v := c.linearIndependent.map' M.subtype M.ker_subtype
  have hliK : LinearIndependent K v := (LinearIndependent.iff_fractionRing D K).mp hli
  have hsp : Submodule.span D (Set.range v) = M := by
    have h1 : Set.range v = M.subtype '' Set.range c := by
      rw [← Set.range_comp]; rfl
    rw [h1, ← Submodule.map_span, c.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspK : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← Submodule.span_span_of_tower D K (Set.range v), hsp, hs]
  let b0 := Module.Basis.mk hliK hspK
  have hn : Module.finrank K Z = Module.finrank D M := by
    simpa using Module.finrank_eq_card_basis b0
  refine ⟨b0.reindex (finCongr hn.symm), ?_⟩
  rw [Module.Basis.range_reindex, Module.Basis.coe_mk, hsp]

theorem exists_loc_basis {K : Type} [Field K] [NumberField K] [StarRing K] {Z : Type} [AddCommGroup Z]
    [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (A : Submodule (𝓞 K) Z) (hA : A.FG)
    (hsp : Submodule.span K (A : Set Z) = ⊤) :
    ∃ b : Module.Basis (Fin (Module.finrank K Z)) K Z,
      localization₂ w.asIdeal A = localization₂ w.asIdeal (Submodule.span (𝓞 K) (Set.range b)) := by
  let D := Localization.subalgebra.ofField K w.asIdeal.primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors w.asIdeal)
  have hloc : IsLocalization w.asIdeal.primeCompl D :=
    Localization.subalgebra.isLocalization_ofField K _ _
  have : IsFractionRing D K := Localization.subalgebra.isFractionRing_ofField K _ _
  have : IsDiscreteValuationRing D :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (𝓞 K) w.ne_bot D
  have : IsScalarTower (𝓞 K) D Z :=
    IsScalarTower.of_algebraMap_smul fun r z => algebraMap_smul K r z
  have hfg : (Submodule.span D (A : Set Z)).FG := by
    obtain ⟨t, rfl⟩ := hA
    exact ⟨t, (Submodule.span_span_of_tower _ _ _).symm⟩
  obtain ⟨b, hb⟩ := exists_basis_of_pid (D := D) (K := K) _ hfg
    (by rw [Submodule.span_span_of_tower, hsp])
  refine ⟨b, ?_⟩
  ext x
  unfold localization₂
  rw [mem_locS_iff _ D, mem_locS_iff _ D,
    Submodule.span_span_of_tower, hb]

end UpperTheory.Reformulated.B.Qi33
