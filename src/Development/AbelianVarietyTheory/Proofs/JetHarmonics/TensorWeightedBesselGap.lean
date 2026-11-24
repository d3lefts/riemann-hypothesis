module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrepDiscreteSeriesSum
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorRawOfFrep
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFunctionLocalityInvariantFactorFiniteSum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirrorDecomposition.HpkRowEsI
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorWeightedBesselSum, Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorWeightedBesselGap

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorWeightedBesselSum =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorWeightedBesselSum", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Jets.SideFam\npublic import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic\npublic import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrepDiscreteSeriesSum\npublic import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorRawOfFrep\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem coef_mul_split : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (om om' : ι → ℂ) (l : R.H → Wp) (l' : R.H → Wq) (lI : ∀ I, (RI I).H → Wp) (lI' : ∀ I, (RI I).H → Wq) (F : Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → IsCoef R l l' F s → ∃ (Ft : κ → Mx k r → (Wq →L[ℂ] Wp)) (st : κ → ℂ), (∀ I, IsCoef (RI I) (lI I) (lI' I) (Ft I) (st I)) ∧ (∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ om') om • F g = ∑ I, Ft I g) ∧ (∀ I, (¬ NzOn (RI I) (lI I) ∨ ¬ NzOn (RI I) (lI' I)) → st I = 0) ∧ ∀ I (κ₀ κ₁ : ℂ), (∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ • l v) → (∀ v ∈ R.sm, lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ • l' v) → st I = (ep I : ℂ) * κ₁ * star κ₀ * s := by
  intro hK k r ι κ _ _ _ _ ρ Γ d R RI io pr ep ε mu muI Wp _ _ _ _ Wq _ _ _ _ om om' l l' lI lI' F s
    hR hRI hF hT hC
  obtain ⟨m, x, y, X, hxy, hFg, hs⟩ := hC
  have hsm : ∀ v ∈ R.TK, v ∈ R.sm := (GlobalTheory.rep_basic_of_isDS hK k r ε mu R hR).2.2.2.2.1
  have hsmI : ∀ I, ∀ v ∈ (RI I).TK, v ∈ (RI I).sm := fun I =>
    (GlobalTheory.rep_basic_of_isDS hK k r ε (muI I) (RI I) (hRI I)).2.2.2.2.1
  have hadj := (GlobalTheory.TensAdj.tens_adj hK k r ι κ ρ Γ d R RI io pr ep ε mu muI hR hRI hF hT).2.2.2.2
  have hkf := (GlobalTheory.tensor_decomposition_kfinite hK k r ι κ ρ Γ d R RI io pr ε mu muI hR hRI hF hT.raw).2.2.2
  have hp : ∀ I (a : ι → ℂ), ∀ v ∈ R.TK, (∑ c, pr I c (tm R a v c)) ∈ (RI I).TK := fun I a v hv =>
    Submodule.sum_mem _ fun c _ => hkf I c _ (Submodule.smul_mem _ _ hv)
  refine ⟨fun I g => ∑ i, ⟪∑ c, pr I c (tm R om (x i) c), (RI I).σ g (∑ c, pr I c (tm R om' (y i) c))⟫_ℂ •
      ((ep I : ℂ) • X i),
    fun I => ∑ i, ⟪lI I (∑ c, pr I c (tm R om (x i) c)),
      ((ep I : ℂ) • X i) (lI' I (∑ c, pr I c (tm R om' (y i) c)))⟫_ℂ, ?_, ?_, ?_, ?_⟩
  · intro I
    exact ⟨m, fun i => ∑ c, pr I c (tm R om (x i) c), fun i => ∑ c, pr I c (tm R om' (y i) c),
      fun i => (ep I : ℂ) • X i, fun i => ⟨hp I om _ (hxy i).1, hp I om' _ (hxy i).2⟩, fun g _ => rfl, rfl⟩
  · intro g hg
    rw [hFg g hg, Finset.smul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, hadj om om' _ (hsm _ (hxy i).1) _ (hsm _ (hxy i).2) g hg, Finset.sum_smul]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [smul_smul, mul_comm]
  · intro I h
    refine Finset.sum_eq_zero fun i _ => ?_
    rcases h with h | h
    · have : lI I (∑ c, pr I c (tm R om (x i) c)) = 0 := by
        by_contra hne
        exact h ⟨_, hsmI I _ (hp I om _ (hxy i).1), hne⟩
      rw [this, inner_zero_left]
    · have : lI' I (∑ c, pr I c (tm R om' (y i) c)) = 0 := by
        by_contra hne
        exact h ⟨_, hsmI I _ (hp I om' _ (hxy i).2), hne⟩
      rw [this, map_zero, inner_zero_right]
  · intro I κ₀ κ₁ h0 h1
    rw [hs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h0 _ (hsm _ (hxy i).1), h1 _ (hsm _ (hxy i).2), map_smul, ContinuousLinearMap.smul_apply,
      inner_smul_left, inner_smul_right, inner_smul_right]
    simp only [starRingEnd_apply]
    ring

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorWeightedBesselSum =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorWeightedBesselGap =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorWeightedBesselGap", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Jets.SideFam\npublic import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt\npublic import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFunctionLocalityInvariantFactorFiniteSum\npublic import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorWeightedBesselSum\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirrorDecomposition.HpkRowEsI\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselPieri

theorem gg_mul {k r : ℕ} {a b : Mx k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) : a * b ∈ GG k r := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
  show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
  calc (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [ha', hb']

theorem one_gg (k r : ℕ) : (1 : Mx k r) ∈ GG k r := by
  show (1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
  simp

theorem one_N (k r : ℕ) : (1 : Mx k r) ∈ Formalism.QuantumDeterminants.Nset k r :=
  ⟨one_gg k r, fun _ _ _ => Matrix.one_apply, fun _ _ _ _ _ => Matrix.one_apply⟩

theorem one_UW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mx k r) ∈ Formalism.QuantumDeterminants.UWset k r z :=
  ⟨one_gg k r, fun _ => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩

theorem herm_iso {ι : Type} [Fintype ι] [DecidableEq ι] {Γ A : Matrix ι ι ℂ} (hA : Aᴴ * Γ * A = Γ) (x y : ι → ℂ) :
    Formalism.QuantumDeterminants.herm Γ (A *ᵥ x) (A *ᵥ y) = Formalism.QuantumDeterminants.herm Γ x y := by
  unfold Formalism.QuantumDeterminants.herm
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hA]

theorem coef_inv {k r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : Mx k r → Matrix ι ι ℂ} {Γ : Matrix ι ι ℂ}
    {d : ℕ} (hρ : IsFRep ρ Γ d) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {om om' : ι → ℂ}
    (h1 : ∀ g ∈ Formalism.QuantumDeterminants.Sset k r D.z, ρ g *ᵥ om = om) (h2 : ∀ g ∈ Formalism.QuantumDeterminants.Sset k r D.z', ρ g *ᵥ om' = om')
    {γ : Mx k r} (hγ : γ ∈ GG k r) (p : B.SS k r) (hp : D.inSS p) :
    Formalism.QuantumDeterminants.herm Γ (ρ (B.sgs p γ) *ᵥ om') om = Formalism.QuantumDeterminants.herm Γ (ρ γ *ᵥ om') om := by
  obtain ⟨hh, hn, hh', hn'⟩ := hp
  obtain ⟨-, -, -, hmul, hiso, -⟩ := hρ
  have hi := PI.MirrorSection₂.uw_inv hh
  have ni := PI.MirrorSection₂.n_inv hn
  have ha : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ ∈ GG k r := gg_mul hi.1 ni.1
  have e1 := h1 _ ⟨_, hi, _, ni, rfl⟩
  have e2 : ρ (Matrix.of p.2.1) *ᵥ om' = om' := h2 _ ⟨_, hh', 1, one_N k r, (Matrix.mul_one _).symm⟩
  have e3 : ρ (Matrix.of p.2.2) *ᵥ om' = om' := h2 _ ⟨1, one_UW k r _, _, hn', (Matrix.one_mul _).symm⟩
  unfold B.sgs
  rw [hmul _ (gg_mul (gg_mul ha hγ) hn'.1) _ hh'.1, hmul _ (gg_mul ha hγ) _ hn'.1, hmul _ ha _ hγ,
    ← mulVec_mulVec, e2, ← mulVec_mulVec, e3, ← mulVec_mulVec]
  conv_lhs => rw [← e1]
  exact herm_iso (hiso _ ha) _ _

end GlobalTheory.BesselPieri
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorWeightedBesselGap =====
