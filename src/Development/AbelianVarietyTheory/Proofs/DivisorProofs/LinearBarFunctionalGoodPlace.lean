module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEqStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruh
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponentsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPairStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfCartan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartzStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeilTransferW

theorem atHTens {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {v : Pl (F := F)} {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E)
    (x u : Matrix (Fin m) (Fin n) (AE F E)) (hx : At (evFin F v) x) :
    At (evFin F v) ((-1 : AE F E) * hTens (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) x u) := by
  intro r hr
  have h : ∀ i j, r • x i j = 0 := fun i j => by
    have := congrFun (congrFun (hx r hr) i) j
    simpa using this
  rw [← mul_smul_comm]
  unfold hTens
  simp only [Finset.smul_sum, ← smul_mul_assoc, h, zero_mul, Finset.sum_const_zero, mul_zero]

theorem sumLinForm {K : Type} [Field K] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (l : Matrix m n K →ₗ[K] K) (Y : Matrix m n K) :
    l Y = ∑ k, ∑ j, Y k j * l (Matrix.single k j 1) := by
  conv_lhs => rw [Y.matrix_eq_sum_single]

  simp only [map_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single k j (Y k j) = Y k j • Matrix.single k j (1 : K) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]

theorem sumMulRight {K : Type} [CommRing K] {m n : Type} [Fintype m] [Fintype n]
    (g : Matrix n n K) (Y L : Matrix m n K) :
    ∑ k, ∑ j, (Y * g) k j * L k j = ∑ k, ∑ j, Y k j * (L * gᵀ) k j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem linBar_right_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (h : UA σ G.W.J) (g : GL (Fin (a + a')) (Fv F v)), h ∈ UAt σ G.W (evFin F v) →
    (mat h).map (piW t) = g.val →
    (mat h).map (piW (t.comp σ)) = (G.W.J.map t)⁻¹ * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val)ᵀ * G.W.J.map t →
    ∀ S : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) → (Fin a' × Fin (a + a') → Fv F v) → ℂ,
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S φ ∈ SB (Fin a' × Fin (a + a') → Fv F v)) →
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ c : ℂ,
        S (c • φ + φ') = c • S φ + S φ') →
      (∀ γ : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) γ → ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) =
          schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((1 : UA σ G.V'.J), h) γ)) (S φ)) →
      ∀ ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ),
        G.M'.IsLinBar B.ψ t 1 1 ι →
        ∃ c : ℂ, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ι (S φ) = c • fun Y => ι φ (Y * g.val) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v t h g hh ht hts S hSB hlin hcov ι hι
  have hcm : IsCMExt F E σ := hT.base.cm
  have hstd := hT.base.std
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  set A := G.V'.J.map t with hAdef
  set Bm := G.W.J.map t with hBdef
  have hA : IsUnit A.det := GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.V'.J t (B.emb w).1 1 one_ne_zero (G.V'.θ w)
    (by rw [one_smul]; exact hT.geo.hV'.cartan w)
  have hBm : IsUnit Bm.det := GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.W.J t (B.emb w).1 Complex.I Complex.I_ne_zero
    (G.W.θ w) (hT.geo.hW.cartan w)
  have hB : IsUnit Bmᵀ.det := by rw [Matrix.det_transpose]; exact hBm
  choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin a') (Fin (a + a')) (Fv F v)) =>
    GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm v t P₀ P₁
  let Pm : Matrix (Fin a') (Fin (a + a')) (Fv F v) → Matrix (Fin a') (Fin (a + a')) (Fv F v) :=
    fun C => -(A⁻¹ * C * (Bmᵀ)⁻¹)
  let Lm : (Matrix (Fin a') (Fin (a + a')) (Fv F v) →ₗ[Fv F v] Fv F v) →
      Matrix (Fin a') (Fin (a + a')) (Fv F v) := fun l => Matrix.of fun k j => l (Matrix.single k j 1)
  have hcoP : ∀ C, -(A * (U 0 (Pm C)).map (piW (t.comp σ)) * Bmᵀ) = C := by
    intro C
    rw [hU1]
    simp only [Pm, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hB, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hA]
  have hsymp : ∀ x u : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) x → x.map (piW t) = 0 →
      u.map (piW (t.comp σ)) = 0 →
      B.ψ (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) x u) =
        GlobalTheory.LatVac.psiAt B.ψ v
          (-(∑ k, ∑ j, (-(A * x.map (piW (t.comp σ)) * Bmᵀ)) k j * u.map (piW t) k j)) := by
    intro x u hx hx0 hu1
    unfold symp
    rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v t _ (atHTens _ _ x u hx)]
    have hp := GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm t G.V'.J G.W.J hT.geo.hV'.herm hT.geo.hW.skew x u hx0 hu1
    dsimp only [cA, incM] at hp
    rw [map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add, hp]
    rfl

  have hL := hι
  unfold Model.IsLinBar at hL
  simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at hL
  have htr := hL.trans
  have hmu := hL.mult
  have hact : ∀ u : Matrix (Fin a') (Fin (a + a')) (AE F E), actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((1 : UA σ G.V'.J), h) u = u * (mat h)ᵀ := by
    intro u; simp [actAB, mat]
  have hat : ∀ u : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) u → At (evFin F v) (u * (mat h)ᵀ) := by
    intro u hu r hr
    rw [← Matrix.smul_mul, hu r hr, Matrix.zero_mul]
  have hmap : ∀ (u : Matrix (Fin a') (Fin (a + a')) (AE F E)) (s : E →ₐ[F] Fv F v),
      (u * (mat h)ᵀ).map (piW s) = u.map (piW s) * ((mat h).map (piW s))ᵀ := by
    intro u s; rw [Matrix.map_mul, Matrix.transpose_map]
  have hbr := fun (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)) hγ (φ : (Fin a' × Fin (a + a') → Fv F v) → ℂ) =>
    GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v γ hγ φ
  have hsb := fun (w : (Fin a' × Fin (a + a') → Fv F v) × (Fin a' × Fin (a + a') → Fv F v))
    (φ : (Fin a' × Fin (a + a') → Fv F v) → ℂ) (hφ : φ ∈ SB _) => GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v w φ hφ
  have c1 : ∀ C, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (U 0 (Pm C))) φ) = fun Y => ι φ (Y + C) := by
    intro C φ hφ
    funext Y
    rw [htr (U 0 (Pm C)) (hUat 0 (Pm C)) (hU0 0 (Pm C)) φ hφ _ (hsb _ φ hφ) (hbr _ (hUat 0 (Pm C)) φ) Y, hcoP]
  have c2 : ∀ l, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (U (-Lm l) 0)) φ) =
        fun Y => GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι φ Y := by
    intro l φ hφ
    funext Y
    have hm := hmu (U (-Lm l) 0) (hUat (-Lm l) 0) (hU1 (-Lm l) 0) φ hφ _ (hsb _ φ hφ) (hbr _ (hUat (-Lm l) 0) φ)
      (U 0 (Pm Y)) (hUat 0 (Pm Y)) (hU0 0 (Pm Y))
    rw [hcoP] at hm
    rw [hm]
    dsimp only [cA, incM]
    rw [hsymp _ _ (hUat 0 (Pm Y)) (hU0 0 (Pm Y)) (hU1 (-Lm l) 0), hcoP, hU0, sumLinForm l Y]
    congr 2
    simp [Lm, Finset.sum_neg_distrib]
  have c3 : ∀ C, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ι (S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (U 0 (Pm C))) φ)) =
        fun Y => ι (S φ) (Y + C * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val)) := by
    intro C φ hφ
    funext Y
    rw [hcov _ (hUat 0 (Pm C)) φ hφ, hact]
    have hat' := hat _ (hUat 0 (Pm C))
    rw [htr _ hat' (by rw [hmap, hU0, Matrix.zero_mul]) _ (hSB φ hφ) _ (hsb _ _ (hSB φ hφ)) (hbr _ hat' _) Y]
    refine congrArg (fun Z => ι (S φ) (Y + Z)) ?_
    rw [hmap, hts, hU1]
    show -(A * (-(A⁻¹ * C * (Bmᵀ)⁻¹) * (Bm⁻¹ * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val)ᵀ * Bm)ᵀ) * Bmᵀ) = _
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_nonsing_inv]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hB, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ hB,
      Matrix.mul_nonsing_inv_cancel_left _ _ hA]
  have c4 : ∀ l, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ι (S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (U (-Lm l) 0)) φ)) =
        fun Y => GlobalTheory.LatVac.psiAt B.ψ v (l (Y * g.val)) * ι (S φ) Y := by
    intro l φ hφ
    funext Y
    rw [hcov _ (hUat (-Lm l) 0) φ hφ, hact]
    have hat' := hat _ (hUat (-Lm l) 0)
    have h1 : (U (-Lm l) 0 * (mat h)ᵀ).map (piW (t.comp σ)) = 0 := by rw [hmap, hU1, Matrix.zero_mul]
    have hm := hmu _ hat' h1 _ (hSB φ hφ) _ (hsb _ _ (hSB φ hφ)) (hbr _ hat' _) (U 0 (Pm Y)) (hUat 0 (Pm Y)) (hU0 0 (Pm Y))
    rw [hcoP] at hm
    rw [hm]
    dsimp only [cA, incM]
    rw [hsymp _ _ (hUat 0 (Pm Y)) (hU0 0 (Pm Y)) h1, hcoP, hmap, ht, hU0, sumLinForm l]
    congr 2
    rw [show (∑ k, ∑ j, (Y * g.val) k j * l (Matrix.single k j 1)) =
      ∑ k, ∑ j, (Y * g.val) k j * Lm l k j from rfl, sumMulRight]
    simp [Matrix.neg_mul, Finset.sum_neg_distrib]
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.LinSchur.eq_smul_of_commute (SB (Fin a' × Fin (a + a') → Fv F v)) (GlobalTheory.LatVac.psiAt B.ψ v)
    (GlobalTheory.SchrSB.continuous_psiAt B.ψ hstd.1 v) (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hstd v) ι
    (fun φ Y => ι (S φ) (Y * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val))) hι.bij
    (fun x hx y hy c => by
      funext Y
      simp only [hlin x hx y hy c, map_add (f := _), map_smul, Pi.add_apply, Pi.smul_apply])
    (fun C => schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (U 0 (Pm C))))
    (fun l => schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (U (-Lm l) 0)))
    (fun C x hx => ⟨hsb _ x hx, c1 C x hx, by
      funext Y
      show ι (S _) (Y * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val)) = ι (S x) ((Y + C) * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val))
      rw [c3 C x hx, Matrix.add_mul]⟩)
    (fun l x hx => ⟨hsb _ x hx, c2 l x hx, by
      funext Y
      show ι (S _) (Y * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val)) =
        GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι (S x) (Y * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val))
      rw [c4 l x hx]
      beta_reduce
      rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]⟩)
  refine ⟨c, fun φ hφ => funext fun Y => ?_⟩
  have e := congrFun (hc φ hφ) (Y * g.val)
  simp only [Pi.smul_apply] at e
  rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at e
  rw [Pi.smul_apply]
  exact e

end GlobalTheory.WeilTransferW
