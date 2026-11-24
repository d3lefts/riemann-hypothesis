module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.LocIdem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ClParts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SpecIntIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.EigKill
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.KerSp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.AnnFin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.ClosedSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.HeckePolCoeffMem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.SphRed, Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.CtrlMu

-- ===== clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.SphRed =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.SphRed", "h": "module\n\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.LocIdem\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ClParts\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SpecIntIff\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.EigKill\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.KerSp\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

universe u in
private theorem sr_abs {R A K M W ι ι' : Type} [CommRing R] [CommRing A] [Algebra R A] [Field K]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    [AddCommGroup W] [Module K W] {J : Type u} (Y0 Y : Submodule A M) [Module.Free A Y0] (hle : Y ≤ Y0)
    (op : ι → Module.End A M) [hc : Fact (CommOn Y op)] (s : ι' → ι) (e : Module.End A Y0)
    (hi : IsIdempotentElem e) (hY : ∀ y : Y0, (y : M) ∈ Y ↔ e y = y) (χ : A →+* K) (sp : M → W)
    (hadd : ∀ f ∈ Y0, ∀ f' ∈ Y0, sp (f + f') = sp f + sp f') (hsmul : ∀ f ∈ Y0, ∀ b : A, sp (b • f) = χ b • sp f)
    (hind : ∀ (κ : Type) (b : Module.Basis κ A Y0), LinearIndependent K fun i => sp (b i))
    (opC : ι → Module.End K W) (hop : ∀ i, ∀ f ∈ Y0, sp (op i f) = opC i (sp f))
    (Z : J → Submodule K W) (hZ : ∀ j i, ∃ μ : K, ∀ F ∈ Z j, opC (s i) F = μ • F)
    (hOZ : ∀ f ∈ Y0, sp f ∈ ⨆ j, Z j) (I : Ideal A) (hI : I = RingHom.ker χ)
    (t : heckeAlg Y op) (ht : t ∈ Algebra.adjoin R (Set.range fun i => heckeGen Y op (s i))) (k : ℕ)
    (h : ∀ y : Y, ((t ^ k : heckeAlg Y op) : Module.End A Y) y ∈ (I • ⊤ : Submodule A Y)) (y : Y) :
    (t : Module.End A Y) y ∈ (I • ⊤ : Submodule A Y) := by
  subst hI
  have hk := UpperTheory.V.Th.AnnihilatorQuotientFinite.kerSp Y0 Y e hi hle hY χ sp hadd hsmul hind
  have key : ∃ φ : Module.End K W, (∀ f : Y, sp ((t : Module.End A Y) f : Y) = φ (sp f)) ∧
      ∀ j, ∃ μ : K, ∀ F ∈ Z j, φ F = μ • F := by
    clear h
    induction ht using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨opC (s i), fun f => hop _ _ (hle f.2), fun j => hZ j i⟩
    | algebraMap r =>
      refine ⟨algebraMap K _ (χ (algebraMap R A r)), fun f => ?_, fun j => ⟨_, fun F _ => rfl⟩⟩
      rw [IsScalarTower.algebraMap_apply R A (heckeAlg Y op)]
      exact hsmul _ (hle f.2) _
    | add a b _ _ ha hb =>
      obtain ⟨φ, h1, h2⟩ := ha
      obtain ⟨ψ, h3, h4⟩ := hb
      refine ⟨φ + ψ, fun f => ?_, fun j => ?_⟩
      · rw [LinearMap.add_apply, ← h1, ← h3]
        exact hadd _ (hle (Subtype.prop _)) _ (hle (Subtype.prop _))
      · obtain ⟨μ, hμ⟩ := h2 j
        obtain ⟨ν, hν⟩ := h4 j
        exact ⟨μ + ν, fun F hF => by rw [LinearMap.add_apply, hμ F hF, hν F hF, add_smul]⟩
    | mul a b _ _ ha hb =>
      obtain ⟨φ, h1, h2⟩ := ha
      obtain ⟨ψ, h3, h4⟩ := hb
      refine ⟨φ * ψ, fun f => ?_, fun j => ?_⟩
      · rw [Module.End.mul_apply, ← h3, ← h1]
        rfl
      · obtain ⟨μ, hμ⟩ := h2 j
        obtain ⟨ν, hν⟩ := h4 j
        exact ⟨ν * μ, fun F hF => by rw [Module.End.mul_apply, hν F hF, map_smul, hμ F hF, smul_smul]⟩
  obtain ⟨φ, h1, h2⟩ := key
  have hp : ∀ (m : ℕ) (f : Y), sp (((t ^ m : heckeAlg Y op) : Module.End A Y) f : Y) = (φ ^ m) (sp f) := by
    intro m
    induction m with
    | zero => intro f; rw [pow_zero, pow_zero]; rfl
    | succ m ih =>
      intro f
      rw [pow_succ, pow_succ, Module.End.mul_apply, ← h1, ← ih]
      rfl
  rw [← hk, h1]
  refine UpperTheory.V.Th.AnnihilatorQuotientFinite.eigKill φ k _ ?_ (by rw [← hp]; exact (hk _).2 (h y))
  refine (iSup_le fun j => ?_ : ⨆ j, Z j ≤ _) (hOZ _ (hle y.2))
  obtain ⟨μ, hμ⟩ := h2 j
  exact fun F hF => Submodule.mem_iSup_of_mem μ (Module.End.mem_eigenspace_iff.2 (hμ F hF))
attribute [local instance 2000] UpperTheory.V.W.coefLocal
attribute [-instance] GlobalTheory.AdmLoc.modFun


theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.sphRed :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.Aut ι P →
    ∀ (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n), lam ∈ H.admitted → H.Arith θ x.toRingHom lam → ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))],
    ∀ t ∈ Algebra.adjoin c.O (Set.range fun p : H.Wp × Fin n => H.gen θ a K (.inl p)), ∀ k : ℕ,
    (∀ y : H.MK θ a K, ((t ^ k : H.TK θ a K) : Module.End A (H.MK θ a K)) y ∈ (RingHom.ker x • ⊤ : Submodule A (H.MK θ a K))) → ∀ y : H.MK θ a K, (t : Module.End A (H.MK θ a K)) y ∈ (RingHom.ker x • ⊤ : Submodule A (H.MK θ a K)) := by
  intro L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι P hP x lam hlam har a K _ t ht k h y
  haveI : Finite (ResidueField c.O) := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1
  haveI : IsCNL A := IsCNL.ofCO c.O A
  obtain ⟨h0, hfin, hfree, -⟩ := hiComm L Ω l n c H hH A θ hθ K
  obtain ⟨e, -, hi, hY, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locIdem A _ _ _ (H.op A) (fun i => algebraMap c.O A (a i)) h0
  obtain ⟨d, ξ, c0, sp, hsp⟩ := spec L Ω l n c H hH A θ hθ ι x lam har
  have hO := (clParts L Ω l n c H hH A θ hθ ι P hP x lam d ξ c0 sp hsp hlam K c0 le_rfl).2
  have hOZ : ∀ f ∈ H.X.Ord (H.τA A) θ (H.lev K), sp f ∈ ⨆ Y : {Y : H.Part ι lam ξ // P lam Y.r}, Y.1.Y := fun f hf => by
    have h1 : sp f ∈ H.OrdAt θ ι x.toRingHom lam ξ K c0 := hsp.span K c0 le_rfl ▸ Submodule.subset_span ⟨f, hf, rfl⟩
    exact (hO.le.trans (iSup_mono fun _ => inf_le_left)) h1
  have hI : RingHom.ker x = RingHom.ker (ι.toRingHom.comp x.toRingHom) := by
    ext b
    simp [RingHom.mem_ker]
  exact sr_abs (R := c.O) (H.X.Ord (H.τA A) θ (H.lev K)) (H.MK θ a K) inf_le_left (H.op A) Sum.inl e hi hY
    (ι.toRingHom.comp x.toRingHom) sp (hsp.add K) (hsp.smul K) (hsp.indep K) (H.opC ι lam d) (hsp.op K)
    (fun Y : {Y : H.Part ι lam ξ // P lam Y.r} => Y.1.Y) (fun Y i => ⟨_, Y.1.sph i.1 _⟩) hOZ _ hI t ht k h y
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.SphRed =====

-- ===== clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.CtrlMu =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.CtrlMu", "h": "module\n\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.AnnFin\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.ClosedSub\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.HeckePolCoeffMem\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.SphRed\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem lam_map {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : W.GDet n A G) (f : A →+* B)
    (g : G) (i : ℕ) : (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  have h0 : (D.map f).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map f := by
    letI : Algebra A (Polynomial B) := ((algebraMap B (Polynomial B)).comp f).toAlgebra
    let φ : Polynomial A →ₐ[A] Polynomial B :=
      { Polynomial.mapRingHom f with commutes' := fun a => Polynomial.map_C f }
    have h := D.nat (Polynomial A) (Polynomial B) φ
      (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.single g 1))
    refine Eq.trans ?_ h
    change D.D (Polynomial B) _ = D.D (Polynomial B) (MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom f) _)
    congr 1
    simp [map_sub, MonoidAlgebra.mapRingHom_single]
  simp [W.GDet.lam, h0]

private theorem red_abs {O R T : Type} [CommRing O] [CommRing R] [CommRing T] [Algebra O R] [Algebra O T] (f : R →ₐ[O] T)
    (I : Ideal T) (S : Subalgebra O T) (hS : ∀ s ∈ S, ∀ k : ℕ, s ^ k ∈ I → s ∈ I) (U : Set R)
    (hU : ∀ u ∈ U, ∃ s ∈ S, f u - s ∈ I) (t : R) (ht : t ∈ Algebra.adjoin O U) (k : ℕ) (hk : f (t ^ k) ∈ I) : f t ∈ I := by
  have key : ∃ s ∈ S, f t - s ∈ I := by
    clear hk
    induction ht using Algebra.adjoin_induction with
    | mem x hx => exact hU x hx
    | algebraMap b => exact ⟨_, S.algebraMap_mem b, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, h1⟩ := hx
      obtain ⟨s', hs', h2⟩ := hy
      refine ⟨s + s', add_mem hs hs', ?_⟩
      have := I.add_mem h1 h2
      rw [map_add (f := _)]; convert this using 1; ring
    | mul x y _ _ hx hy =>
      obtain ⟨s, hs, h1⟩ := hx
      obtain ⟨s', hs', h2⟩ := hy
      refine ⟨s * s', mul_mem hs hs', ?_⟩
      have := I.add_mem (I.mul_mem_left (f x) h2) (I.mul_mem_left s' h1)
      rw [map_mul]; convert this using 1; ring
  obtain ⟨s, hs, h1⟩ := key
  have e : Ideal.Quotient.mk I (f t) = Ideal.Quotient.mk I s := Ideal.Quotient.eq.2 h1
  have h2 : s ^ k ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow, ← e, ← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact hk
  have := I.add_mem h1 (hS s hs k h2)
  simpa using this

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.ctrlMu :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.Aut ι P →
    ∀ (x : A →ₐ[c.O] c.O) (lam : Wt L l n), lam ∈ H.admitted → H.Arith θ ((Algebra.ofId c.O (Qbar l)).comp x).toRingHom lam →
    ∀ (a : H.Op → c.O) (K : H.Lev) [Module.Finite A (H.MK θ a K)] (R : Type) [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq)
      (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ) (μ : R →+* Module.End A (H.MK θ a K)),
      (H.MK θ a K = ⊥ ∨ ∃ (_ : Fact (CommOn (H.MK θ a K) (H.op A))) (_ : Alg.IsCO c.O (H.TK θ a K)) (f : R →ₐ[c.O] H.TK θ a K),
        H.IsMap θ a K D₀ ψ₀ f ∧ ∀ t, μ t = (f t : Module.End A (H.MK θ a K))) →
      ∀ t ∈ Algebra.adjoin c.O {b : R | ∃ i g, b = D₀.lam i (MonoidAlgebra.single g 1)}, ∀ k : ℕ,
        (∀ y, μ (t ^ k) y ∈ (RingHom.ker x • ⊤ : Submodule A (H.MK θ a K))) →
        ∀ y, μ t y ∈ (RingHom.ker x • ⊤ : Submodule A (H.MK θ a K)) := by
  intro L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι P hP x lam hl har a K _ R _ _ D₀ ψ₀ μ hμ t ht k hk y
  rcases hμ with h0 | ⟨_, _, f, hf, hμ⟩
  · have : μ t y = 0 := Subtype.ext ((Submodule.mem_bot A).1 (h0 ▸ (μ t y).2))
    rw [this]
    exact zero_mem _
  haveI := c.dvr
  have hker : RingHom.ker ((Algebra.ofId c.O (Qbar l)).comp x) = RingHom.ker x := by
    ext b
    rw [RingHom.mem_ker, RingHom.mem_ker]
    exact map_eq_zero_iff (algebraMap c.O (Qbar l)) Subtype.val_injective
  obtain ⟨I, hI, hfin⟩ := Th.AnnihilatorQuotientFinite.annFin x (heckeAlg (H.MK θ a K) (H.op A)).val.toRingHom fun o y => by
    rw [IsScalarTower.algebraMap_apply c.O A (H.TK θ a K)]
    rfl
  have h1 := red_abs f I (Algebra.adjoin c.O (Set.range fun p : H.Wp × Fin n => H.gen θ a K (.inl p)))
    (fun s hs k hk => (hI s).2 (by
      have := Th.AnnihilatorQuotientFinite.sphRed L Ω l n c H hH A θ hθ ι P hP _ lam hl har a K s hs k
      rw [hker] at this
      exact this ((hI _).1 hk))) _ (by
      rintro _ ⟨i, g, rfl⟩
      refine Th.AnnihilatorQuotientFinite.closedSub I _ _ fun N => ?_
      have := Th.AnnihilatorQuotientFinite.frobS L Ω l n c H hH A θ a K _ _ _ hf i g N
      rwa [lam_map] at this) t ht k ((hI _).2 fun y => by
      have := hk y
      rwa [hμ] at this)
  rw [hμ]
  exact (hI _).1 h1 y
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.CtrlMu =====
